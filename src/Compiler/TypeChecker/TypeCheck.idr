module Compiler.TypeChecker.TypeCheck

import Control.Monad.State
import Data.List
import Data.SortedMap
import Data.SortedSet

import Compiler.ScopeAndNameResolution.Data
import Compiler.TypeChecker.Phases.BodyCheck                -- phase B
import Compiler.TypeChecker.Data
import Compiler.TypeChecker.Phases.EffectsCheck             -- phase E
import Compiler.TypeChecker.Helper
import Compiler.TypeChecker.Phases.OwnershipCheck           -- phase C
import Compiler.TypeChecker.Phases.SignatureCheck           -- phase A
import Compiler.TypeChecker.PreludeSignatures
import Compiler.TypeChecker.State
import Compiler.TypeChecker.Type
import Compiler.TypeChecker.Phases.TypedAstTranslation      -- phase T
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Source
import Frontend.Syntax.AST
import Frontend.Syntax.Name

%default total

--------------------------------------------------------------------------------
-- Item Helpers
--------------------------------------------------------------------------------

itemSymbolId : ResolvedItem -> SymbolId
itemSymbolId item =
  case item.value of
    ItemFunction declaration => declaration.functionName.value.nameNodeSymbolId
    ItemConst declaration    => declaration.constName.value.nameNodeSymbolId
    ItemModule _             => notImplemented "itemSymbol" "ItemModule"
    ItemUse _                => notImplemented "itemSymbol" "ItemUse"
    ItemEnum _               => notImplemented "itemSymbol" "ItemEnum"
    ItemQEnum _              => notImplemented "itemSymbol" "ItemQEnum"
    ItemStruct _             => notImplemented "itemSymbol" "ItemStruct"
    ItemImpl _               => notImplemented "itemSymbol" "ItemImpl"

itemNameSpan : ResolvedItem -> SourceSpan
itemNameSpan item =
  case item.value of
    ItemFunction declaration => declaration.functionName.astInfo.span
    ItemConst declaration    => declaration.constName.astInfo.span
    ItemModule _             => notImplemented "itemNameSpan" "ItemModule"
    ItemUse _                => notImplemented "itemNameSpan" "ItemUse"
    ItemEnum _               => notImplemented "itemNameSpan" "ItemEnum"
    ItemQEnum _              => notImplemented "itemNameSpan" "ItemQEnum"
    ItemStruct _             => notImplemented "itemNameSpan" "ItemStruct"
    ItemImpl _               => notImplemented "itemNameSpan" "ItemImpl"

sameItem : ResolvedItem -> ResolvedItem -> Bool
sameItem a b = a.astInfo.nodeId == b.astInfo.nodeId

--------------------------------------------------------------------------------
-- Seeding
--------------------------------------------------------------------------------

sourceCodeItems : ResolvedSourceFile -> List ResolvedItem
sourceCodeItems (MkAstNode _ _ (MkSourceFileNode _ items)) = items

seedTypeTables : ScopeTables -> TypeTables
seedTypeTables scopeTables =
  MkTypeTables
    scopeTables.scopes
    scopeTables.nodeScopes
    (map (\symbol => { symbolType := TypeNotYetResolved } symbol) scopeTables.symbols)
    (map (\variable => { quantumStorage := PendingQbitClassification } variable) scopeTables.localVarsMeta)
    scopeTables.memberScopes
    scopeTables.references
    empty                                                -- constValues
    empty                                                -- expressionTypes
    empty                                                -- patternTypes
    empty                                                -- coercions
    empty                                                -- calls

seedPresetSymbolTypes : TypeTables -> TypeTables
seedPresetSymbolTypes tables = { symbols := map fixedType tables.symbols } tables
  where
    fixedType : TypedSymbolInfo -> TypedSymbolInfo
    fixedType symbol =
      case (symbol.symbolKind, symbol.origin) of
        (SymbolModule, _)               => { symbolType := NoValueType } symbol
        (SymbolFunction, PreludeSymbol) => { symbolType := preludeSymbolType symbol.declaredName } symbol
        _                               => symbol

seedTypeCheckerState : ResolvedModule -> List ResolvedItem -> TypeCheckerState
seedTypeCheckerState resolvedModule items =
  MkTypeCheckerState
    (seedPresetSymbolTypes (seedTypeTables resolvedModule.tables))
    Nothing
    emptyInferenceState
    (fromList (map (\item => (itemSymbolId item, item)) items))
    empty
    empty

--------------------------------------------------------------------------------
-- Cycles
--------------------------------------------------------------------------------

-- Every stuck item waits for a symbol another stuck item declares, so walking
-- the waits from the first stuck item must revisit a symbol; the symbols from
-- that first visit onwards are the cycle. `const A: i32 = B; const B: i32 = A;`
-- gives [B, A].
resolutionCycleTypeError : TypeTables -> List (ResolvedItem, SymbolId) -> TypeError
resolutionCycleTypeError tables stuck =
  case stuck of
    [] => unreachable {function = "resolutionCycleError"} {reason = "a round without progress has stuck items"}
    (first, firstWait) :: _ =>
      CyclicDeclaration (map symbolName (loopFrom (S (length stuck)) [] firstWait)) (itemNameSpan first)
  where
    symbolName : SymbolId -> String
    symbolName symbolId =
      case lookup symbolId tables.symbols of
        Just symbol => symbol.declaredName
        Nothing => unreachable "resolutionCycleError" "a cycle references an unknown symbol"

    waits : List (SymbolId, SymbolId)
    waits = map (\(item, waitingFor) => (itemSymbolId item, waitingFor)) stuck

    -- `visited` holds the symbols walked so far, most recent first.
    loopFrom : (fuel : Nat) -> (visited : List SymbolId) -> SymbolId -> List SymbolId
    loopFrom Z visited _ = reverse visited
    loopFrom (S fuel) visited symbol =
      if elem symbol visited
        then symbol :: reverse (takeWhile (/= symbol) visited)
        else case lookup symbol waits of
               Just next => loopFrom fuel (symbol :: visited) next
               Nothing   => reverse (symbol :: visited)

--------------------------------------------------------------------------------
-- Passes A and B, in runBodyAndSignatureCheck
--------------------------------------------------------------------------------

-- What passes A and B still have to do, each list in source order.
record WorkTodo where
  constructor MkWorkTodo
  signatures : List ResolvedItem     -- pass A has not recorded the signature yet
  bodies     : List ResolvedItem     -- pass B has not checked the body or initializer yet

noRemaining : WorkTodo -> Nat
noRemaining work = length work.signatures + length work.bodies

-- A blocked check leaves the state exactly as it was so retrying next round is safe.
attemptCheck : StateT TypeCheckerState (Either CheckFailure) () -> StateT TypeCheckerState (Either CheckFailure) (Maybe SymbolId)
attemptCheck computation = do
  stateBefore <- get
  case execStateT stateBefore computation of
    Right stateAfter       => put stateAfter >> pure Nothing
    Left (Blocked symbol)  => pure (Just symbol)
    Left failure           => lift (Left failure)

-- The items whose check blocked, each with the symbol it is waiting for.
attemptAllChecks : (ResolvedItem -> StateT TypeCheckerState (Either CheckFailure) ()) 
    -> List ResolvedItem 
    -> StateT TypeCheckerState (Either CheckFailure) (List (ResolvedItem, SymbolId))
attemptAllChecks checkFunction [] = pure []
attemptAllChecks checkFunction (item :: items) = do
  outcome <- attemptCheck (checkFunction item)
  stuck <- attemptAllChecks checkFunction items
  pure (maybe stuck (\waitingFor => (item, waitingFor) :: stuck) outcome)

-- One round: pass A on every pending signature, then pass B on every pending
-- body whose signature is recorded. Each productive round completes at least
-- one of the 2n entries, so 2n + 1 runBodyAndSignatureCheck always suffice.
runBodyAndSignatureChecks : (fuel : Nat) -> WorkTodo -> StateT TypeCheckerState (Either CheckFailure) ()
runBodyAndSignatureChecks _ (MkWorkTodo [] []) = pure ()
runBodyAndSignatureChecks Z _ = unreachable {function = "runBodyAndSignatureCheck"} {reason = "every productive round completes an entry"}
runBodyAndSignatureChecks (S fuel) work = do
  stuckSignatures <- attemptAllChecks checkSignature work.signatures
  let waitingForSignature = \item => any (sameItem item . fst) stuckSignatures
  stuckBodies <- attemptAllChecks checkBody (filter (not . waitingForSignature) work.bodies)
  let stillPending = \item => waitingForSignature item || any (sameItem item . fst) stuckBodies
      next = MkWorkTodo (map fst stuckSignatures) (filter stillPending work.bodies)
  if noRemaining next < noRemaining work
    then runBodyAndSignatureChecks fuel next
    else do
      checkerState <- get
      let typeError = resolutionCycleTypeError checkerState.tables (stuckSignatures ++ stuckBodies)
      lift (Left (Failed typeError)) 

resolveAndCheckTypes : TypeCheckerState -> List ResolvedItem -> Either TypeError TypeTables
resolveAndCheckTypes seededState items =
  case execStateT seededState (runBodyAndSignatureChecks (2 * length items + 1) (MkWorkTodo items items)) of
    Right finalState      => Right finalState.tables
    Left (Failed typeErr) => Left typeErr
    Left (Blocked _)      => unreachable {function = "resolveAndCheckTypes"} {reason = "attemptCheck catches every block"}

--------------------------------------------------------------------------------
-- The pipeline
--------------------------------------------------------------------------------

||| Passes A and B run in rounds until every signature and body is checked;
||| then the typed AST is built, and effects and ownership are checked once each.
public export
typeCheck : ResolvedModule -> Either TypeError TypedModule
typeCheck resolvedModule = do
  let items = sourceCodeItems resolvedModule.ast
  typeTables <- resolveAndCheckTypes (seedTypeCheckerState resolvedModule items) items    -- A ⇄ B
  let typedAst = translateAst typeTables resolvedModule.ast                               -- T: pure, cannot fail
  checkEffects typeTables typedAst                                                        -- E
  ownership <- checkOwnership typeTables typedAst                                         -- C
  pure (MkTypedModule resolvedModule.rootModule resolvedModule.rootScope typedAst typeTables ownership)


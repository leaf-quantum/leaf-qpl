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
import Compiler.TypeChecker.Signatures
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

sourceItems : ResolvedSourceFile -> List ResolvedItem
sourceItems (MkAstNode _ _ (MkSourceFileNode _ items)) = items

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

-- The symbols no pass computes a type for. A module — the root, which is not
-- an item, and the prelude's `<prelude>` — has no value. A prelude function
-- used as a value has the type Signatures gives it (§4.2): a gate's owned form
-- at `linear` with both capabilities, a math function's f64 form; `Param` and
-- `phase` are not values (`NoValueType`). Calls to prelude names are checked
-- from Signatures directly.
seedFixedTypes : TypeTables -> TypeTables
seedFixedTypes tables = { symbols := map fixedType tables.symbols } tables
  where
    fixedType : TypedSymbolInfo -> TypedSymbolInfo
    fixedType symbol =
      case (symbol.symbolKind, symbol.origin) of
        (SymbolModule, _)               => { symbolType := NoValueType } symbol
        (SymbolFunction, PreludeSymbol) => { symbolType := preludeValueType symbol.declaredName } symbol
        _                               => symbol

-- Resolution's tables with every type still unresolved except the prelude's,
-- and the items indexed by the symbol each declares.
seedTypeCheckerState : ResolvedModule -> List ResolvedItem -> TypeCheckerState
seedTypeCheckerState resolvedModule items =
  MkTypeCheckerState
    (seedFixedTypes (seedTypeTables resolvedModule.tables))
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
cycleError : List (ResolvedItem, SymbolId) -> TypeError
cycleError stuck =
  case stuck of
    [] => unreachable {function = "cycleError"} {reason = "a round without progress has stuck items"}
    (first, firstWait) :: _ =>
      CyclicDeclaration (loopFrom (S (length stuck)) [] firstWait) (itemNameSpan first)
  where
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

module ScopeAndNameResolution.ResolveTestHelper

import Compiler.ScopeAndNameResolution.Data
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Source
import Frontend.Syntax.AST
import Frontend.Syntax.Common
import Frontend.Syntax.Name
import Frontend.Syntax.Pattern
import ScopeAndNameResolution.Helper

import Data.List
import Data.List1
import Data.Maybe
import Data.SnocList
import Data.SortedMap

%default total

export
at : Nat -> List a -> Maybe a
at _ [] = Nothing
at Z (x :: _) = Just x
at (S n) (_ :: xs) = at n xs

export
functionNamed : String -> ResolvedModule -> Maybe (AstInfo, FunctionDeclarationNode ResolvedAstPhase)
functionNamed name resolved =
  let MkSourceFileNode _ items = resolved.ast.value
  in head' (mapMaybe pick items)
  where
    pick : ResolvedItem -> Maybe (AstInfo, FunctionDeclarationNode ResolvedAstPhase)
    pick (MkAstNode info _ (ItemFunction fn)) =
      if fn.functionName.value.resolvedNameNodeText == name then Just (info, fn) else Nothing
    pick _ = Nothing

export
constantNamed : String -> ResolvedModule -> Maybe (AstInfo, ConstDeclarationNode ResolvedAstPhase)
constantNamed name resolved =
  let MkSourceFileNode _ items = resolved.ast.value
  in head' (mapMaybe pick items)
  where
    pick : ResolvedItem -> Maybe (AstInfo, ConstDeclarationNode ResolvedAstPhase)
    pick (MkAstNode info _ (ItemConst con)) =
      if con.constName.value.resolvedNameNodeText == name then Just (info, con) else Nothing
    pick _ = Nothing

export
letAt : Nat -> ResolvedBlock -> Maybe (LetBindingNode ResolvedAstPhase)
letAt index block = do
  statement <- at index block.value.blockStatements
  case statement.value of
    StatementLet binding => Just binding
    _ => Nothing

export
exprAt : Nat -> ResolvedBlock -> Maybe ResolvedExpr
exprAt index block = do
  statement <- at index block.value.blockStatements
  case statement.value of
    StatementSemiExpression expression => Just expression
    StatementExpression expression => Just expression
    _ => Nothing

export
binder : ResolvedPattern -> Maybe ResolvedName
binder (MkAstNode _ _ (PatternName _ name)) = Just name
binder _ = Nothing

nameUse : ResolvedExpr -> Maybe ResolvedName
nameUse (MkAstNode _ _ (ExprName name)) = Just name
nameUse _ = Nothing

export
initializer : LetBindingNode ResolvedAstPhase -> Maybe ResolvedExpr
initializer binding = map (.initializerValue) binding.letInitializer

export
symbolId : ResolvedName -> SymbolId
symbolId name = name.value.resolvedNameNodeSymbolId

export
scopeFor : ResolvedModule -> AstNode ResolvedAstPhase a -> Maybe ScopeInfo
scopeFor resolved node = do
  scopeId <- lookup node.astInfo.nodeId resolved.tables.nodeScopes
  lookup scopeId resolved.tables.scopes

sameRole : ReferenceRole -> ReferenceRole -> Bool
sameRole DeclarationReference DeclarationReference = True
sameRole ValueReference ValueReference = True
sameRole AssignmentTarget AssignmentTarget = True
sameRole _ _ = False

-- Compare each occurrence, role and context with its unique reference entry.
-- Compound assignments can reuse a written name for both a write and a read.
-- This catches missing references, wrong targets/roles/contexts and lost spans.
export
referenceMatches : ResolvedModule -> ReferenceRole -> NodeId -> ResolvedName -> Bool
referenceMatches resolved role context name =
  case filter (\ref => ref.occurrence.nodeId == name.astInfo.nodeId &&
                       sameRole ref.role role && ref.contextNode == context) (allReferences resolved) of
    [ref] => ref.target == symbolId name && sameRole ref.role role &&
             ref.contextNode == context && ref.writtenName == name.value.resolvedNameNodeText &&
             spanKey ref.occurrence.span == spanKey name.astInfo.span &&
             lookup name.astInfo.nodeId resolved.tables.nodeScopes == Just ref.enclosingScope &&
             lookup context resolved.tables.nodeScopes == Just ref.enclosingScope
    _ => False

export
useMatches : ResolvedModule -> ResolvedName -> ResolvedExpr -> Maybe Bool
useMatches resolved declaration expression = do
  name <- nameUse expression
  pure (symbolId name == symbolId declaration &&
        referenceMatches resolved ValueReference expression.astInfo.nodeId name)

export
bindingMatches : ScopeInfo -> ResolvedName -> Bool
bindingMatches scope name = case lookup name.value.resolvedNameNodeText scope.valueBindings of
  Nothing => False
  Just binding => binding.target == symbolId name &&
    binding.writtenName == name.value.resolvedNameNodeText &&
    map spanKey binding.introducedAt == Just (spanKey name.astInfo.span) &&
    (case binding.bindingKind of DeclaredBinding => True; _ => False) &&
    (case binding.bindingVisibility of LexicalVisibility => True; _ => False)

export
localMatches : ResolvedModule -> ResolvedName -> Bool -> Bool
localMatches resolved name mutable = case lookup (symbolId name) resolved.tables.localVariables of
  Just (MkLocalVariableInfo actual PendingQubitDefault) =>
    case actual of
      MutableVariable => mutable
      ImmutableVariable => not mutable
  _ => False

export
symbolMatches : ResolvedModule -> ResolvedName -> ScopeId -> String -> AstInfo -> Bool
symbolMatches resolved name scope kind origin =
  case lookup (symbolId name) resolved.tables.symbols of
    Nothing => False
    Just symbol => symbol.symbolId == symbolId name &&
      symbol.declaredName == name.value.resolvedNameNodeText &&
      symbol.declaringScope == scope && symbol.declaringModule == resolved.rootModule &&
      kindText symbol.symbolKind == kind &&
      (case symbol.origin of
         SourceSymbol info => info.nodeId == origin.nodeId && spanKey info.span == spanKey origin.span
         _ => False)

export
isBlock : ScopeInfo -> Bool
isBlock scope = case scope.kind of BlockScope => True; _ => False

export
patternBinders : ResolvedPattern -> List (ResolvedPattern, ResolvedName)
patternBinders pattern@(MkAstNode _ _ node) = case node of
  PatternName _ name => [(pattern, name)]
  PatternTuple elements => concatMap recur (forget elements)
  PatternArray elements => concatMap recur elements
  _ => []
  where
    recur : ResolvedPattern -> List (ResolvedPattern, ResolvedName)
    recur p = patternBinders (assert_smaller node p)

export
blockBody : ResolvedExpr -> Maybe ResolvedBlock
blockBody (MkAstNode _ _ node) = case node of
  ExprBlock block => Just block
  ExprLoop block => Just block
  ExprWhile _ block => Just block
  ExprCtrl (ControlledBlock _ _ block) => Just block
  ExprAdjoint (AdjointBlock block) => Just block
  _ => Nothing

-- Shared semantic assertion for constructs that introduce an ordinary block.
export
blockIsolation : String -> Either String Bool
blockIsolation wrapper = checkSource
  ("fn f(q: qubit) { " ++ wrapper ++ " { let inner = 1; inner; } q; }") $ \resolved => do
    (_, fn) <- functionNamed "f" resolved
    [MkAstNode _ _ (NormalParameter _ _ q _)] <- pure fn.functionParameters
      | _ => Nothing
    outer <- scopeFor resolved fn.functionBody
    construct <- exprAt 0 fn.functionBody
    constructScope <- scopeFor resolved construct
    block <- blockBody construct
    inner <- scopeFor resolved block
    binding <- letAt 0 block
    name <- binder binding.letPattern
    use <- exprAt 1 block
    after <- exprAt 1 fn.functionBody
    innerUse <- useMatches resolved name use
    afterUse <- useMatches resolved q after
    pure (isBlock inner && inner.id /= outer.id && inner.parent == Just outer.id &&
          constructScope.id == outer.id && bindingMatches inner name &&
          isNothing (lookup "inner" outer.valueBindings) && innerUse && afterUse)

-- The parser currently sets the filename on the source-file node only.
-- Check diagnostic coordinates independently; referenceMatches above checks
-- that the full incoming AST span is preserved in the reference table.
export
coordinates : SourceSpan -> (Nat, Nat, Nat, Nat)
coordinates span = (span.start.line, span.start.column, span.end.line, span.end.column)

export
unresolved : String -> String -> Either String Bool
unresolved source expected = map (== expected) (expectUnresolvedName source)

export
nodeHasScope : ResolvedModule -> ScopeId -> AstNode ResolvedAstPhase a -> Bool
nodeHasScope resolved scope node = lookup node.astInfo.nodeId resolved.tables.nodeScopes == Just scope

export
parameterNames : FunctionDeclarationNode ResolvedAstPhase -> Maybe (List ResolvedName)
parameterNames fn = traverse parameterName fn.functionParameters
  where
    parameterName : AstNode ResolvedAstPhase (FunctionParameterNode ResolvedAstPhase) -> Maybe ResolvedName
    parameterName (MkAstNode _ _ (NormalParameter _ _ name _)) = Just name
    parameterName _ = Nothing

export
assignmentAt : Nat -> ResolvedBlock -> Maybe (AssignmentNode ResolvedAstPhase)
assignmentAt index block = do
  statement <- at index block.value.blockStatements
  case statement.value of
    StatementAssignment assignment => Just assignment
    _ => Nothing

export
usesInScope : ResolvedModule -> ScopeId -> List (ResolvedName, ResolvedExpr) -> Maybe Bool
usesInScope resolved scope uses = do
  matches <- traverse (\(declaration, expression) => useMatches resolved declaration expression) uses
  pure (all id matches && all (\(_, expression) => nodeHasScope resolved scope expression) uses)

-- The test supplies the expected name occurrences explicitly; this helper
-- does not discover them by traversing the same expression cases as Resolve.
export
expressionUses : String -> List String -> (ResolvedExpr -> Maybe (List ResolvedExpr)) -> Either String Bool
expressionUses expression expected select = checkSource
  ("fn g(x: i32, n: i32) {} fn f(a: [i32; 2], i: i32, x: i32, n: i32, pair: (i32, i32)) { " ++
   expression ++ "; }") $ \resolved => do
    (_, g) <- functionNamed "g" resolved
    (_, f) <- functionNamed "f" resolved
    names <- parameterNames f
    let declarations = SortedMap.fromList $ map (\name => (name.value.resolvedNameNodeText, name))
                                     (g.functionName :: names)
    targets <- traverse (\name => SortedMap.lookup name declarations) expected
    expression <- exprAt 0 f.functionBody
    uses <- select expression
    names <- traverse nameUse uses
    scope <- scopeFor resolved f.functionBody
    matches <- usesInScope resolved scope.id (zip targets uses)
    pure (length uses == length expected && matches && nodeHasScope resolved scope.id expression &&
          map (\ref => ref.occurrence.nodeId) (valueReferences resolved) == map (\name => name.astInfo.nodeId) names)

-- Compare the complete occurrence inventory as well as each reference's
-- contents, so omitted entries and additional entries both fail the assertion.
export
referenceInventory : ResolvedModule -> List (ReferenceRole, NodeId, ResolvedName) -> Bool
referenceInventory resolved expected =
  let buckets = SortedMap.toList resolved.tables.references
      actual = concatMap (\(key, refs) => map (\ref => (key, ref.occurrence.nodeId)) (refs <>> [])) buckets
  in map fst buckets == sort (nub (map (\(_, _, name) => symbolId name) expected)) &&
     sort actual == sort (map (\(_, _, name) => (symbolId name, name.astInfo.nodeId)) expected) &&
     all (\(role, context, name) => referenceMatches resolved role context name) expected

export
sourceSymbols : ResolvedModule -> List ResolvedSymbolInfo
sourceSymbols resolved = filter fromSource (map snd (SortedMap.toList resolved.tables.symbols))
  where
    fromSource : ResolvedSymbolInfo -> Bool
    fromSource symbol = case symbol.origin of SourceSymbol _ => True; _ => False

-- Resolve a matching single declaration to obtain the expected conflicting
-- SymbolId without depending on how many synthetic Prelude symbols exist.
export
duplicateDeclaration : String -> String -> String -> (Nat, Nat, Nat, Nat) -> Either String Bool
duplicateDeclaration first second name expectedSpan = do
  expected <- checkSource first $ \resolved => do
    root <- lookup resolved.rootScope resolved.tables.scopes
    binding <- lookup name root.valueBindings
    previousSpan <- binding.introducedAt
    pure (binding.target, spanKey previousSpan)
  case resolveSource (first ++ "\n" ++ second) of
    Left (ResolutionFailure (DuplicateDeclaration actual conflicts span previousSpan)) =>
      Right (actual == name && conflicts == [fst expected] && coordinates span == expectedSpan &&
             span.file == previousSpan.file && spanKey previousSpan == snd expected)
    Left err => Left (show err)
    Right _ => Left "Expected DuplicateDeclaration, but resolution succeeded"

-- Returns the name and the binder and constant coordinates of the expected
-- BindingShadowsConstant diagnostic.
export
constantShadowing : String -> Either String (String, (Nat, Nat, Nat, Nat), (Nat, Nat, Nat, Nat))
constantShadowing source = case resolveSource source of
  Left (ResolutionFailure (BindingShadowsConstant name _ binder constant)) =>
    Right (name, coordinates binder, coordinates constant)
  Left err => Left (show err)
  Right _ => Left "Expected BindingShadowsConstant, but resolution succeeded"

module ScopeAndNameResolution.ResolveTestHelper

import Compiler.ScopeAndNameResolution.Data
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Source
import Frontend.Syntax.AST
import Frontend.Syntax.Attribute
import Frontend.Syntax.Common
import Frontend.Syntax.Contract
import Frontend.Syntax.Doc
import Frontend.Syntax.Name
import Frontend.Syntax.Pattern
import Frontend.Syntax.Type
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

-- The value returned by the statement at `index`. Desugaring turns a function
-- body's final expression into such a `return` statement.
export
returnedAt : Nat -> ResolvedBlock -> Maybe ResolvedExpr
returnedAt index block = do
  MkAstNode _ _ (ExprReturn (Just value)) <- exprAt index block
    | _ => Nothing
  Just value

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
sameRole PatternReference PatternReference = True
sameRole _ _ = False

-- Compare each occurrence, role and context with its unique reference entry.
-- A compound assignment retains its operator and has one target occurrence;
-- its read-modify-write behavior is represented by the operator, not a copied name.
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

-- Constants in patterns reference an existing symbol and introduce neither a
-- local binding nor local-variable metadata in the occurrence's scope.
export
constantOccurrenceMatches : ResolvedModule -> ResolvedName -> NodeId -> ResolvedName -> Bool
constantOccurrenceMatches resolved constant context name =
  case scopeFor resolved name of
    Nothing => False
    Just scope =>
      symbolId name == symbolId constant &&
      referenceMatches resolved PatternReference context name &&
      isNothing (lookup (symbolId name) resolved.tables.localVariables) &&
      isNothing (lookup name.value.resolvedNameNodeText scope.valueBindings) &&
      not (elem (symbolId name) (scope.declaredSymbolsInOrder <>> []))

export
constantPatternMatches : ResolvedModule -> ResolvedName -> ResolvedPattern -> Bool
constantPatternMatches resolved constant pattern = case pattern.value of
  PatternPath path =>
    let name = MkAstNode path.astInfo path.metadata
                 (MkResolvedNameNode path.value.firstPathSegmentText path.value.resolvedPathTargetSymbolId)
    in path.value.remainingPathSegmentTexts == [] &&
       path.value.firstPathSegmentText == constant.value.resolvedNameNodeText &&
       constantOccurrenceMatches resolved constant pattern.astInfo.nodeId name
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
  Just (MkLocalVariableInfo actual PendingQbitDefault) =>
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

-- Every block scope must be the scope recorded for its own AST node. This
-- also detects duplicated scope creation for blocks that contain no names.
export
blockScopesMatchNodes : ResolvedModule -> Bool
blockScopesMatchNodes resolved = all matches (SortedMap.toList resolved.tables.scopes)
  where
    matches : (ScopeId, ScopeInfo) -> Bool
    matches (scopeId, scope) = case (scope.kind, scope.origin) of
      (BlockScope, SourceScope info) =>
        lookup info.nodeId resolved.tables.nodeScopes == Just scopeId
      _ => True

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
  ("fn f(q: qbit) { " ++ wrapper ++ " { let inner = 1; inner; } q; }") $ \resolved => do
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
  ("const N: i32 = 2; fn g(x: i32, n: i32) {} fn f(a: [i32; 2], i: i32, x: i32, n: i32, pair: (i32, i32)) { " ++
   expression ++ "; }") $ \resolved => do
    (_, con) <- constantNamed "N" resolved
    (_, g) <- functionNamed "g" resolved
    (_, f) <- functionNamed "f" resolved
    names <- parameterNames f
    let declarations = SortedMap.fromList $ map (\name => (name.value.resolvedNameNodeText, name))
                                     (con.constName :: g.functionName :: names)
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
valueReferenceOccurrence : ResolvedExpr -> Maybe (ReferenceRole, NodeId, ResolvedName)
valueReferenceOccurrence expression = do
  name <- nameUse expression
  pure (ValueReference, expression.astInfo.nodeId, name)

export
sourceSymbols : ResolvedModule -> List ResolvedSymbolInfo
sourceSymbols resolved = filter fromSource (map snd (SortedMap.toList resolved.tables.symbols))
  where
    fromSource : ResolvedSymbolInfo -> Bool
    fromSource symbol = case symbol.origin of SourceSymbol _ => True; _ => False

-- The parser currently accepts only a bare identifier after `for`. For richer
-- resolver fixtures, move the first let's already parsed pattern into the
-- following loop, then remove that let. Its node IDs and diagnostic positions
-- are retained, and the resulting AST contains each node only once.
moveLetPatternToFor : SourceFile CanonicalAstPhase -> Maybe (SourceFile CanonicalAstPhase)
moveLetPatternToFor source = do
  let MkSourceFileNode docs items = source.value
  items <- traverse moveInFunction items
  pure ({ value := MkSourceFileNode docs items } source)
  where
    replaceLoopPattern : CanonicalPattern -> CanonicalExpr -> Maybe CanonicalExpr
    replaceLoopPattern pattern expression = case expression.value of
      ExprFor _ iterator body => Just ({ value := ExprFor pattern iterator body } expression)
      _ => Nothing

    -- A loop that ends the function body was desugared into its `return` statement.
    replaceExpression : CanonicalPattern -> CanonicalExpr -> Maybe CanonicalExpr
    replaceExpression pattern expression = case expression.value of
      ExprReturn (Just returned) => do
        returned <- replaceLoopPattern pattern returned
        pure ({ value := ExprReturn (Just returned) } expression)
      _ => replaceLoopPattern pattern expression

    replaceStatement : CanonicalPattern -> Statement CanonicalAstPhase -> Maybe (Statement CanonicalAstPhase)
    replaceStatement pattern statement = case statement.value of
      StatementExpression expression => do
        expression <- replaceExpression pattern expression
        pure ({ value := StatementExpression expression } statement)
      StatementSemiExpression expression => do
        expression <- replaceExpression pattern expression
        pure ({ value := StatementSemiExpression expression } statement)
      _ => Nothing

    moveInFunction : Item CanonicalAstPhase -> Maybe (Item CanonicalAstPhase)
    moveInFunction item = case item.value of
      ItemFunction fn => do
        first :: loop :: rest <- pure fn.functionBody.value.blockStatements | _ => Nothing
        StatementLet binding <- pure first.value | _ => Nothing
        loop <- replaceStatement binding.letPattern loop
        let body : CanonicalBlock =
              { value := { blockStatements := loop :: rest } fn.functionBody.value } fn.functionBody
        pure ({ value := ItemFunction ({ functionBody := body } fn) } item)
      _ => Just item

withForPattern : String -> (Either FixtureError ResolvedModule -> Either String a) -> Either String a
withForPattern source inspect = do
  canonical <- either (Left . show) Right (canonicalSource source)
  adjusted <- case moveLetPatternToFor canonical of
    Nothing => Left "Expected a let pattern followed by a for loop in the canonical fixture"
    Just adjusted => Right adjusted
  inspect (resolveCanonicalSource adjusted)

export
checkForPattern : String -> (ResolvedModule -> Maybe a) -> Either String a
checkForPattern source inspect = withForPattern source $ \result => case result of
  Left err => Left (show err)
  Right resolved => case inspect resolved of
    Nothing => Left "Unexpected resolved for-pattern fixture or missing table entry"
    Just value => Right value

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

-- Duplicate binders are a resolution error, whereas repeated constant pattern
-- occurrences are legal and must not be rejected by post-parse validation.
export
duplicateBinder : String -> Either String (String, (Nat, Nat, Nat, Nat), (Nat, Nat, Nat, Nat))
duplicateBinder source = case resolveSource source of
  Left (ResolutionFailure (DuplicateDeclaration name [_] current previous)) =>
    Right (name, coordinates current, coordinates previous)
  Left err => Left (show err)
  Right _ => Left "Expected DuplicateDeclaration, but resolution succeeded"

export
duplicateForBinder : String -> Either String (String, (Nat, Nat, Nat, Nat), (Nat, Nat, Nat, Nat))
duplicateForBinder source = withForPattern source $ \result => case result of
  Left (ResolutionFailure (DuplicateDeclaration name [_] current previous)) =>
    Right (name, coordinates current, coordinates previous)
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

export
forConstantShadowing : String -> Either String (String, (Nat, Nat, Nat, Nat), (Nat, Nat, Nat, Nat))
forConstantShadowing source = withForPattern source $ \result => case result of
  Left (ResolutionFailure (BindingShadowsConstant name _ binder constant)) =>
    Right (name, coordinates binder, coordinates constant)
  Left err => Left (show err)
  Right _ => Left "Expected BindingShadowsConstant, but resolution succeeded"

-- Returns the name and the use and local declaration coordinates of the
-- expected LocalValueUsedAsConstant diagnostic.
export
nonConstantUse : String -> Either String (String, (Nat, Nat, Nat, Nat), (Nat, Nat, Nat, Nat))
nonConstantUse source = case resolveSource source of
  Left (ResolutionFailure (LocalValueUsedAsConstant name _ use local)) =>
    Right (name, coordinates use, coordinates local)
  Left err => Left (show err)
  Right _ => Left "Expected LocalValueUsedAsConstant, but resolution succeeded"

-- Every value reference resolves to a symbol with the given kind, in source order.
export
valueReferenceKinds : ResolvedModule -> Maybe (List (String, String))
valueReferenceKinds resolved = traverse describe (valueReferences resolved)
  where
    describe : SymbolReference -> Maybe (String, String)
    describe reference = do
      symbol <- lookup reference.target resolved.tables.symbols
      pure (reference.writtenName, kindText symbol.symbolKind)

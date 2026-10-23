module Compiler.ScopeAndNameResolution.Resolve

import Control.Monad.State
import Compiler.Prelude
import Compiler.TypeChecker.Data
import Compiler.ScopeAndNameResolution.Data
import Compiler.ScopeAndNameResolution.Helper
import Data.List
import Data.List1
import Data.Maybe
import Data.SnocList
import Data.SortedMap
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Source
import Frontend.Syntax.Attribute
import Frontend.Syntax.AST
import Frontend.Syntax.Contract
import Frontend.Syntax.Common
import Frontend.Syntax.Doc
import Frontend.Syntax.Literal
import Frontend.Syntax.Name
import Frontend.Syntax.Operator
import Frontend.Syntax.Pattern
import Frontend.Syntax.Type

%default total

resolveNode : AstInfo -> ProvenanceMetadata -> a -> ResolvedAstNode a
resolveNode astInfo (MkProvenanceMetadata provenance) = resolvedAstNode astInfo provenance

resolveAstNode : {a : Type} -> AstNode CanonicalAstPhase a -> AstNode ResolvedAstPhase a
resolveAstNode (MkAstNode docInfo metadata value) = resolveNode docInfo metadata value

visibleConstantBinding : String -> ScopeTables -> Maybe ScopeBinding
visibleConstantBinding nameText scopeTables =
  case retrieveSymbolBinding nameText scopeTables of
    Binding binding => case map (.symbolKind) (lookup binding.target scopeTables.symbols) of
      Just SymbolConstant => Just binding
      _ => Nothing
    _ => Nothing

rejectConstantShadowing : String -> SourceSpan -> StateT ScopeTables (Either ResolutionError) ()
rejectConstantShadowing nameText binderSpan = do
  scopeTables <- get
  case visibleConstantBinding nameText scopeTables of
    Just binding => case binding.introducedAt of
      Just constantSpan =>
        lift $ Left $ BindingShadowsConstant nameText binding.target binderSpan constantSpan
      -- Constants are only declared from source, which always records the name span.
      Nothing => unreachable {function = "rejectConstantShadowing"} {reason = "constant binding has no introduction span"}
    Nothing => pure ()

rejectLocalNameUsedInConstantRole : String -> SourceSpan -> ScopeBinding -> StateT ScopeTables (Either ResolutionError) ()
rejectLocalNameUsedInConstantRole nameText useSpan binding = do
  scopeTables <- get
  case (scopeTables.constContextBoundary, lookup binding.target scopeTables.symbols) of
    (Just boundary, Just symbol) =>
      if isLocalSymbolKind symbol.symbolKind && isScopeOrAncestor symbol.declaringScope boundary scopeTables
        then case binding.introducedAt of
          Just localSpan =>
            lift $ Left $ LocalValueUsedAsConstant nameText binding.target useSpan localSpan
          -- Locals and parameters are only declared from source, which always records the name span.
          Nothing => unreachable {function = "rejectLocalNameUsedInConstantRole"} {reason = "local binding has no introduction span"}
        else pure ()
    _ => pure ()

-- Resolves an array length or repeat count, restoring any enclosing context afterwards.
withConstContext : StateT ScopeTables (Either ResolutionError) a -> StateT ScopeTables (Either ResolutionError) a
withConstContext resolveConstant = do
  scopeTables <- get
  let enclosingBoundary = scopeTables.constContextBoundary
  put $ { constContextBoundary := Just scopeTables.currentScope } scopeTables
  result <- resolveConstant
  modify $ \scopeTables => { constContextBoundary := enclosingBoundary } scopeTables
  pure result

-- Runs an action inside a new child scope of the current scope, restoring the
-- enclosing scope and scope kind afterwards.
withChildScope : ScopeKind -> ScopeOrigin -> StateT ScopeTables (Either ResolutionError) a -> StateT ScopeTables (Either ResolutionError) a
withChildScope childScopeKind childScopeOrigin resolveInChildScope = do
  scopeTables <- get
  let enclosingScopeId = scopeTables.currentScope
  let enclosingScopeKind = scopeTables.currentScopeKind
  let childScopeId = scopeTables.nextScopeId
  let childScopeInfo = MkScopeInfo
        childScopeId
        childScopeKind
        (Just enclosingScopeId)
        childScopeOrigin
        empty empty empty [<]
  put $
    {
      currentScope := childScopeId,
      currentScopeKind := childScopeKind,
      scopes := insert childScopeId childScopeInfo scopeTables.scopes
    } scopeTables
  result <- resolveInChildScope
  modify $ \scopeTables =>
    {
      currentScope := enclosingScopeId,
      currentScopeKind := enclosingScopeKind
    } scopeTables
  pure result

-- Declares a let/for binder or a function parameter in the current scope.
-- Callers must first go through resolveConstantPatternName: an immutable bare
-- constant name is a constant pattern, not a declaration. Reaching this with a
-- visible constant is therefore always an error.
declareLocalName : SymbolKind
  -> (contextNode : NodeId)
  -> (bindingMutability : Maybe Mutability)
  -> CanonicalName
  -> StateT ScopeTables (Either ResolutionError) ResolvedName
declareLocalName symbolKind contextNode bindingMutability
    (MkAstNode nameInfo metadata (MkNameNode nameText)) = do
  rejectConstantShadowing nameText nameInfo.span
  recordNodeScope nameInfo.nodeId
  scopeTables <- get
  let symbolId = scopeTables.nextSymbolId
  let symbolInfo = MkSymbolInfo
        symbolId
        symbolKind
        ()
        nameText
        scopeTables.currentScope
        scopeTables.currentModule
        LexicalVisibility
        (SourceSymbol nameInfo)
  let variableMutability = case bindingMutability of
        Nothing => ImmutableVariable
        Just Mutable => MutableVariable
  let localVariableInfo = MkLocalVariableInfo variableMutability PendingQubitDefault
  let scopeBinding = MkScopeBinding
        nameText
        (Just nameInfo.span)
        symbolId
        DeclaredBinding
        LexicalVisibility
  let symbolReference = MkSymbolReference
        symbolId
        nameInfo
        scopeTables.currentScope
        contextNode
        DeclarationReference
        nameText
  let bindInScope : ScopeInfo -> ScopeInfo
      bindInScope scope =
        {
          valueBindings := insert nameText scopeBinding scope.valueBindings,
          declaredSymbolsInOrder := scope.declaredSymbolsInOrder :< symbolId
        } scope
  modify $ \scopeTables =>
    {
      symbols := insert symbolId symbolInfo scopeTables.symbols,
      localVariables := insert symbolId localVariableInfo scopeTables.localVariables,
      references := insert symbolId [< symbolReference] scopeTables.references,
      scopes := updateExisting bindInScope scopeTables.currentScope scopeTables.scopes
    } scopeTables
  pure $ resolveNode nameInfo metadata $
    MkResolvedNameNode nameText symbolId

-- Resolves a use of an already visible name and records the reference.
-- Declarations go through declareLocalName or declareValueSymbol instead.
resolveName : (contextNode : NodeId)
  -> (role : ReferenceRole)
  -> CanonicalName
  -> StateT ScopeTables (Either ResolutionError) ResolvedName
resolveName contextNode role
    (MkAstNode nameInfo metadata (MkNameNode nameText)) = do
  recordNodeScope nameInfo.nodeId
  scopeTables <- get
  nameScopeBinding <- case retrieveSymbolBinding nameText scopeTables of
    UnresolvedBinding =>
      lift $ Left $ UnresolvedName nameText nameInfo.span
    InaccessibleBinding symbolId =>
      lift $ Left $ InaccessibleSymbol nameText symbolId nameInfo.span
    Binding scopeBinding => pure scopeBinding
  rejectLocalNameUsedInConstantRole nameText nameInfo.span nameScopeBinding
  let boundSymbolId = nameScopeBinding.target
  let symbolReference = MkSymbolReference
        boundSymbolId
        nameInfo
        scopeTables.currentScope
        contextNode
        role
        nameText
  modify $ \scopeTables =>
    let existingReferences = fromMaybe [<] (lookup boundSymbolId scopeTables.references)
    in {
       references := insert boundSymbolId (existingReferences :< symbolReference) scopeTables.references
    } scopeTables
  pure $ resolveNode nameInfo metadata $
    MkResolvedNameNode nameText boundSymbolId

-- Bare immutable constant names are patterns referring to that constant.
-- Explicit `mut` requests a binding and may not shadow a constant.
resolveConstantPatternName : NodeId -> Maybe Mutability -> CanonicalName ->
                            StateT ScopeTables (Either ResolutionError) (Maybe ResolvedName)
resolveConstantPatternName context mutability name = do
  case mutability of
    Just Mutable => rejectConstantShadowing name.value.nameNodeText name.astInfo.span
    Nothing => pure ()
  scopeTables <- get
  case visibleConstantBinding name.value.nameNodeText scopeTables of
    Just _ => map Just (resolveName context PatternReference name)
    Nothing => pure Nothing

resolveParameterName : NodeId -> Maybe Mutability -> CanonicalName ->
                       StateT ScopeTables (Either ResolutionError) ResolvedName
resolveParameterName context mutability name = do
  constant <- resolveConstantPatternName context mutability name
  case constant of
    Just resolvedConstant => pure resolvedConstant
    Nothing => declareLocalName SymbolFunctionParameter context mutability name

resolveAttribute : CanonicalAttribute -> ResolvedAttribute
resolveAttribute (MkAstNode attributeInfo metadata (MkAttributeNode name arguments)) =
  resolveNode attributeInfo metadata $
    MkAttributeNode
      (resolveAstNode name)
      (map (map resolveAstNode) arguments)

resolvePath : CanonicalPath -> StateT ScopeTables (Either ResolutionError) ResolvedPath
resolvePath (MkAstNode pathAstInfo metadata (MkPathNode firstSegment remainingSegments)) = do
  recordNodeScope pathAstInfo.nodeId
  notImplemented {function = "resolvePath"} {feature = "paths"}
  --pure $ resolveNode pathAstInfo metadata $
  --  MkResolvedPathNode
  --    (pathSegmentText firstSegment)
  --    (map pathSegmentText remainingSegments)
  --    (MkSymbolId pathAstInfo.nodeId.surfaceId)
  --where
  --  pathSegmentText : CanonicalPathSegment -> String
  --  pathSegmentText (MkAstNode _ _ (PathSegmentName text)) = text
  --  pathSegmentText (MkAstNode _ _ PathSegmentSelf) = "self"

resolvePatternUnchecked : CanonicalPattern -> StateT ScopeTables (Either ResolutionError) ResolvedPattern
resolvePatternUnchecked (MkAstNode patternInfo metadata patternNode) = do
  recordNodeScope patternInfo.nodeId
  resolvedPatternNode <- case patternNode of
    PatternWildcard =>
      pure PatternWildcard
    PatternName mutability binderName => do
      constant <- resolveConstantPatternName patternInfo.nodeId mutability binderName
      case constant of
        Just name =>
          pure $ PatternPath $ resolveNode name.astInfo name.metadata $
            MkResolvedPathNode name.value.resolvedNameNodeText [] name.value.resolvedNameNodeSymbolId
        Nothing => do
          resolvedBinderName <- declareLocalName SymbolLocalBinding patternInfo.nodeId mutability binderName
          pure $ PatternName mutability resolvedBinderName
    PatternPath valuePath =>
      notImplemented {function = "resolvePatternUnchecked"} {feature = "path patterns (needed for modules)"}
      --pure $ PatternPath (resolvePath valuePath)
    PatternLiteral literal =>
      pure $ PatternLiteral (resolveAstNode literal)
    PatternParenthesized innerPattern =>
      unreachable {function = "resolvePatternUnchecked"} {reason = "parenthesized patterns should have been removed during desugaring"}
    PatternTuple elementPatterns => do
      resolvedElements <- traverse recur elementPatterns
      pure $ PatternTuple resolvedElements
    PatternArray elementPatterns => do
      resolvedElements <- traverse recur elementPatterns
      pure $ PatternArray resolvedElements
    PatternStruct structPath fieldPatterns => do
      notImplemented {function = "resolvePatternUnchecked"} {feature = "struct patterns"}
      --resolvedFields <- traverse resolveStructPatternField fieldPatterns
      --pure $ PatternStruct (resolvePath structPath) resolvedFields
    PatternEnumTuple variantPath argumentPatterns => do
      notImplemented {function = "resolvePatternUnchecked"} {feature = "tuple-like enum variant patterns"}
      --resolvedArguments <- traverse recur argumentPatterns
      --pure $ PatternEnumTuple (resolvePath variantPath) resolvedArguments
  pure $ resolveNode patternInfo metadata resolvedPatternNode
  where
    recur : CanonicalPattern -> StateT ScopeTables (Either ResolutionError) ResolvedPattern
    recur pattern =
      resolvePatternUnchecked (assert_smaller patternNode pattern)

    --resolveStructPatternField : CanonicalStructPatternField -> StateT ScopeTables (Either ResolutionError) ResolvedStructPatternField
    --resolveStructPatternField (MkAstNode fieldInfo metadata fieldNode) = do
    --  recordNodeScope fieldInfo.nodeId
    --  resolvedFieldNode <- case fieldNode of
    --    -- Desugaring rewrites `{ x }` to `{ x: x }` with a PatternName binder, so
    --    -- `recur` below classifies it: `Point { N }` with a visible constant N is
    --    -- a constant pattern, as in Rust. Never declare it via declareLocalName directly.
    --    StructPatternFieldShorthand _ _ =>
    --      unreachable {function = "resolveStructPatternField"} {reason = "struct pattern field shorthands should have been removed during desugaring"}
    --    StructPatternFieldExplicit fieldName fieldPattern => do
    --      resolvedFieldName <- resolveName fieldInfo.nodeId FieldReference fieldName
    --      resolvedFieldPattern <- recur fieldPattern
    --      pure $ StructPatternFieldExplicit resolvedFieldName resolvedFieldPattern
    --  pure $ resolveNode fieldInfo metadata resolvedFieldNode

-- Check a complete pattern/parameter list after classifying names. Repeated
-- constant references are legal; only local/parameter declarations are binders.
rejectDuplicateBindings : List ResolvedName -> StateT ScopeTables (Either ResolutionError) ()
rejectDuplicateBindings names = do
  scopeTables <- get
  lift $ checkNames scopeTables empty names
  where
    checkNames : ScopeTables -> SortedMap String ResolvedName -> List ResolvedName -> Either ResolutionError ()
    checkNames _ _ [] = Right ()
    checkNames scopeTables seen (name :: rest) =
      case lookup name.value.resolvedNameNodeSymbolId scopeTables.symbols of
        Just symbol => if isLocalSymbolKind symbol.symbolKind
          then case lookup name.value.resolvedNameNodeText seen of
            Just first => Left $ DuplicateDeclaration name.value.resolvedNameNodeText
              [first.value.resolvedNameNodeSymbolId] name.astInfo.span first.astInfo.span
            Nothing => checkNames scopeTables (insert name.value.resolvedNameNodeText name seen) rest
          else checkNames scopeTables seen rest
        Nothing => checkNames scopeTables seen rest

resolvePattern : CanonicalPattern -> StateT ScopeTables (Either ResolutionError) ResolvedPattern
resolvePattern pattern = do
  resolved <- resolvePatternUnchecked pattern
  rejectDuplicateBindings (bindingNames resolved)
  pure resolved
  where
    -- TODO: when struct and enum patterns are implemented, collect their binders
    -- here too (struct shorthand fields, explicit field patterns, enum tuple
    -- arguments); the `_ => []` case would otherwise skip their duplicates.
    -- Duplicate parameters of impl methods must also be checked once ItemImpl is
    -- resolved, since Compiler.Validation.PostParseValidation no longer reports them.
    bindingNames : ResolvedPattern -> List ResolvedName
    bindingNames (MkAstNode _ _ pattern) = case pattern of
      PatternName _ name => [name]
      PatternTuple elements => concatMap (\nested => bindingNames (assert_smaller pattern nested)) (forget elements)
      PatternArray elements => concatMap (\nested => bindingNames (assert_smaller pattern nested)) elements
      _ => []

-- Establish all signature names before resolving any parameter types, so a
-- later parameter also receives a non-constant-use diagnostic in array lengths.
resolveFunctionParameterName : CanonicalFunctionParameter -> StateT ScopeTables (Either ResolutionError) ResolvedName
resolveFunctionParameterName (MkAstNode parameterInfo _ (NormalParameter _ mutability name _)) = do
  recordNodeScope parameterInfo.nodeId
  resolveParameterName parameterInfo.nodeId (map (.value) mutability) name
resolveFunctionParameterName (MkAstNode _ _ (ReceiverParameter _ _)) =
  notImplemented {function = "resolveFunctionParameterName"} {feature = "receiver parameters (self, &self, &mut self)"}

mutual
  resolveExpressionNode : AstInfo -> ExpressionNode CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (ExpressionNode ResolvedAstPhase)
  resolveExpressionNode expressionInfo expression =
    case expression of
      ExprLiteral literal => pure $ ExprLiteral (resolveAstNode literal)
      ExprName name => do
        resolvedName <- resolveName expressionInfo.nodeId ValueReference name
        pure $ ExprName resolvedName
      ExprPath path => do
        resolvedPath <- resolvePath path
        pure $ ExprPath resolvedPath
      ExprBuiltin builtin => pure $ ExprBuiltin builtin
      ExprSelf () => notImplemented {function = "resolveExpressionNode"} {feature = "self expressions"}
      ExprParenthesized inner => unreachable {function = "resolveExpressionNode"} {reason = "parenthesized expressions should have been removed during desugaring"}
      ExprTuple elements => do
        resolvedElements <- traverse resolveNestedExpression elements
        pure $ ExprTuple resolvedElements
      ExprArray elements => do
        resolvedElements <- traverse resolveNestedExpression elements
        pure $ ExprArray resolvedElements
      ExprRepeatedArray element count => do
        resolvedElement <- resolveNestedExpression element
        resolvedCount <- withConstContext (resolveNestedExpression count)
        pure $ ExprRepeatedArray resolvedElement resolvedCount
      ExprStructLiteral path fields => notImplemented {function = "resolveExpressionNode"} {feature = "struct literals (ExprStructLiteral)"}
      ExprCall callee arguments => do
        resolvedCallee <- resolveNestedExpression callee
        resolvedArguments <- traverse resolveNestedExpression arguments
        pure $ ExprCall resolvedCallee resolvedArguments
      ExprMethodCall receiver name arguments => do
        let MkAstNode nameInfo _ _ = name
        recordNodeScope nameInfo.nodeId
        resolvedReceiver <- resolveNestedExpression receiver
        resolvedArguments <- traverse resolveNestedExpression arguments
        pure $ ExprMethodCall resolvedReceiver (resolveAstNode name) resolvedArguments
      ExprField object name => do
        let MkAstNode nameInfo _ _ = name
        recordNodeScope nameInfo.nodeId
        resolvedObject <- resolveNestedExpression object
        pure $ ExprField resolvedObject (resolveAstNode name)
      ExprTupleIndex tuple indexText => do
        resolvedTuple <- resolveNestedExpression tuple
        pure $ ExprTupleIndex resolvedTuple indexText
      ExprIndex object index => do
        resolvedObject <- resolveNestedExpression object
        resolvedIndex <- resolveNestedExpression index
        pure $ ExprIndex resolvedObject resolvedIndex
      ExprUnary operator operand => do
        resolvedOperand <- resolveNestedExpression operand
        pure $ ExprUnary (resolveAstNode operator) resolvedOperand
      ExprBinary operator left right => do
        resolvedLeft <- resolveNestedExpression left
        resolvedRight <- resolveNestedExpression right
        pure $ ExprBinary (resolveAstNode operator) resolvedLeft resolvedRight
      ExprRange start operator end => do
        resolvedStart <- traverse resolveNestedExpression start
        resolvedEnd <- traverse resolveNestedExpression end
        pure $ ExprRange resolvedStart (resolveAstNode operator) resolvedEnd
      ExprCast operand target => do
        resolvedOperand <- resolveNestedExpression operand
        resolvedTarget <- resolveType target
        pure $ ExprCast resolvedOperand resolvedTarget
      ExprBlock block => do
        resolvedBlock <- resolveBlockExpression block
        pure $ ExprBlock resolvedBlock
      ExprIf ifNode => do
        resolvedIfNode <- resolveIfNode ifNode
        pure $ ExprIf resolvedIfNode
      ExprQIf ifNode => notImplemented {function = "resolveExpressionNode"} {feature = "ExprQIf"}
      ExprSIf ifNode => notImplemented {function = "resolveExpressionNode"} {feature = "ExprSIf"}
      ExprMatch matchNode => notImplemented {function = "resolveExpressionNode"} {feature = "ExprMatch"}
      ExprQMatch matchNode => notImplemented {function = "resolveExpressionNode"} {feature = "ExprQMatch"}
      ExprSMatch matchNode => notImplemented {function = "resolveExpressionNode"} {feature = "ExprSMatch"}
      ExprLoop body => do
        resolvedBody <- resolveBlockExpression body
        pure $ ExprLoop resolvedBody
      ExprWhile condition body => do
        resolvedCondition <- resolveNestedExpression condition
        resolvedBody <- resolveBlockExpression body
        pure $ ExprWhile resolvedCondition resolvedBody
      ExprFor pattern iterator body => do
        resolvedIterator <- resolveNestedExpression iterator
        -- The pattern scope originates from the for expression; its body block
        -- gets its own BlockScope originating from the block node.
        (resolvedPattern, resolvedBody) <- withChildScope ForScope (SourceScope expressionInfo) $ do
          resolvedPattern <- resolvePattern pattern
          resolvedBody <- resolveBlockExpression body
          pure (resolvedPattern, resolvedBody)
        pure $ ExprFor resolvedPattern resolvedIterator resolvedBody
      ExprBreak value => do
        resolvedValue <- traverse resolveNestedExpression value
        pure $ ExprBreak resolvedValue
      ExprContinue => pure ExprContinue
      ExprReturn value => do
        resolvedValue <- traverse resolveNestedExpression value
        pure $ ExprReturn resolvedValue
      ExprCtrl control => do
        resolvedControl <- resolveControlExpressionNode control
        pure $ ExprCtrl resolvedControl
      ExprAdjoint adjoint => do
        resolvedAdjoint <- resolveAdjointExpressionNode adjoint
        pure $ ExprAdjoint resolvedAdjoint
    where
      resolveNestedExpression : CanonicalExpr -> StateT ScopeTables (Either ResolutionError) ResolvedExpr
      resolveNestedExpression nestedExpression =
        resolveExpression (assert_smaller expression nestedExpression)

      resolveBlockExpression : CanonicalBlock -> StateT ScopeTables (Either ResolutionError) ResolvedBlock
      resolveBlockExpression
        (MkAstNode blockAstInfo metadata (MkBlockNode blockInnerDocs blockStatements finalExpression)) = do
        (resolvedStatements, resolvedFinalExpression) <- withChildScope BlockScope (SourceScope blockAstInfo) $ do
          recordNodeScope blockAstInfo.nodeId
          resolvedStatements <- traverse (\statement => resolveStatement (assert_smaller expression statement)) blockStatements
          resolvedFinalExpression <- traverse resolveNestedExpression finalExpression
          pure (resolvedStatements, resolvedFinalExpression)
        pure $ resolveNode blockAstInfo metadata $
          MkBlockNode
            (map resolveAstNode blockInnerDocs)
            resolvedStatements
            resolvedFinalExpression

      resolveIfNode : ClassicalIfNode CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (ClassicalIfNode ResolvedAstPhase)
      resolveIfNode ifNode@(MkClassicalIfNode ifCondition ifThenBlock ifElseBranch) = do
        resolvedCondition <- resolveNestedExpression ifCondition
        resolvedThenBlock <- resolveBlockExpression ifThenBlock
        resolvedElseBranch <- traverse resolveElseNode ifElseBranch
        pure $ MkClassicalIfNode resolvedCondition resolvedThenBlock resolvedElseBranch
        where
          resolveElseNode : ClassicalElseNode CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (ClassicalElseNode ResolvedAstPhase)
          resolveElseNode (ElseBlock elseBlock) = do
            resolvedElseBlock <- resolveBlockExpression elseBlock
            pure $ ElseBlock resolvedElseBlock
          resolveElseNode (ElseChainedIf (MkAstNode chainedIfInfo metadata chainedIfNode)) = do
            recordNodeScope chainedIfInfo.nodeId
            resolvedIfNode <- resolveIfNode (assert_smaller ifNode chainedIfNode)
            pure $ ElseChainedIf $
              resolveNode chainedIfInfo metadata resolvedIfNode

      resolveControlExpressionNode : ControlExpressionNode CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (ControlExpressionNode ResolvedAstPhase)
      resolveControlExpressionNode (ControlledCallable controlQubits onBasisRaw controlledCallable) = do
        resolvedControlQubits <- traverse resolveNestedExpression controlQubits
        resolvedCallable <- resolveNestedExpression controlledCallable
        pure $ ControlledCallable
          resolvedControlQubits
          (map resolveAstNode onBasisRaw)
          resolvedCallable
      resolveControlExpressionNode (ControlledBlock controlQubits onBasisRaw controlledBlock) = do
        resolvedControlQubits <- traverse resolveNestedExpression controlQubits
        resolvedBlock <- resolveBlockExpression controlledBlock
        pure $ ControlledBlock
          resolvedControlQubits
          (map resolveAstNode onBasisRaw)
          resolvedBlock

      resolveAdjointExpressionNode : AdjointExpressionNode CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (AdjointExpressionNode ResolvedAstPhase)
      resolveAdjointExpressionNode (AdjointOfCallable adjointedCallable) = do
        resolvedCallable <- resolveNestedExpression adjointedCallable
        pure $ AdjointOfCallable resolvedCallable
      resolveAdjointExpressionNode (AdjointBlock adjointedBlock) = do
        resolvedBlock <- resolveBlockExpression adjointedBlock
        pure $ AdjointBlock resolvedBlock

  resolveExpression : CanonicalExpr -> StateT ScopeTables (Either ResolutionError) ResolvedExpr
  resolveExpression (MkAstNode expressionInfo metadata expressionNode) = do
    recordNodeScope expressionInfo.nodeId
    resolvedExpressionNode <- resolveExpressionNode expressionInfo expressionNode
    pure $ resolveNode expressionInfo metadata resolvedExpressionNode

  resolveType : Ty CanonicalAstPhase (Expr CanonicalAstPhase) -> StateT ScopeTables (Either ResolutionError) (Ty ResolvedAstPhase (Expr ResolvedAstPhase))
  resolveType (MkAstNode tyAstInfo metadata typeNode) = do
    recordNodeScope tyAstInfo.nodeId
    resolvedType <- case typeNode of
        TyPrimitive primitiveName => do
          pure $ TyPrimitive primitiveName
        TyPath typePath => do
          resolvedPath <- resolveTypePath tyAstInfo.nodeId typePath
          pure $ TyPath resolvedPath
        TyUnit => do
          pure TyUnit
        TyParenthesized innerType => do
          unreachable {function = "resolveType"} {reason = "parenthesized types should have been removed during desugaring"}
        TyTuple elementTypes => do
          resolvedElementTypes <- traverse resolveNestedType elementTypes
          pure $ TyTuple resolvedElementTypes
        TyArray elementType sizeExpression => do
          resolvedElementType <- resolveNestedType elementType
          resolvedSizeExpression <- withConstContext (resolveExpression sizeExpression)
          pure $ TyArray
            resolvedElementType
            resolvedSizeExpression
        TySlice elementType => do
          resolvedElementType <- resolveNestedType elementType
          pure $ TySlice resolvedElementType
        TyReference borrowKind referencedType => do
          resolvedReferenceType <- resolveNestedType referencedType
          pure $ TyReference
            (resolveAstNode borrowKind)
            resolvedReferenceType
        TyQualified storageQualifiers qualifiedType => do
          resolvedQualifiedType <- resolveNestedType qualifiedType
          pure $ TyQualified
            (map resolveAstNode storageQualifiers)
            resolvedQualifiedType
        TyFunction functionEffect functionParameters returnType => do
          resolvedFunctionParameters <- traverse resolveParameter functionParameters
          resolvedReturnType <- traverse resolveNestedType returnType
          pure $ TyFunction
            (map resolveAstNode functionEffect)
            resolvedFunctionParameters
            resolvedReturnType
    pure $ resolveNode tyAstInfo metadata resolvedType
      where
        resolveTypePath : NodeId -> AstNode CanonicalAstPhase (PathNode CanonicalAstPhase) ->
                            StateT ScopeTables (Either ResolutionError) (AstNode ResolvedAstPhase ResolvedPathNode)
        resolveTypePath nodeId (MkAstNode pathInfo _ (MkPathNode firstSegment remainingSegments)) = do
          recordNodeScope pathInfo.nodeId
          notImplemented {function = "resolveTypePath"} {feature = "type paths (needed for modules and structs)"}
        resolveNestedType : CanonicalTy -> StateT ScopeTables (Either ResolutionError) ResolvedTy
        resolveNestedType nestedType = resolveType (assert_smaller typeNode nestedType)
        resolveParameter : CanonicalAstNode (FunctionTypeParameterNode CanonicalAstPhase (CanonicalAstNode (ExpressionNode CanonicalAstPhase))) ->
           StateT ScopeTables (Either ResolutionError) $ ResolvedAstNode (FunctionTypeParameterNode ResolvedAstPhase (ResolvedAstNode (ExpressionNode ResolvedAstPhase)))
        resolveParameter (MkAstNode parameterAstInfo metadata (MkFunctionTypeParameterNode parameterName parameterType)) = do
          recordNodeScope parameterAstInfo.nodeId
          resolvedNestedType <- resolveNestedType parameterType
          pure $ resolveNode parameterAstInfo metadata $
            -- Not resolveName: a function-type parameter name is never a
            -- symbol (see the comment on FunctionTypeParameterNode in
            -- Syntax/Type.idr), so only its AstNode wrapping is updated.
            MkFunctionTypeParameterNode (resolveAstNode parameterName) resolvedNestedType

  resolveLetInitializer : LetInitializerNode CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (LetInitializerNode ResolvedAstPhase)
  resolveLetInitializer (MkLetInitializerNode marker value) = do
    resolvedValue <- resolveExpression value
    pure $ MkLetInitializerNode (resolveAstNode marker) resolvedValue

  resolveAssignmentTarget : CanonicalAstNode (AssignmentTargetNode CanonicalAstPhase) -> StateT ScopeTables (Either ResolutionError) (ResolvedAstNode (AssignmentTargetNode ResolvedAstPhase))
  resolveAssignmentTarget (MkAstNode assignmentTargetAstInfo metadata assignmentTargetNode) = do
    recordNodeScope assignmentTargetAstInfo.nodeId
    resolvedAssignmentTarget <- case assignmentTargetNode of
      AssignTargetName targetName => do
        resolvedTargetName <- resolveName assignmentTargetAstInfo.nodeId AssignmentTarget targetName
        pure $ AssignTargetName resolvedTargetName
      AssignTargetIndex targetObject indexExpression => do
        resolvedTargetObject <- resolveExpression targetObject
        resolvedIndexExpression <- resolveExpression indexExpression
        pure $ AssignTargetIndex
          resolvedTargetObject
          resolvedIndexExpression
      AssignTargetField targetObject fieldName => do
        let MkAstNode fieldInfo _ _ = fieldName
        recordNodeScope fieldInfo.nodeId
        resolvedTargetObject <- resolveExpression targetObject
        pure $ AssignTargetField
          resolvedTargetObject
          (resolveAstNode fieldName)
      AssignTargetTupleIndex targetObject tupleIndexRawText => do
        resolvedTargetObject <- resolveExpression targetObject
        pure $ AssignTargetTupleIndex
          resolvedTargetObject
          tupleIndexRawText
    pure (resolveNode assignmentTargetAstInfo metadata resolvedAssignmentTarget)

  resolveStatement : Statement CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (Statement ResolvedAstPhase)
  resolveStatement (MkAstNode statementAstInfo metadata statementNode) = do
    recordNodeScope statementAstInfo.nodeId
    resolvedStatementNode <- case statementNode of
        StatementLet (MkLetBindingNode qualifiers pattern typeAnnotation initializer) => do
          resolvedTypeAnnotation <- traverse (\ty => resolveType (assert_smaller statementNode ty)) typeAnnotation
          resolvedInitializer <- traverse (\init => resolveLetInitializer (assert_smaller statementNode init)) initializer
          -- New bindings are visible only after their annotation and initializer.
          resolvedPattern <- resolvePattern pattern
          pure $ StatementLet $
            MkLetBindingNode
              (map resolveAstNode qualifiers)
              resolvedPattern
              resolvedTypeAnnotation
              resolvedInitializer
        StatementAssignment (MkAssignmentNode assignmentTarget assignmentOperator assignmentValue) => do
          resolvedAssignmentTarget <- resolveAssignmentTarget assignmentTarget
          resolvedExpression <- resolveExpression assignmentValue
          pure $ StatementAssignment $
            MkAssignmentNode
              resolvedAssignmentTarget
              (resolveAstNode assignmentOperator)
              resolvedExpression
        StatementSemiExpression statementExpression => do
          resolvedExpression <- resolveExpression statementExpression
          pure $ StatementSemiExpression resolvedExpression
        StatementExpression statementExpression => do
          resolvedExpression <- resolveExpression statementExpression
          pure $ StatementExpression resolvedExpression
    pure (resolveNode statementAstInfo metadata resolvedStatementNode)

resolveFunctionParameter : ResolvedName -> AstNode CanonicalAstPhase (FunctionParameterNode CanonicalAstPhase) ->
                           StateT ScopeTables (Either ResolutionError) (AstNode ResolvedAstPhase (FunctionParameterNode ResolvedAstPhase))
resolveFunctionParameter resolvedParameterName
  (MkAstNode parameterInfo metadata (NormalParameter parameterDocs parameterMutability parameterName parameterType)) = do
    resolvedParameterType <- resolveType parameterType
    pure $ resolveNode parameterInfo metadata $
      NormalParameter
        (map resolveAstNode parameterDocs)
        (map resolveAstNode parameterMutability)
        resolvedParameterName
        resolvedParameterType
resolveFunctionParameter _ (MkAstNode _ _ (ReceiverParameter _ _)) =
  notImplemented {function = "resolveFunctionParameter"} {feature = "receiver parameters (self, &self, &mut self)"}

resolveSignedPauliTerm : SignedPauliTerm CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (SignedPauliTerm ResolvedAstPhase)
resolveSignedPauliTerm (MkAstNode termInfo metadata (MkSignedPauliTermNode sign pauliString)) = do
  recordNodeScope termInfo.nodeId
  pure $ resolveNode termInfo metadata $
    MkSignedPauliTermNode sign (resolveAstNode pauliString)

resolveContractPredicate : CanonicalContractPredicate -> StateT ScopeTables (Either ResolutionError) ResolvedContractPredicate
resolveContractPredicate (MkAstNode predicateInfo metadata predicateNode) = do
  recordNodeScope predicateInfo.nodeId
  resolvedContract <- case predicateNode of
    ContractClean qubitArgument => do
      resolvedQubitArgument <- resolveExpression qubitArgument
      pure $ ContractClean resolvedQubitArgument
    ContractBasis qubitArgument pauliString => do
      resolvedQubitArgument <- resolveExpression qubitArgument
      pure $ ContractBasis
        resolvedQubitArgument
        (resolveAstNode pauliString)
    ContractSeparable qubitArgument => do
      resolvedQubitArgument <- resolveExpression qubitArgument
      pure $ ContractSeparable resolvedQubitArgument
    ContractIsolated qubitArgument => do
      resolvedQubitArgument <- resolveExpression qubitArgument
      pure $ ContractIsolated resolvedQubitArgument
    ContractProduct firstQubitSet otherQubitSets => do
      resolvedFirstQubitSet <- resolveExpression firstQubitSet
      resolvedOtherQubitSets <- traverse resolveExpression otherQubitSets
      pure $ ContractProduct
        resolvedFirstQubitSet
        resolvedOtherQubitSets
    ContractStabilized qubitArgument stabilizerTerms => do
      resolvedQubitArgument <- resolveExpression qubitArgument
      resolvedStabilizerTerms <- traverse resolveSignedPauliTerm stabilizerTerms
      pure $ ContractStabilized
        resolvedQubitArgument
        resolvedStabilizerTerms
  pure $ resolveNode predicateInfo metadata resolvedContract

resolveContractClause : ContractClause CanonicalAstPhase (Expr CanonicalAstPhase) -> StateT ScopeTables (Either ResolutionError) (ContractClause ResolvedAstPhase (Expr ResolvedAstPhase))
resolveContractClause (MkAstNode contractAstInfo metadata contractClauseNode) = do
  recordNodeScope contractAstInfo.nodeId
  resolvedClause <- case contractClauseNode of
      RequiresClause predicate => do
        resolvedContractPredicate <- resolveContractPredicate predicate
        pure $ RequiresClause resolvedContractPredicate
      EnsuresClause predicate => do
        resolvedContractPredicate <- resolveContractPredicate predicate
        pure $ EnsuresClause resolvedContractPredicate
  pure $ resolveNode contractAstInfo metadata resolvedClause

resolveFunctionBody : Block CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (Block ResolvedAstPhase)
resolveFunctionBody (MkAstNode _ _ (MkBlockNode _ _ (Just _))) =
  unreachable {function = "resolveFunctionBody"} {reason = "the final expression of a function body should have been desugared to a statement"}
resolveFunctionBody (MkAstNode functionBodyAstInfo metadata (MkBlockNode blockInnerDocs blockStatements Nothing)) = do
  resolvedBlockStatement <- withChildScope BlockScope (SourceScope functionBodyAstInfo) $ do
    recordNodeScope functionBodyAstInfo.nodeId
    traverse resolveStatement blockStatements
  pure $ resolveNode functionBodyAstInfo metadata $ MkBlockNode
      (map resolveAstNode blockInnerDocs)
      resolvedBlockStatement
      Nothing

-- Adds a value-namespace declaration to the current scope.
-- Fails with DuplicateDeclaration if the scope already declares the same name.
declareValueSymbol : AstInfo -> SymbolKind -> SymbolVisibility -> CanonicalName -> StateT ScopeTables (Either ResolutionError) ()
declareValueSymbol itemInfo symbolKind visibility (MkAstNode nameInfo _ (MkNameNode nameText)) = do
  recordNodeScope itemInfo.nodeId
  scopeTables <- get
  let symbolId = scopeTables.nextSymbolId
  let currentScope = scopeTables.currentScope
  let existingBinding = lookup currentScope scopeTables.scopes >>= \scope => lookup nameText scope.valueBindings
  case existingBinding of
    Just binding => case binding.introducedAt of
      Just previousSpan =>
        lift $ Left $ DuplicateDeclaration nameText [binding.target] nameInfo.span previousSpan
      -- Source declarations always record their name span. Prelude bindings
      -- live in the parent scope and cannot be a same-scope conflict here.
      Nothing => unreachable {function = "declareValueSymbol"} {reason = "existing source declaration has no introduction span"}
    Nothing => pure ()
  let symbolInfo = MkSymbolInfo
        symbolId
        symbolKind
        ()
        nameText
        currentScope
        scopeTables.currentModule
        visibility
        (SourceSymbol itemInfo)
  let symbolReference = MkSymbolReference symbolId nameInfo currentScope itemInfo.nodeId DeclarationReference nameText
  let scopeBinding = MkScopeBinding nameText (Just nameInfo.span) symbolId DeclaredBinding visibility
  let bindInScope : ScopeInfo -> ScopeInfo
      bindInScope scope =
        {
          valueBindings := insert nameText scopeBinding scope.valueBindings,
          declaredSymbolsInOrder := scope.declaredSymbolsInOrder :< symbolId
        } scope
  modify $ \scopeTables =>
    {
      symbols := insert symbolId symbolInfo scopeTables.symbols,
      references := insert symbolId [< symbolReference] scopeTables.references,
      scopes := updateExisting bindInScope currentScope scopeTables.scopes
    } scopeTables

-- First pass over a scope's items: declares every item name before any item body
-- is resolved, so items can refer to each other regardless of declaration order.
declareItem : CanonicalItem -> StateT ScopeTables (Either ResolutionError) ()
declareItem (MkAstNode itemInfo _ item) =
  case item of
    ItemModule declaration => notImplemented {function = "declareItem"} {feature = "ItemModule"}
    ItemUse declaration => notImplemented {function = "declareItem"} {feature = "ItemUse"}
    ItemConst (MkConstDeclarationNode _ constVisibility constName _ _) =>
      declareValueSymbol itemInfo SymbolConstant (symbolVisibility constVisibility) constName
    ItemEnum declaration => notImplemented {function = "declareItem"} {feature = "ItemEnum"}
    ItemQEnum declaration => notImplemented {function = "declareItem"} {feature = "ItemQEnum"}
    ItemStruct declaration => notImplemented {function = "declareItem"} {feature = "ItemStruct"}
    ItemImpl declaration => notImplemented {function = "declareItem"} {feature = "ItemImpl"}
    ItemFunction (MkFunctionDeclarationNode _ _ functionVisibility _ _ functionName _ _ _ _ _) =>
      declareValueSymbol itemInfo SymbolFunction (symbolVisibility functionVisibility) functionName

-- Resolves the name of an item that declareItem has already declared in the
-- current scope to that declaration's SymbolId.
resolveDeclaredValueName : CanonicalName -> StateT ScopeTables (Either ResolutionError) ResolvedName
resolveDeclaredValueName (MkAstNode nameInfo metadata (MkNameNode nameText)) = do
  recordNodeScope nameInfo.nodeId
  scopeTables <- get
  let declaredBinding = lookup scopeTables.currentScope scopeTables.scopes >>= \scope => lookup nameText scope.valueBindings
  case declaredBinding of
    Just binding => pure $ resolveNode nameInfo metadata $ MkResolvedNameNode nameText binding.target
    Nothing => unreachable {function = "resolveDeclaredValueName"} {reason = "item name was not declared by declareItem"}

-- Second pass over a scope's items: resolves each item against the scope that
-- declareItem has already populated with all item names.
resolveItem : CanonicalItem -> StateT ScopeTables (Either ResolutionError) ResolvedItem
resolveItem (MkAstNode itemInfo metadata item) = do
  resolvedItem <- case item of
    ItemModule declaration => notImplemented {function = "resolveItem"} {feature = "ItemModule"}
    ItemUse declaration => notImplemented {function = "resolveItem"} {feature = "ItemUse"}
    ItemConst declaration => do
      resolvedDeclaration <- resolveConstDeclaration declaration
      pure $ ItemConst resolvedDeclaration
    ItemEnum declaration => notImplemented {function = "resolveItem"} {feature = "ItemEnum"}
    ItemQEnum declaration => notImplemented {function = "resolveItem"} {feature = "ItemQEnum"}
    ItemStruct declaration => notImplemented {function = "resolveItem"} {feature = "ItemStruct"}
    ItemImpl declaration => notImplemented {function = "resolveItem"} {feature = "ItemImpl"}
    ItemFunction declaration => do
      resolvedDeclaration <- resolveFunctionDeclaration declaration
      pure $ ItemFunction resolvedDeclaration
  pure $ resolveNode itemInfo metadata resolvedItem
  where
    resolveConstDeclaration : ConstDeclarationNode CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (ConstDeclarationNode ResolvedAstPhase)
    resolveConstDeclaration (MkConstDeclarationNode constDocs constVisibility constName constType constValue) = do
      resolvedConstName <- resolveDeclaredValueName constName
      resolvedConstType <- resolveType constType
      resolvedConstValue <- resolveExpression constValue
      pure $ MkConstDeclarationNode
        (map resolveAstNode constDocs)
        (map resolveAstNode constVisibility)
        resolvedConstName
        resolvedConstType
        resolvedConstValue

    resolveFunctionDeclaration : FunctionDeclarationNode CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (FunctionDeclarationNode ResolvedAstPhase)
    resolveFunctionDeclaration
        (MkFunctionDeclarationNode
          functionDocs
          functionAttributes
          functionVisibility
          functionConstness
          functionEffect
          functionName
          functionParameters
          returnType
          supportClause
          contractClauses
          functionBody) = do
      resolvedFunctionName <- resolveDeclaredValueName functionName
      (resolvedParameters, resolvedReturnType, resolvedContracts, resolvedBody) <-
        withChildScope FunctionScope (SourceScope itemInfo) $ do
          resolvedParameterNames <- traverse resolveFunctionParameterName functionParameters
          rejectDuplicateBindings resolvedParameterNames
          resolvedParameters <- traverse (\(name, parameter) => resolveFunctionParameter name parameter)
                                         (zip resolvedParameterNames functionParameters)
          resolvedReturnType <- traverse resolveType returnType
          resolvedContracts <- traverse resolveContractClause contractClauses
          resolvedBody <- resolveFunctionBody functionBody
          pure (resolvedParameters, resolvedReturnType, resolvedContracts, resolvedBody)
      pure $ MkFunctionDeclarationNode
        (map resolveAstNode functionDocs)
        (map resolveAttribute functionAttributes)
        (map resolveAstNode functionVisibility)
        (map resolveAstNode functionConstness)
        (map resolveAstNode functionEffect)
        resolvedFunctionName
        resolvedParameters
        resolvedReturnType
        (map resolveAstNode supportClause)
        resolvedContracts
        resolvedBody

registerPrelude : StateT ScopeTables (Either ResolutionError) ()
registerPrelude = do
  scopeTables <- get
  let preludeScopeId = scopeTables.nextScopeId
  let preludeModuleId = scopeTables.nextSymbolId
  let preludeModuleInfo = MkSymbolInfo
        preludeModuleId
        SymbolModule
        ()
        "<prelude>"
        scopeTables.currentScope
        scopeTables.currentModule
        PublicVisibility
        PreludeSymbol
  let preludeScopeInfo = MkScopeInfo
        preludeScopeId
        ModuleScope
        Nothing
        PreludeScope
        empty
        empty
        empty
        [<]
  let attachPrelude : ScopeInfo -> ScopeInfo
      attachPrelude scope =
        {
          parent := Just preludeScopeId,
          declaredSymbolsInOrder := scope.declaredSymbolsInOrder :< preludeModuleId
        } scope
  modify $ \scopeTables =>
    {
      symbols := insert preludeModuleId preludeModuleInfo scopeTables.symbols,
      scopes := insert preludeScopeId preludeScopeInfo $
        updateExisting attachPrelude scopeTables.currentScope scopeTables.scopes,
      memberScopes := insert preludeModuleId preludeScopeId scopeTables.memberScopes
    } scopeTables
  traverse_ (declarePreludeFunction preludeScopeId preludeModuleId) preludeFunctionNames
  where
    declarePreludeFunction : ScopeId -> SymbolId -> String -> StateT ScopeTables (Either ResolutionError) ()
    declarePreludeFunction scopeId moduleId nameText = do
      scopeTables <- get
      let symbolId = scopeTables.nextSymbolId
      let symbolInfo = MkSymbolInfo
            symbolId
            SymbolFunction
            ()
            nameText
            scopeId
            moduleId
            PublicVisibility
            PreludeSymbol
      let scopeBinding = MkScopeBinding
            nameText
            Nothing
            symbolId
            PreludeBinding
            PublicVisibility
      let bindInScope : ScopeInfo -> ScopeInfo
          bindInScope scope =
            {
              valueBindings := insert nameText scopeBinding scope.valueBindings,
              declaredSymbolsInOrder := scope.declaredSymbolsInOrder :< symbolId
            } scope
      modify $ \scopeTables =>
        {
          symbols := insert symbolId symbolInfo scopeTables.symbols,
          scopes := updateExisting bindInScope scopeId scopeTables.scopes
        } scopeTables

||| Perform symbol and scope resolution over the canonical AST of
||| a source file, starting from the scope of the root module.
export
resolveCanonicalSyntax : CanonicalSourceFile -> Either ResolutionError ResolvedModule
resolveCanonicalSyntax (MkAstNode fileInfo metadata (MkSourceFileNode docs items)) = do
  (scopeTables, resolvedItems) <- runStateT initialScopeTables $ do
    registerPrelude
    traverse_ declareItem items
    traverse resolveItem items
  pure $ MkResolvedModule
    moduleSymbolId
    moduleScopeId
    (resolveNode fileInfo metadata $ MkSourceFileNode (map resolveAstNode docs) resolvedItems)
    scopeTables
  where
    moduleScopeId = MkScopeId 0
    moduleSymbolId = MkSymbolId 0
    moduleScopeInfo = MkScopeInfo moduleScopeId ModuleScope Nothing (SourceScope fileInfo) empty empty empty [<]
    -- The root module has no enclosing scope or module, so it declares itself in its own scope and module
    moduleSymbolInfo = MkSymbolInfo moduleSymbolId SymbolModule () "" moduleScopeId moduleSymbolId PublicVisibility (SourceSymbol fileInfo)
    initialScopeTables =
      MkScopeTables
        moduleScopeId
        ModuleScope
        moduleSymbolId
        Nothing
        (singleton fileInfo.nodeId moduleScopeId)
        (singleton moduleSymbolId moduleSymbolInfo)
        empty
        empty
        (singleton moduleScopeId moduleScopeInfo)
        (singleton moduleSymbolId moduleScopeId)

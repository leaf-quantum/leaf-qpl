module Compiler.ScopeAndNameResolution.Resolve

import Control.Monad.State
import Compiler.Prelude
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
resolveAstNode (MkAstNode docInfo (MkProvenanceMetadata provenance) value) = resolveNode docInfo (MkProvenanceMetadata provenance) value

-- Rust reads a binder that names a visible constant as a constant pattern, which
-- is refutable in `let`, parameters and `for`, so such binders are rejected.
-- Items are declared before bodies are resolved, so later constants count too.
rejectConstantShadowing : String -> SourceSpan -> StateT ScopeTables (Either ResolutionError) ()
rejectConstantShadowing nameText binderSpan = do
  scopeTables <- get
  case retrieveSymbolBinding nameText scopeTables of
    Binding binding => case map (.symbolKind) (lookup binding.target scopeTables.symbols) of
      Just SymbolConstant => case binding.introducedAt of
        Just constantSpan =>
          lift $ Left $ BindingShadowsConstant nameText binding.target binderSpan constantSpan
        -- Constants are only declared from source, which always records the name span.
        Nothing => assert_total $ idris_crash "rejectConstantShadowing: constant binding has no introduction span"
      _ => pure ()
    _ => pure ()

resolveName : (contextNode : NodeId)
  -> (role : ReferenceRole)
  -> (bindingMutability : Maybe Mutability)
  -> CanonicalName
  -> StateT ScopeTables (Either ResolutionError) ResolvedName
resolveName contextNode DeclarationReference bindingMutability
    (MkAstNode nameInfo (MkProvenanceMetadata provenance) (MkNameNode nameText)) = do
  rejectConstantShadowing nameText nameInfo.span
  recordNodeScope nameInfo.nodeId
  scopeTables <- get
  let declaredNameSymbolId = scopeTables.nextSymbolId
  let symbolInfo = MkSymbolInfo
        declaredNameSymbolId
        SymbolLocalBinding
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
        declaredNameSymbolId
        DeclaredBinding
        LexicalVisibility
  let symbolReference = MkSymbolReference
        declaredNameSymbolId
        nameInfo
        scopeTables.currentScope
        contextNode
        DeclarationReference
        nameText
  let bindInScope : ScopeInfo -> ScopeInfo
      bindInScope scope =
        {
          valueBindings := insert nameText scopeBinding scope.valueBindings,
          declaredSymbolsInOrder := scope.declaredSymbolsInOrder :< declaredNameSymbolId
        } scope
  modify $ \scopeTables =>
    {
      symbols := insert declaredNameSymbolId symbolInfo scopeTables.symbols,
      localVariables := insert declaredNameSymbolId localVariableInfo scopeTables.localVariables,
      references := insert declaredNameSymbolId [< symbolReference] scopeTables.references,
      scopes := updateExisting bindInScope scopeTables.currentScope scopeTables.scopes
    } scopeTables
  pure $ resolveNode nameInfo (MkProvenanceMetadata provenance) $
    MkResolvedNameNode nameText declaredNameSymbolId

resolveName contextNode role bindingMutability
    (MkAstNode nameInfo (MkProvenanceMetadata provenance) (MkNameNode nameText)) = do
  recordNodeScope nameInfo.nodeId
  scopeTables <- get
  nameScopeBinding <- case retrieveSymbolBinding nameText scopeTables of
    UnresolvedBinding =>
      lift $ Left $ UnresolvedName nameText nameInfo.span
    InnacessibleBinding symbolId =>
      lift $ Left $ InaccessibleSymbol nameText symbolId nameInfo.span
    Binding scopeBinding => pure scopeBinding
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
  pure $ resolveNode nameInfo (MkProvenanceMetadata provenance) $
    MkResolvedNameNode nameText boundSymbolId

resolveParameterName : (contextNode : NodeId) -> (bindingMutability : Maybe Mutability) -> CanonicalName -> StateT ScopeTables (Either ResolutionError) ResolvedName
resolveParameterName contextNodeId bindingMutability (MkAstNode nameInfo (MkProvenanceMetadata provenance) (MkNameNode nameText)) = do
  rejectConstantShadowing nameText nameInfo.span
  recordNodeScope nameInfo.nodeId
  scopeTables <- get
  let symbolId = scopeTables.nextSymbolId
  let symbolInfo = MkSymbolInfo
        symbolId
        SymbolFunctionParameter
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
        contextNodeId
        DeclarationReference
        nameText
  let bindInScope : ScopeInfo -> ScopeInfo
      bindInScope scope =
        {
          valueBindings := insert nameText scopeBinding scope.valueBindings,
          declaredSymbolsInOrder := scope.declaredSymbolsInOrder :< symbolId
        } scope
  put $
    {
      symbols := insert symbolId symbolInfo scopeTables.symbols,
      localVariables := insert symbolId localVariableInfo scopeTables.localVariables,
      references := insert symbolId [< symbolReference] scopeTables.references,
      scopes := updateExisting bindInScope scopeTables.currentScope scopeTables.scopes
    } scopeTables
  pure $ resolveNode nameInfo (MkProvenanceMetadata provenance) $
    MkResolvedNameNode nameText symbolId

resolveAttribute : CanonicalAttribute -> ResolvedAttribute
resolveAttribute (MkAstNode attributeInfo (MkProvenanceMetadata provenance) (MkAttributeNode name arguments)) =
  resolveNode attributeInfo (MkProvenanceMetadata provenance) $
    MkAttributeNode
      (resolveAstNode name)
      (map (map resolveAstNode) arguments)

resolvePath : CanonicalPath -> StateT ScopeTables (Either ResolutionError) ResolvedPath
resolvePath (MkAstNode pathAstInfo (MkProvenanceMetadata provenance) (MkPathNode firstSegment remainingSegments)) = do
  recordNodeScope pathAstInfo.nodeId
  assert_total $ idris_crash "Resolve.idr: resolvePath: paths not yet implemented."
  --pure $ resolveNode pathAstInfo (MkProvenanceMetadata provenance) $
  --  MkResolvedPathNode
  --    (pathSegmentText firstSegment)
  --    (map pathSegmentText remainingSegments)
  --    (MkSymbolId pathAstInfo.nodeId.surfaceId)
  --where
  --  pathSegmentText : CanonicalPathSegment -> String
  --  pathSegmentText (MkAstNode _ _ (PathSegmentName text)) = text
  --  pathSegmentText (MkAstNode _ _ PathSegmentSelf) = "self"

resolvePattern : CanonicalPattern -> StateT ScopeTables (Either ResolutionError) ResolvedPattern
resolvePattern (MkAstNode patternInfo (MkProvenanceMetadata provenance) patternNode) = do
  recordNodeScope patternInfo.nodeId
  resolvedPatternNode <- case patternNode of
    PatternWildcard =>
      pure PatternWildcard
    PatternName mutability binderName => do
      -- duplicate names in a let pattern are detected in PostParseValidation
      resolvedBinderName <- resolveName patternInfo.nodeId DeclarationReference mutability binderName
      pure $ PatternName mutability resolvedBinderName
    PatternPath valuePath =>
      assert_total $ idris_crash "Resolve.idr: resolveStructPatternField: path patterns are not yet supported, should be implemented for module support."
      --pure $ PatternPath (resolvePath valuePath)
    PatternLiteral literal =>
      pure $ PatternLiteral (resolveAstNode literal)
    PatternParenthesized innerPattern =>
      assert_total (idris_crash "Parenthesized patterns should have been removed during the desugaring phase.")
    PatternTuple elementPatterns => do
      resolvedElements <- traverse recur elementPatterns
      pure $ PatternTuple resolvedElements
    PatternArray elementPatterns => do
      resolvedElements <- traverse recur elementPatterns
      pure $ PatternArray resolvedElements
    PatternStruct structPath fieldPatterns => do
      assert_total $ idris_crash "Resolve.idr: resolveStructPatternField: structs are not yet supported."
      --resolvedFields <- traverse resolveStructPatternField fieldPatterns
      --pure $ PatternStruct (resolvePath structPath) resolvedFields
    PatternEnumTuple variantPath argumentPatterns => do
      assert_total $ idris_crash "Resolve.idr: resolveStructPatternField: enums and tuple like enums are not yet supported."
      --resolvedArguments <- traverse recur argumentPatterns
      --pure $ PatternEnumTuple (resolvePath variantPath) resolvedArguments
  pure $ resolveNode patternInfo (MkProvenanceMetadata provenance) resolvedPatternNode
  where
    recur : CanonicalPattern -> StateT ScopeTables (Either ResolutionError) ResolvedPattern
    recur pattern =
      resolvePattern (assert_smaller patternNode pattern)

    --resolveStructPatternField : CanonicalStructPatternField -> StateT ScopeTables (Either ResolutionError) ResolvedStructPatternField
    --resolveStructPatternField (MkAstNode fieldInfo (MkProvenanceMetadata provenance) fieldNode) = do
    --  recordNodeScope fieldInfo.nodeId
    --  resolvedFieldNode <- case fieldNode of
    --    StructPatternFieldShorthand mutability fieldAndBinderName => do
    --      -- This call describes the binder. The shorthand's field reference
    --      -- must also be resolved separately when member lookup is implemented.
    --      resolvedBinderName <- resolveName fieldInfo.nodeId DeclarationReference mutability fieldAndBinderName
    --      pure $ StructPatternFieldShorthand mutability resolvedBinderName
    --    StructPatternFieldExplicit fieldName fieldPattern => do
    --      resolvedFieldName <- resolveName fieldInfo.nodeId FieldReference Nothing fieldName
    --      resolvedFieldPattern <- recur fieldPattern
    --      pure $ StructPatternFieldExplicit resolvedFieldName resolvedFieldPattern
    --  pure $ resolveNode fieldInfo (MkProvenanceMetadata provenance) resolvedFieldNode

mutual
  resolveExpressionNode : NodeId -> ExpressionNode CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (ExpressionNode ResolvedAstPhase)
  resolveExpressionNode expressionNodeId expression =
    case expression of
      ExprLiteral literal => pure $ ExprLiteral (resolveAstNode literal)
      ExprName name => do
        resolvedName <- resolveName expressionNodeId ValueReference Nothing name
        pure $ ExprName resolvedName
      ExprPath path => do
        resolvedPath <- resolvePath path
        pure $ ExprPath resolvedPath
      ExprBuiltin builtin => pure $ ExprBuiltin builtin
      ExprSelf () => assert_total (idris_crash "Resolve.idr: resolveExpressionNode: self and structs are not yet supported.")
      ExprParenthesized inner => assert_total (idris_crash "Parenthesized expressions should have been removed during the desugaring phase.")
      ExprTuple elements => do
        resolvedElements <- traverse resolveNestedExpression elements
        pure $ ExprTuple resolvedElements
      ExprArray elements => do
        resolvedElements <- traverse resolveNestedExpression elements
        pure $ ExprArray resolvedElements
      ExprRepeatedArray element count => do
        resolvedElement <- resolveNestedExpression element
        resolvedCount <- resolveNestedExpression count
        pure $ ExprRepeatedArray resolvedElement resolvedCount
      ExprStructLiteral path fields => assert_total $ idris_crash "Resolve.idr: resolveExpressionNode: ExprStructLiteral not implemented"
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
      ExprQIf ifNode => assert_total $ idris_crash "Resolve.idr: resolveExpressionNode: ExprQIf not implemented"
      ExprSIf ifNode => assert_total $ idris_crash "Resolve.idr: resolveExpressionNode: ExprSIf not implemented"
      ExprMatch matchNode => assert_total $ idris_crash "Resolve.idr: resolveExpressionNode: ExprMatch not implemented"
      ExprQMatch matchNode => assert_total $ idris_crash "Resolve.idr: resolveExpressionNode: ExprQMatch not implemented"
      ExprSMatch matchNode => assert_total $ idris_crash "Resolve.idr: resolveExpressionNode: ExprSMatch not implemented"
      ExprLoop body => do
        resolvedBody <- resolveBlockExpression body
        pure $ ExprLoop resolvedBody
      ExprWhile condition body => do
        resolvedCondition <- resolveNestedExpression condition
        resolvedBody <- resolveBlockExpression body
        pure $ ExprWhile resolvedCondition resolvedBody
      ExprFor pattern iterator body => do
        resolvedIterator <- resolveNestedExpression iterator
        scopeTables <- get
        let enclosingScopeId = scopeTables.currentScope
        let enclosingScopeKind = scopeTables.currentScopeKind
        let forBodyScopeId = scopeTables.nextScopeId
        let MkAstNode bodyAstInfo _ _ = body
        let forBodyScopeInfo = MkScopeInfo
              forBodyScopeId
              ForScope
              (Just enclosingScopeId)
              (SourceScope bodyAstInfo)
              empty empty empty [<]
        modify $ \scopeTables =>
            {
              currentScope := forBodyScopeId,
              currentScopeKind := ForScope,
              scopes := insert forBodyScopeId forBodyScopeInfo scopeTables.scopes
            } scopeTables
        resolvedPattern <- resolvePattern pattern
        resolvedBody <- resolveBlockExpression body
        modify $ \scopeTables =>
            {
              currentScope := enclosingScopeId,
              currentScopeKind := enclosingScopeKind
            } scopeTables
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
        (MkAstNode blockAstInfo (MkProvenanceMetadata provenance) (MkBlockNode blockInnerDocs blockStatements finalExpression)) = do
        scopeTables <- get
        let enclosingScopeId = scopeTables.currentScope
        let enclosingScopeKind = scopeTables.currentScopeKind
        let blockScopeId = scopeTables.nextScopeId
        let blockScopeInfo = MkScopeInfo
              blockScopeId
              BlockScope
              (Just enclosingScopeId)
              (SourceScope blockAstInfo)
              empty empty empty [<]
        modify $ \scopeTables =>
            {
              currentScope := blockScopeId,
              currentScopeKind := BlockScope,
              scopes := insert blockScopeId blockScopeInfo scopeTables.scopes
            } scopeTables
        recordNodeScope blockAstInfo.nodeId
        resolvedStatements <- traverse (\statement => resolveStatement (assert_smaller expression statement)) blockStatements
        resolvedFinalExpression <- traverse resolveNestedExpression finalExpression
        modify $ \scopeTables =>
            {
              currentScope := enclosingScopeId,
              currentScopeKind := enclosingScopeKind
            } scopeTables
        pure $ resolveNode blockAstInfo (MkProvenanceMetadata provenance) $
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
          resolveElseNode (ElseChainedIf (MkAstNode chainedIfInfo (MkProvenanceMetadata provenance) chainedIfNode)) = do
            recordNodeScope chainedIfInfo.nodeId
            resolvedIfNode <- resolveIfNode (assert_smaller ifNode chainedIfNode)
            pure $ ElseChainedIf $
              resolveNode chainedIfInfo (MkProvenanceMetadata provenance) resolvedIfNode

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

  resolveExpression : CanonicalExpr ->  StateT ScopeTables (Either ResolutionError) ResolvedExpr
  resolveExpression (MkAstNode expressionInfo (MkProvenanceMetadata provenance) expressionNode) = do
    recordNodeScope expressionInfo.nodeId
    resolvedExpressionNode <- resolveExpressionNode expressionInfo.nodeId expressionNode
    pure $ resolveNode expressionInfo (MkProvenanceMetadata provenance) resolvedExpressionNode

  resolveType : Ty CanonicalAstPhase (Expr CanonicalAstPhase) ->  StateT ScopeTables (Either ResolutionError) (Ty ResolvedAstPhase (Expr ResolvedAstPhase))
  resolveType (MkAstNode tyAstInfo (MkProvenanceMetadata provenance) typeNode) = do
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
          assert_total (idris_crash "Parenthesized types should have been removed during the desugaring phase.")
        TyTuple elementTypes => do
          resolvedElementTypes <- traverse resolveNestedType elementTypes
          pure $ TyTuple resolvedElementTypes
        TyArray elementType sizeExpression => do
          resolvedElementType <- resolveNestedType elementType
          resolvedSizeExpression <- resolveExpression sizeExpression
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
    pure $ resolveNode tyAstInfo (MkProvenanceMetadata provenance) resolvedType
      where
        resolveTypePath : NodeId -> AstNode CanonicalAstPhase (PathNode CanonicalAstPhase) ->
                            StateT ScopeTables (Either ResolutionError) (AstNode ResolvedAstPhase ResolvedPathNode)
        resolveTypePath nodeId (MkAstNode pathInfo (MkProvenanceMetadata pathProvenance) (MkPathNode firstSegment remainingSegments)) = do
          recordNodeScope pathInfo.nodeId
          assert_total $ idris_crash "Resolving TypePaths is not yet implemented, will be needed to be to enable modules and later structs."
        resolveNestedType : CanonicalTy -> StateT ScopeTables (Either ResolutionError) ResolvedTy
        resolveNestedType nestedType = resolveType (assert_smaller typeNode nestedType)
        resolveParameter : CanonicalAstNode (FunctionTypeParameterNode CanonicalAstPhase (CanonicalAstNode (ExpressionNode CanonicalAstPhase))) ->
           StateT ScopeTables (Either ResolutionError) $ ResolvedAstNode (FunctionTypeParameterNode ResolvedAstPhase (ResolvedAstNode (ExpressionNode ResolvedAstPhase)))
        resolveParameter (MkAstNode parameterAstInfo (MkProvenanceMetadata provenance) (MkFunctionTypeParameterNode parameterName parameterType)) = do
          recordNodeScope parameterAstInfo.nodeId
          resolvedNestedType <- resolveNestedType parameterType
          pure $ resolveNode parameterAstInfo (MkProvenanceMetadata provenance) $
            -- Not resolveName: a function-type parameter name is never a
            -- symbol (see the comment on FunctionTypeParameterNode in
            -- Syntax/Type.idr), so only its AstNode wrapping is updated.
            MkFunctionTypeParameterNode (resolveAstNode parameterName) resolvedNestedType

  resolveFunctionParameterType : AstNode CanonicalAstPhase (FunctionParameterNode CanonicalAstPhase) -> StateT ScopeTables (Either ResolutionError) (Maybe ResolvedTy)
  resolveFunctionParameterType
    (MkAstNode parameterInfo (MkProvenanceMetadata provenance) (NormalParameter parameterDocs parameterMutability parameterName parameterType)) = do
      resolvedType <- resolveType parameterType
      pure (Just resolvedType)
  -- The self syntax has no type annotations in Leaf
  resolveFunctionParameterType
    (MkAstNode parameterInfo (MkProvenanceMetadata provenance) (ReceiverParameter receiverDocs receiverBorrow)) =
      pure Nothing

  resolveFunctionParameter: AstNode CanonicalAstPhase (FunctionParameterNode CanonicalAstPhase) -> Maybe ResolvedTy ->
                            StateT ScopeTables (Either ResolutionError) (AstNode ResolvedAstPhase (FunctionParameterNode ResolvedAstPhase))
  resolveFunctionParameter
    (MkAstNode parameterInfo (MkProvenanceMetadata provenance) (NormalParameter parameterDocs parameterMutability parameterName parameterType))
    (Just resolvedParameterType) = do
      recordNodeScope parameterInfo.nodeId
      resolvedParameterName <- resolveParameterName parameterInfo.nodeId
        (map (\node => node.value) parameterMutability) parameterName
      pure $ resolveNode parameterInfo (MkProvenanceMetadata provenance) $
        NormalParameter
          (map resolveAstNode parameterDocs)
          (map resolveAstNode parameterMutability)
          resolvedParameterName
          resolvedParameterType
  resolveFunctionParameter (MkAstNode parameterInfo (MkProvenanceMetadata provenance) (ReceiverParameter receiverDocs receiverBorrow)) Nothing 
    = assert_total $ idris_crash "Resolve.idr: resolveFunctionParameter: receiver function parameters (self & variants) are not yet supported." 
  resolveFunctionParameter (MkAstNode _ _ (NormalParameter _ _ _ _)) Nothing =
      assert_total $ idris_crash "Resolve.idr: resolveFunctionParameter: normal function parameter is missing its resolved type."
  resolveFunctionParameter (MkAstNode _ _ (ReceiverParameter _ _)) (Just _) =
      assert_total $ idris_crash "Resolve.idr: resolveFunctionParameter: receiver function parameter (self & variants) unexpectedly has a type annotation."

  resolveSignedPauliTerm : SignedPauliTerm CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (SignedPauliTerm ResolvedAstPhase)
  resolveSignedPauliTerm (MkAstNode termInfo (MkProvenanceMetadata provenance) (MkSignedPauliTermNode sign pauliString)) = do
    recordNodeScope termInfo.nodeId
    pure $ resolveNode termInfo (MkProvenanceMetadata provenance) $
      MkSignedPauliTermNode sign (resolveAstNode pauliString)

  resolveContractPredicate : CanonicalContractPredicate -> StateT ScopeTables (Either ResolutionError) ResolvedContractPredicate
  resolveContractPredicate (MkAstNode predicateInfo (MkProvenanceMetadata provenance) predicateNode) = do 
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
    pure $ resolveNode predicateInfo (MkProvenanceMetadata provenance) resolvedContract

  resolveContractClause : ContractClause CanonicalAstPhase (Expr CanonicalAstPhase) -> StateT ScopeTables (Either ResolutionError) (ContractClause ResolvedAstPhase (Expr ResolvedAstPhase))
  resolveContractClause (MkAstNode contractAstInfo (MkProvenanceMetadata provenance) contractClauseNode) = do
    recordNodeScope contractAstInfo.nodeId
    resolvedClause <- case contractClauseNode of
        RequiresClause predicate => do
          resolvedContractPredicate <- resolveContractPredicate predicate
          pure $ RequiresClause resolvedContractPredicate
        EnsuresClause predicate => do
          resolvedContractPredicate <- resolveContractPredicate predicate
          pure $ EnsuresClause resolvedContractPredicate 
    pure $ resolveNode contractAstInfo (MkProvenanceMetadata provenance) resolvedClause 

  resolveLetInitializer : LetInitializerNode CanonicalAstPhase -> StateT ScopeTables (Either ResolutionError) (LetInitializerNode ResolvedAstPhase)
  resolveLetInitializer (MkLetInitializerNode marker value) = do
    resolvedValue <- resolveExpression value
    pure $ MkLetInitializerNode (resolveAstNode marker) resolvedValue

  resolveAssignmentTarget : CanonicalAstNode (AssignmentTargetNode CanonicalAstPhase) -> StateT ScopeTables (Either ResolutionError) (ResolvedAstNode (AssignmentTargetNode ResolvedAstPhase))
  resolveAssignmentTarget (MkAstNode assignmentTargetAstInfo (MkProvenanceMetadata provenance) assignmentTargetNode) = do 
    recordNodeScope assignmentTargetAstInfo.nodeId
    resolvedAssigmentTarget <- case assignmentTargetNode of 
      AssignTargetName targetName => do
        resolvedTargetName <- resolveName assignmentTargetAstInfo.nodeId AssignmentTarget Nothing targetName
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
    pure (resolveNode assignmentTargetAstInfo (MkProvenanceMetadata provenance) resolvedAssigmentTarget)

  resolveStatement : Statement CanonicalAstPhase ->  StateT ScopeTables (Either ResolutionError) (Statement ResolvedAstPhase)
  resolveStatement (MkAstNode statementAstInfo (MkProvenanceMetadata provenance) statementNode) = do
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
    pure (resolveNode statementAstInfo (MkProvenanceMetadata provenance) resolvedStatementNode)
 
resolveFunctionBody : Block CanonicalAstPhase ->  StateT ScopeTables (Either ResolutionError) (Block ResolvedAstPhase)
resolveFunctionBody (MkAstNode _ (MkProvenanceMetadata _) (MkBlockNode _ _ (Just _))) =
  assert_total $ idris_crash "Resolve.idr: resolveFunctionBody: the final expression in a function body should have been desugared to a statement."
resolveFunctionBody (MkAstNode functionBodyAstInfo (MkProvenanceMetadata provenance) (MkBlockNode blockInnerDocs blockStatements Nothing)) = do
  scopeTables <- get
  let enclosingScopeId = scopeTables.currentScope
  let enclosingScopeKind = scopeTables.currentScopeKind
  let functionBodyScopeId = scopeTables.nextScopeId
  let functionBodyScopeInfo = MkScopeInfo
        functionBodyScopeId
        BlockScope
        (Just enclosingScopeId)
        (SourceScope functionBodyAstInfo)
        empty empty empty [<]
  modify $ \scopeTables =>
    {
      currentScope := functionBodyScopeId,
      currentScopeKind := BlockScope,
      scopes := insert functionBodyScopeId functionBodyScopeInfo scopeTables.scopes
    } scopeTables
  recordNodeScope functionBodyAstInfo.nodeId
  resolvedBlockStatement <- traverse resolveStatement blockStatements
  modify $ \scopeTables =>
    {
      currentScope := enclosingScopeId,
      currentScopeKind := enclosingScopeKind
    } scopeTables
  pure $ resolveNode functionBodyAstInfo (MkProvenanceMetadata provenance) $ MkBlockNode
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
      Nothing => assert_total $ idris_crash "declareValueSymbol: existing source declaration has no introduction span"
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
  put $
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
    ItemModule declaration => assert_total $ idris_crash "Resolve.idr: declareItem: ItemModule not implemented"
    ItemUse declaration => assert_total $ idris_crash "Resolve.idr: declareItem: ItemUse not implemented"
    ItemConst (MkConstDeclarationNode _ constVisibility constName _ _) =>
      declareValueSymbol itemInfo SymbolConstant (symbolVisibility constVisibility) constName
    ItemEnum declaration => assert_total $ idris_crash "Resolve.idr: declareItem: ItemEnum not implemented"
    ItemQEnum declaration => assert_total $ idris_crash "Resolve.idr: declareItem: ItemQEnum not implemented"
    ItemStruct declaration => assert_total $ idris_crash "Resolve.idr: declareItem: ItemStruct not implemented"
    ItemImpl declaration => assert_total $ idris_crash "Resolve.idr: declareItem: ItemImpl not implemented"
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
    Nothing => assert_total $ idris_crash "Resolve.idr: resolveDeclaredValueName: item name was not declared by declareItem."

-- Second pass over a scope's items: resolves each item against the scope that
-- declareItem has already populated with all item names.
resolveItem : CanonicalItem -> StateT ScopeTables (Either ResolutionError) ResolvedItem
resolveItem (MkAstNode itemInfo (MkProvenanceMetadata provenance) item) = do
  resolvedItem <- case item of
    ItemModule declaration => assert_total $ idris_crash "Resolve.idr: resolveItem: ItemModule not implemented."
    ItemUse declaration => assert_total $ idris_crash "Resolve.idr: resolveItem: ItemUse not implemented."
    ItemConst declaration => do
      resolvedDeclaration <- resolveConstDeclaration declaration
      pure $ ItemConst resolvedDeclaration
    ItemEnum declaration => assert_total $ idris_crash "Resolve.idr: resolveItem: ItemEnum not implemented"
    ItemQEnum declaration => assert_total $ idris_crash "Resolve.idr: resolveItem: ItemQEnum not implemented"
    ItemStruct declaration => assert_total $ idris_crash "Resolve.idr: resolveItem: ItemStruct not implemented"
    ItemImpl declaration => assert_total $ idris_crash "Resolve.idr: resolveItem: ItemImpl not implemented"
    ItemFunction declaration => do
      resolvedDeclaration <- resolveFunctionDeclaration declaration
      pure $ ItemFunction resolvedDeclaration
  pure $ resolveNode itemInfo (MkProvenanceMetadata provenance) resolvedItem
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
      scopeTables <- get
      let callSiteScopeId = scopeTables.currentScope
      let callSiteScopeKind = scopeTables.currentScopeKind
      let functionDeclarationBlockScopeId = scopeTables.nextScopeId
      let functionDeclarationBlockScopeInfo = 
        MkScopeInfo functionDeclarationBlockScopeId FunctionScope (Just callSiteScopeId) (SourceScope itemInfo) empty empty empty [<]
      modify $ \scopeTables =>
        { 
          currentScope := functionDeclarationBlockScopeId,
          currentScopeKind := FunctionScope,
          scopes := insert functionDeclarationBlockScopeId functionDeclarationBlockScopeInfo scopeTables.scopes
        } scopeTables
      resolvedParameterTypes <- traverse resolveFunctionParameterType functionParameters
      resolvedReturnType <- traverse resolveType returnType
      resolvedParameters <- traverse
        (\(parameter, resolvedType) =>  resolveFunctionParameter parameter resolvedType) (zip functionParameters resolvedParameterTypes)
      resolvedContracts <- traverse resolveContractClause contractClauses
      resolvedBody <- resolveFunctionBody functionBody
      modify $ \scopeTables =>
        { 
          currentScope := callSiteScopeId,
          currentScopeKind := callSiteScopeKind
        } scopeTables
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
  put $
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
      put $
        {
          symbols := insert symbolId symbolInfo scopeTables.symbols,
          scopes := updateExisting bindInScope scopeId scopeTables.scopes
        } scopeTables

||| Perform symbol and scope resolution over the canonical AST of
||| soure a file starting from a scope corresponding to root module.
export
resolveCanonicalSyntax : CanonicalSourceFile -> Either ResolutionError ResolvedModule
resolveCanonicalSyntax (MkAstNode fileInfo provenance (MkSourceFileNode docs items)) = do
  (scopeTables, resolvedItems) <- runStateT initialScopeTables $ do
    registerPrelude
    traverse_ declareItem items
    traverse resolveItem items
  pure $ MkResolvedModule
    moduleSymbolId
    moduleScopeId
    (resolveNode fileInfo provenance $ MkSourceFileNode (map resolveAstNode docs) resolvedItems)
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
        (singleton fileInfo.nodeId moduleScopeId)
        (singleton moduleSymbolId moduleSymbolInfo)
        empty
        empty
        (singleton moduleScopeId moduleScopeInfo)
        (singleton moduleSymbolId moduleScopeId)

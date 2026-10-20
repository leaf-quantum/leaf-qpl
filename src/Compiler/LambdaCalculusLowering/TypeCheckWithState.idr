module Compiler.ScopeAndNameResolution.Resolve

import Control.Monad.State
import Compiler.ScopeAndNameResolution.Data
import Compiler.ScopeAndNameResolution.Helper
import Data.List1
import Data.SortedMap
import Frontend.ASTData
import Frontend.ASTPhases
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
resolveNode astInfo (MkProvenanceMetadata provenance) =
  resolvedAstNode astInfo provenance

resolveAstNode : {a : Type} -> AstNode CanonicalAstPhase a -> AstNode ResolvedAstPhase a
resolveAstNode (MkAstNode docInfo (MkProvenanceMetadata provenance) value) = resolveNode docInfo (MkProvenanceMetadata provenance) value

resolveName : CanonicalName -> State ScopeTables ResolvedName
resolveName (MkAstNode nameInfo (MkProvenanceMetadata provenance) (MkNameNode nameText)) = do
  pure $ resolveNode nameInfo (MkProvenanceMetadata provenance) $
    MkResolvedNameNode nameText (MkSymbolId nameInfo.nodeId.surfaceId) -- TODO REVIEW

resolveAttribute : CanonicalAttribute -> ResolvedAttribute
resolveAttribute (MkAstNode attributeInfo (MkProvenanceMetadata provenance) (MkAttributeNode name arguments)) =
  resolveNode attributeInfo (MkProvenanceMetadata provenance) $
    MkAttributeNode
      (resolveAstNode name)
      (map (map resolveAstNode) arguments)

resolvePath : CanonicalPath -> ResolvedPath
resolvePath (MkAstNode pathAstInfo (MkProvenanceMetadata provenance) (MkPathNode firstSegment remainingSegments)) =
  resolveNode pathAstInfo (MkProvenanceMetadata provenance) $
    MkResolvedPathNode
      (pathSegmentText firstSegment)
      (map pathSegmentText remainingSegments)
      (MkSymbolId pathAstInfo.nodeId.surfaceId) -- TODO REVIEW
  where
    -- pathSegmentText discards each segment's own AstNode (span and
    -- NodeId) down to its bare spelling. That is fine for the FINAL
    -- segment -- its resolved target becomes resolvedPathTargetSymbolId
    -- above -- but every segment BEFORE the last one is a QUALIFIER
    -- (`math` in `math::calculate`) that must itself resolve to some
    -- SymbolId (a module or type) to walk the path at all, and once real
    -- resolution replaces the TODO REVIEW placeholder above, that
    -- per-qualifier lookup needs somewhere to record its result.
    --
    -- ResolvedPathNode has no room for it: it keeps only the final target
    -- and raw segment text (see the comment on ResolvedPathNode in
    -- Syntax/Name.idr). So each qualifier's resolution must instead be
    -- recorded as a SymbolReference with role = QualifierReference in
    -- ResolvedModule.references, built from THIS segment's own AstInfo --
    -- available right here, before pathSegmentText throws the span away --
    -- not from the collapsed path's outer AstInfo. Validate.idr already
    -- expects such entries to reference NodeIds absent from the resolved
    -- AST/nodeScopes table (see its doc comment on validateResolvedModule).
    -- Do not let real path resolution ship without also emitting them, or
    -- a typo'd qualifier ("my_libary::helper") will point at nothing and
    -- its diagnostic will silently vanish.
    pathSegmentText : CanonicalPathSegment -> String
    pathSegmentText (MkAstNode _ _ (PathSegmentName text)) = text
    pathSegmentText (MkAstNode _ _ PathSegmentSelf) = "self"

resolvePattern : CanonicalPattern -> State ScopeTables ResolvedPattern
resolvePattern (MkAstNode patternInfo (MkProvenanceMetadata provenance) patternNode) = do
  resolvedPatternNode <- case patternNode of
    PatternWildcard =>
      pure PatternWildcard
    PatternName mutability binderName => do
      resolvedBinderName <- resolveName binderName
      pure $ PatternName mutability resolvedBinderName
    PatternPath valuePath =>
      pure $ PatternPath (resolvePath valuePath)
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
      resolvedFields <- traverse resolveStructPatternField fieldPatterns
      pure $ PatternStruct (resolvePath structPath) resolvedFields
    PatternEnumTuple variantPath argumentPatterns => do
      resolvedArguments <- traverse recur argumentPatterns
      pure $ PatternEnumTuple (resolvePath variantPath) resolvedArguments
  pure $ resolveNode patternInfo (MkProvenanceMetadata provenance) resolvedPatternNode
  where
    recur : CanonicalPattern -> State ScopeTables ResolvedPattern
    recur pattern =
      resolvePattern (assert_smaller patternNode pattern)

    resolveStructPatternField : CanonicalStructPatternField -> State ScopeTables ResolvedStructPatternField
    resolveStructPatternField (MkAstNode fieldInfo (MkProvenanceMetadata provenance) fieldNode) = do
      resolvedFieldNode <- case fieldNode of
        StructPatternFieldShorthand mutability fieldAndBinderName => do
          resolvedBinderName <- resolveName fieldAndBinderName
          pure $ StructPatternFieldShorthand mutability resolvedBinderName
        StructPatternFieldExplicit fieldName fieldPattern => do
          resolvedFieldName <- resolveName fieldName
          resolvedFieldPattern <- recur fieldPattern
          pure $ StructPatternFieldExplicit resolvedFieldName resolvedFieldPattern
      pure $ resolveNode fieldInfo (MkProvenanceMetadata provenance) resolvedFieldNode

mutual
  resolveExpressionNode : ExpressionNode CanonicalAstPhase -> State ScopeTables (ExpressionNode ResolvedAstPhase)
  resolveExpressionNode expression =
    case expression of
      ExprLiteral literal => pure $ ExprLiteral (resolveAstNode literal)
      ExprName name => do
        resolvedName <- resolveName name
        pure $ ExprName resolvedName
      ExprPath path => pure $ ExprPath (resolvePath path)
      ExprBuiltin builtin => pure $ ExprBuiltin builtin
      ExprSelf () => pure $ ExprSelf ?resolveSelfSymbolId
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
        resolvedReceiver <- resolveNestedExpression receiver
        resolvedArguments <- traverse resolveNestedExpression arguments
        pure $ ExprMethodCall resolvedReceiver (resolveAstNode name) resolvedArguments
      ExprField object name => do
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
        resolvedPattern <- resolvePattern pattern
        resolvedBody <- resolveBlockExpression body
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
      resolveNestedExpression : CanonicalExpr -> State ScopeTables ResolvedExpr
      resolveNestedExpression nestedExpression =
        resolveExpression (assert_smaller expression nestedExpression)

      resolveBlockExpression : CanonicalBlock -> State ScopeTables ResolvedBlock
      resolveBlockExpression
        (MkAstNode blockAstInfo (MkProvenanceMetadata provenance) (MkBlockNode blockInnerDocs blockStatements finalExpression)) = do
        resolvedStatements <- traverse (\statement => resolveStatement (assert_smaller expression statement)) blockStatements
        resolvedFinalExpression <- traverse resolveNestedExpression finalExpression
        pure $ resolveNode blockAstInfo (MkProvenanceMetadata provenance) $
          MkBlockNode
            (map resolveAstNode blockInnerDocs)
            resolvedStatements
            resolvedFinalExpression

      resolveIfNode : ClassicalIfNode CanonicalAstPhase -> State ScopeTables (ClassicalIfNode ResolvedAstPhase)
      resolveIfNode ifNode@(MkClassicalIfNode ifCondition ifThenBlock ifElseBranch) = do
        resolvedCondition <- resolveNestedExpression ifCondition
        resolvedThenBlock <- resolveBlockExpression ifThenBlock
        resolvedElseBranch <- traverse resolveElseNode ifElseBranch
        pure $ MkClassicalIfNode resolvedCondition resolvedThenBlock resolvedElseBranch
        where
          resolveElseNode : ClassicalElseNode CanonicalAstPhase -> State ScopeTables (ClassicalElseNode ResolvedAstPhase)
          resolveElseNode (ElseBlock elseBlock) = do
            resolvedElseBlock <- resolveBlockExpression elseBlock
            pure $ ElseBlock resolvedElseBlock
          resolveElseNode (ElseChainedIf (MkAstNode chainedIfInfo (MkProvenanceMetadata provenance) chainedIfNode)) = do
            resolvedIfNode <- resolveIfNode (assert_smaller ifNode chainedIfNode)
            pure $ ElseChainedIf $
              resolveNode chainedIfInfo (MkProvenanceMetadata provenance) resolvedIfNode

      resolveControlExpressionNode : ControlExpressionNode CanonicalAstPhase -> State ScopeTables (ControlExpressionNode ResolvedAstPhase)
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

      resolveAdjointExpressionNode : AdjointExpressionNode CanonicalAstPhase -> State ScopeTables (AdjointExpressionNode ResolvedAstPhase)
      resolveAdjointExpressionNode (AdjointOfCallable adjointedCallable) = do
        resolvedCallable <- resolveNestedExpression adjointedCallable
        pure $ AdjointOfCallable resolvedCallable
      resolveAdjointExpressionNode (AdjointBlock adjointedBlock) = do
        resolvedBlock <- resolveBlockExpression adjointedBlock
        pure $ AdjointBlock resolvedBlock

  resolveExpression : CanonicalExpr ->  State ScopeTables ResolvedExpr
  resolveExpression (MkAstNode expressionInfo (MkProvenanceMetadata provenance) expressionNode) = do
    resolvedExpressionNode <- resolveExpressionNode expressionNode
    pure $ resolveNode expressionInfo (MkProvenanceMetadata provenance) resolvedExpressionNode

  resolveType : Ty CanonicalAstPhase (Expr CanonicalAstPhase) ->  State ScopeTables (Ty ResolvedAstPhase (Expr ResolvedAstPhase))
  resolveType (MkAstNode tyAstInfo (MkProvenanceMetadata provenance) typeNode) = do
    resolvedType <- case typeNode of
        TyPrimitive primitiveName => do
          pure $ TyPrimitive primitiveName
        TyPath typePath => do
          pure $ TyPath (resolvePath typePath)
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
        resolveNestedType : CanonicalTy -> State ScopeTables ResolvedTy
        resolveNestedType nestedType = resolveType (assert_smaller typeNode nestedType)
        resolveParameter : CanonicalAstNode (FunctionTypeParameterNode CanonicalAstPhase (CanonicalAstNode (ExpressionNode CanonicalAstPhase))) ->
           State ScopeTables $ ResolvedAstNode (FunctionTypeParameterNode ResolvedAstPhase (ResolvedAstNode (ExpressionNode ResolvedAstPhase)))
        resolveParameter (MkAstNode parameterAstInfo (MkProvenanceMetadata provenance) (MkFunctionTypeParameterNode parameterName parameterType)) = do
          resolvedNestedType <- resolveNestedType parameterType
          pure $ resolveNode parameterAstInfo (MkProvenanceMetadata provenance) $
            -- Not resolveName: a function-type parameter name is never a
            -- symbol (see the comment on FunctionTypeParameterNode in
            -- Syntax/Type.idr), so only its AstNode wrapping is updated.
            MkFunctionTypeParameterNode (resolveAstNode parameterName) resolvedNestedType

  resolveFunctionParameter: AstNode CanonicalAstPhase (FunctionParameterNode CanonicalAstPhase) ->  
                            State ScopeTables (AstNode ResolvedAstPhase (FunctionParameterNode ResolvedAstPhase))
  resolveFunctionParameter (MkAstNode parameterInfo (MkProvenanceMetadata provenance) (NormalParameter parameterDocs parameterMutability parameterName parameterType)) = do
    resolvedParameterName <- resolveName parameterName
    resolvedParameterType <- resolveType parameterType
    pure $ resolveNode parameterInfo (MkProvenanceMetadata provenance) $
      NormalParameter
        (map resolveAstNode parameterDocs)
        (map resolveAstNode parameterMutability)
        resolvedParameterName
        resolvedParameterType
  resolveFunctionParameter (MkAstNode parameterInfo (MkProvenanceMetadata provenance) (ReceiverParameter receiverDocs receiverBorrow)) = do
    pure $ resolveNode parameterInfo (MkProvenanceMetadata provenance) $
      ReceiverParameter
        (map resolveAstNode receiverDocs)
        (map resolveAstNode receiverBorrow)

  resolveSignedPauliTerm : SignedPauliTerm CanonicalAstPhase -> State ScopeTables (SignedPauliTerm ResolvedAstPhase)
  resolveSignedPauliTerm (MkAstNode termInfo (MkProvenanceMetadata provenance) (MkSignedPauliTermNode sign pauliString)) = do
    pure $ resolveNode termInfo (MkProvenanceMetadata provenance) $
      MkSignedPauliTermNode sign (resolveAstNode pauliString)

  resolveContractPredicate : CanonicalContractPredicate -> State ScopeTables ResolvedContractPredicate
  resolveContractPredicate (MkAstNode predicateInfo (MkProvenanceMetadata provenance) predicateNode) = do 
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

  resolveContractClause : ContractClause CanonicalAstPhase (Expr CanonicalAstPhase) -> State ScopeTables (ContractClause ResolvedAstPhase (Expr ResolvedAstPhase)) 
  resolveContractClause (MkAstNode contractAstInfo (MkProvenanceMetadata provenance) contractClauseNode) = do
    resolvedClause <- case contractClauseNode of
        RequiresClause predicate => do
          resolvedContractPredicate <- resolveContractPredicate predicate
          pure $ RequiresClause resolvedContractPredicate
        EnsuresClause predicate => do
          resolvedContractPredicate <- resolveContractPredicate predicate
          pure $ EnsuresClause resolvedContractPredicate 
    pure $ resolveNode contractAstInfo (MkProvenanceMetadata provenance) resolvedClause 

  resolveLetInitializer : LetInitializerNode CanonicalAstPhase -> State ScopeTables (LetInitializerNode ResolvedAstPhase)
  resolveLetInitializer (MkLetInitializerNode marker value) = do
    resolvedValue <- resolveExpression value
    pure $ MkLetInitializerNode (resolveAstNode marker) resolvedValue

  resolveAssignmentTarget : CanonicalAstNode (AssignmentTargetNode CanonicalAstPhase) -> State ScopeTables (ResolvedAstNode (AssignmentTargetNode ResolvedAstPhase))
  resolveAssignmentTarget (MkAstNode assignmentTargetAstInfo (MkProvenanceMetadata provenance) assignmentTargetNode) = do 
    resolvedAssigmentTarget <- case assignmentTargetNode of 
      AssignTargetName targetName => do
        resolvedTargetName <- resolveName targetName 
        pure $ AssignTargetName resolvedTargetName
      AssignTargetIndex targetObject indexExpression => do
        resolvedTargetObject <- resolveExpression targetObject
        resolvedIndexExpression <- resolveExpression indexExpression
        pure $ AssignTargetIndex
          resolvedTargetObject
          resolvedIndexExpression
      AssignTargetField targetObject fieldName => do
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

  resolveStatement : Statement CanonicalAstPhase ->  State ScopeTables (Statement ResolvedAstPhase)
  resolveStatement (MkAstNode statementAstInfo (MkProvenanceMetadata provenance) statementNode) = do
    resolvedStatementNode <- case statementNode of
        StatementLet (MkLetBindingNode qualifiers pattern typeAnnotation initializer) => do
          resolvedTypeAnnotation <- traverse (\ty => resolveType (assert_smaller statementNode ty)) typeAnnotation
          resolvedInitializer <- traverse (\init => resolveLetInitializer (assert_smaller statementNode init)) initializer
          resolvedPattern <- resolvePattern pattern
          pure $ StatementLet $
            MkLetBindingNode
              (map resolveAstNode qualifiers)
              resolvedPattern
              resolvedTypeAnnotation
              resolvedInitializer
        StatementAssignment (MkAssignmentNode assignmentTarget assignmentOperator assignmentValue) => do
          resolvedExpression <- resolveExpression assignmentValue
          resolvedAssignmentTarget <- resolveAssignmentTarget assignmentTarget 
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
 
resolveFunctionBody : Block CanonicalAstPhase ->  State ScopeTables (Block ResolvedAstPhase)
resolveFunctionBody (MkAstNode functionBodyAstInfo (MkProvenanceMetadata provenance) (MkBlockNode blockInnerDocs blockStatements finalExpression)) = do
  resolvedBlockStatement <- traverse resolveStatement blockStatements
  resolvedFinalExpression <- traverse resolveExpression finalExpression 
  pure $ resolveNode functionBodyAstInfo (MkProvenanceMetadata provenance) $ MkBlockNode
      (map resolveAstNode blockInnerDocs)
      resolvedBlockStatement 
      resolvedFinalExpression  

resolveItem : CanonicalItem -> State ScopeTables ResolvedItem
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
    resolveConstDeclaration : ConstDeclarationNode CanonicalAstPhase -> State ScopeTables (ConstDeclarationNode ResolvedAstPhase)
    resolveConstDeclaration
        (MkConstDeclarationNode constDocs constVisibility constName constType constValue) = do
      resolvedConstName <- resolveName constName
      resolvedConstType <- resolveType constType
      resolvedConstValue <- resolveExpression constValue
      pure $ MkConstDeclarationNode
        (map resolveAstNode constDocs)
        (map resolveAstNode constVisibility)
        resolvedConstName
        resolvedConstType
        resolvedConstValue

    resolveFunctionDeclaration : FunctionDeclarationNode CanonicalAstPhase -> State ScopeTables (FunctionDeclarationNode ResolvedAstPhase)
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
      resolvedFunctionName <- resolveName functionName
      resolvedParameters <- traverse resolveFunctionParameter functionParameters
      resolvedReturnType <- traverse resolveType returnType
      resolvedContracts <- traverse resolveContractClause contractClauses
      resolvedBody <- resolveFunctionBody functionBody
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


-- creates a scope for modules, functions, blocks and similar constructs;
-- records declarations in symbol tables;
-- assigns a unique SymbolId to each declared entity;
-- resolves variable, function, type and module names;
-- handles shadowing;
-- checks visibility and imports;
-- detects duplicate declarations;
-- reports unknown or ambiguous names.

resolveCanonicalSyntax : CanonicalSourceFile -> Either ResolutionError ResolvedModule
resolveCanonicalSyntax
    (MkAstNode fileInfo (MkProvenanceMetadata provenance) (MkSourceFileNode docs items)) =
  let
    emptyScopeTables = MkScopeTables empty empty empty empty empty empty
    (scopeTables, resolvedItems) = runState emptyScopeTables (traverse resolveItem items)
    resolvedDocs = map resolveAstNode docs
  in Right $
    MkResolvedModule
      (MkSymbolId 0)
      (MkScopeId 0)
      (resolveNode fileInfo (MkProvenanceMetadata provenance) $
        MkSourceFileNode resolvedDocs resolvedItems)
      scopeTables
    

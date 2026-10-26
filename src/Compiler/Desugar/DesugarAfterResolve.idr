module Compiler.ScopeAndNameResolution.Resolve

import Compiler.ScopeAndNameResolution.Data
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

resolveName : CanonicalName -> ResolvedName
resolveName (MkAstNode nameInfo (MkProvenanceMetadata provenance) (MkNameNode nameText)) =
  resolveNode nameInfo (MkProvenanceMetadata provenance) $
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

resolvePattern : CanonicalPattern -> ResolvedPattern
resolvePattern (MkAstNode patternInfo (MkProvenanceMetadata provenance) patternNode) =
  resolveNode patternInfo (MkProvenanceMetadata provenance) $
    case patternNode of
      PatternWildcard =>
        PatternWildcard
      PatternName mutability binderName =>
        PatternName mutability (resolveName binderName)
      PatternPath valuePath =>
        PatternPath (resolvePath valuePath)
      PatternLiteral literal =>
        PatternLiteral (resolveAstNode literal)
      PatternParenthesized innerPattern =>
        PatternParenthesized (recur innerPattern)
      PatternTuple elementPatterns =>
        PatternTuple (map recur elementPatterns)
      PatternArray elementPatterns =>
        PatternArray (map recur elementPatterns)
      PatternStruct structPath fieldPatterns =>
        PatternStruct
          (resolvePath structPath)
          (map resolveStructPatternField fieldPatterns)
      PatternEnumTuple variantPath argumentPatterns =>
        PatternEnumTuple
          (resolvePath variantPath)
          (map recur argumentPatterns)
  where
    recur : CanonicalPattern -> ResolvedPattern
    recur pattern =
      resolvePattern (assert_smaller patternNode pattern)

    resolveStructPatternField : CanonicalStructPatternField -> ResolvedStructPatternField
    resolveStructPatternField (MkAstNode fieldInfo (MkProvenanceMetadata provenance) fieldNode) =
      resolveNode fieldInfo (MkProvenanceMetadata provenance) $
        case fieldNode of
          StructPatternFieldShorthand mutability fieldAndBinderName =>
            StructPatternFieldShorthand
              mutability
              (resolveName fieldAndBinderName)
          StructPatternFieldExplicit fieldName fieldPattern =>
            StructPatternFieldExplicit
              (resolveName fieldName)
              (recur fieldPattern)

mutual
  resolveExpressionNode : ExpressionNode CanonicalAstPhase -> ExpressionNode ResolvedAstPhase
  resolveExpressionNode expression =
    case expression of
      ExprLiteral literal => ExprLiteral (resolveAstNode literal)
      ExprName name => ExprName (resolveName name)
      ExprPath path => ExprPath (resolvePath path)
      ExprBuiltin builtin => ExprBuiltin builtin
      ExprSelf () => ExprSelf ?resolveSelfSymbolId
      ExprParenthesized inner => ExprParenthesized (resolveNestedExpression inner)
      ExprTuple elements => ExprTuple (map resolveNestedExpression elements)
      ExprArray elements => ExprArray (map resolveNestedExpression elements)
      ExprRepeatedArray element count => ExprRepeatedArray (resolveNestedExpression element) (resolveNestedExpression count)
      ExprStructLiteral path fields => assert_total $ idris_crash "Resolve.idr: resolveExpressionNode: ExprStructLiteral not implemented"
      ExprCall callee arguments => ExprCall (resolveNestedExpression callee) (map resolveNestedExpression arguments)
      ExprMethodCall receiver name arguments => ExprMethodCall (resolveNestedExpression receiver) (resolveName name) (map resolveNestedExpression arguments)
      ExprField object name => ExprField (resolveNestedExpression object) (resolveName name)
      ExprTupleIndex tuple indexText => ExprTupleIndex (resolveNestedExpression tuple) indexText
      ExprIndex object index => ExprIndex (resolveNestedExpression object) (resolveNestedExpression index)
      ExprUnary operator operand => ExprUnary (resolveAstNode operator) (resolveNestedExpression operand)
      ExprBinary operator left right => ExprBinary (resolveAstNode operator) (resolveNestedExpression left) (resolveNestedExpression right)
      ExprRange start operator end => ExprRange (map resolveNestedExpression start) (resolveAstNode operator) (map resolveNestedExpression end)
      ExprCast operand target => ExprCast (resolveNestedExpression operand) (resolveType target)
      ExprBlock block => ExprBlock (resolveBlockExpression block)
      ExprIf ifNode => ExprIf (resolveIfNode ifNode)
      ExprQIf ifNode => assert_total $ idris_crash "Resolve.idr: resolveExpressionNode: ExprQIf not implemented"
      ExprSIf ifNode => assert_total $ idris_crash "Resolve.idr: resolveExpressionNode: ExprSIf not implemented"
      ExprMatch matchNode => assert_total $ idris_crash "Resolve.idr: resolveExpressionNode: ExprMatch not implemented"
      ExprQMatch matchNode => assert_total $ idris_crash "Resolve.idr: resolveExpressionNode: ExprQMatch not implemented"
      ExprSMatch matchNode => assert_total $ idris_crash "Resolve.idr: resolveExpressionNode: ExprSMatch not implemented"
      ExprLoop body => ExprLoop (resolveBlockExpression body)
      ExprWhile condition body => ExprWhile (resolveNestedExpression condition) (resolveBlockExpression body)
      ExprFor pattern iterator body => ExprFor (resolvePattern pattern) (resolveNestedExpression iterator) (resolveBlockExpression body)
      ExprBreak value => ExprBreak (map resolveNestedExpression value)
      ExprContinue => ExprContinue
      ExprReturn value => ExprReturn (map resolveNestedExpression value)
      ExprCtrl control => ExprCtrl (resolveControlExpressionNode control)
      ExprAdjoint adjoint => ExprAdjoint (resolveAdjointExpressionNode adjoint)
    where
      resolveNestedExpression : CanonicalExpr -> ResolvedExpr
      resolveNestedExpression nestedExpression =
        resolveExpression (assert_smaller expression nestedExpression)
      resolveBlockExpression : CanonicalBlock -> ResolvedBlock
      resolveBlockExpression 
        (MkAstNode blockAstInfo (MkProvenanceMetadata provenance) (MkBlockNode blockInnerDocs blockStatements finalExpression)) =
        resolveNode blockAstInfo (MkProvenanceMetadata provenance) $
          MkBlockNode 
            (map resolveAstNode blockInnerDocs) 
            (map (\statement => resolveStatement (assert_smaller expression statement)) blockStatements) 
            (map resolveNestedExpression finalExpression)
      resolveIfNode : ClassicalIfNode CanonicalAstPhase -> ClassicalIfNode ResolvedAstPhase
      resolveIfNode ifNode@(MkClassicalIfNode ifCondition ifThenBlock ifElseBranch) =
        MkClassicalIfNode
          (resolveNestedExpression ifCondition)
          (resolveBlockExpression ifThenBlock)
          (map resolveElseNode ifElseBranch)
        where
          resolveElseNode : ClassicalElseNode CanonicalAstPhase -> ClassicalElseNode ResolvedAstPhase
          resolveElseNode (ElseBlock elseBlock) =
            ElseBlock (resolveBlockExpression elseBlock)
          resolveElseNode (ElseChainedIf (MkAstNode chainedIfInfo (MkProvenanceMetadata provenance) chainedIfNode)) =
            ElseChainedIf $
              resolveNode chainedIfInfo (MkProvenanceMetadata provenance) $
                resolveIfNode (assert_smaller ifNode chainedIfNode)
      resolveControlExpressionNode : ControlExpressionNode CanonicalAstPhase -> ControlExpressionNode ResolvedAstPhase
      resolveControlExpressionNode (ControlledCallable controlQubits onBasisRaw controlledCallable) =
        ControlledCallable
          (map resolveNestedExpression controlQubits)
          (map resolveAstNode onBasisRaw)
          (resolveNestedExpression controlledCallable)
      resolveControlExpressionNode (ControlledBlock controlQubits onBasisRaw controlledBlock) =
        ControlledBlock
          (map resolveNestedExpression controlQubits)
          (map resolveAstNode onBasisRaw)
          (resolveBlockExpression controlledBlock)
      resolveAdjointExpressionNode : AdjointExpressionNode CanonicalAstPhase -> AdjointExpressionNode ResolvedAstPhase
      resolveAdjointExpressionNode (AdjointOfCallable adjointedCallable) = AdjointOfCallable (resolveNestedExpression adjointedCallable)
      resolveAdjointExpressionNode (AdjointBlock adjointedBlock) = AdjointBlock (resolveBlockExpression adjointedBlock)

  resolveExpression : CanonicalExpr -> ResolvedExpr
  resolveExpression (MkAstNode expressionInfo (MkProvenanceMetadata provenance) expressionNode) =
    resolveNode expressionInfo (MkProvenanceMetadata provenance) (resolveExpressionNode expressionNode)

  resolveType : Ty CanonicalAstPhase (Expr CanonicalAstPhase) -> Ty ResolvedAstPhase (Expr ResolvedAstPhase)
  resolveType (MkAstNode tyAstInfo (MkProvenanceMetadata provenance) typeNode) =
    resolveNode tyAstInfo (MkProvenanceMetadata provenance) $
      case typeNode of
        TyPrimitive primitiveName =>
          TyPrimitive primitiveName
        TyPath typePath =>
          TyPath (resolvePath typePath)
        TyUnit =>
          TyUnit
        TyParenthesized innerType =>
          TyParenthesized (resolveNestedType innerType)
        TyTuple elementTypes =>
          TyTuple (map resolveNestedType elementTypes)
        TyArray elementType sizeExpression =>
          TyArray 
            (resolveNestedType elementType) 
            (resolveExpression sizeExpression)
        TySlice elementType =>
          TySlice (resolveNestedType elementType)
        TyReference borrowKind referencedType =>
          TyReference 
            (resolveAstNode borrowKind) 
            (resolveNestedType referencedType)
        TyQualified multiplicityQualifier qualifiedType =>
          TyQualified (resolveAstNode multiplicityQualifier) (resolveNestedType qualifiedType)
        TyFunction functionEffect functionParameters returnType =>
          TyFunction
            (map resolveAstNode functionEffect)
            (map resolveParameter functionParameters)
            (map resolveNestedType returnType)
      where
        resolveNestedType : CanonicalTy -> ResolvedTy
        resolveNestedType nestedType =
          resolveType (assert_smaller typeNode nestedType)
        resolveParameter : CanonicalAstNode (FunctionTypeParameterNode CanonicalAstPhase (CanonicalAstNode (ExpressionNode CanonicalAstPhase))) ->
          ResolvedAstNode (FunctionTypeParameterNode ResolvedAstPhase (ResolvedAstNode (ExpressionNode ResolvedAstPhase)))
        resolveParameter (MkAstNode parameterAstInfo (MkProvenanceMetadata provenance) (MkFunctionTypeParameterNode parameterName parameterType)) =
          resolveNode parameterAstInfo (MkProvenanceMetadata provenance) $
            -- Not resolveName: a function-type parameter name is never a
            -- symbol (see the comment on FunctionTypeParameterNode in
            -- Syntax/Type.idr), so only its AstNode wrapping is updated.
            MkFunctionTypeParameterNode (resolveAstNode parameterName) (resolveNestedType parameterType)

  resolveFunctionParameter: AstNode CanonicalAstPhase (FunctionParameterNode CanonicalAstPhase) -> AstNode ResolvedAstPhase (FunctionParameterNode ResolvedAstPhase)
  resolveFunctionParameter (MkAstNode parameterInfo (MkProvenanceMetadata provenance) (NormalParameter parameterDocs parameterMutability parameterName parameterType)) =
    resolveNode parameterInfo (MkProvenanceMetadata provenance) $
      NormalParameter
        (map resolveAstNode parameterDocs)
        (map resolveAstNode parameterMutability)
        (resolveName parameterName)
        (resolveType parameterType)
  resolveFunctionParameter (MkAstNode parameterInfo (MkProvenanceMetadata provenance) (ReceiverParameter receiverDocs receiverBorrow)) =
    resolveNode parameterInfo (MkProvenanceMetadata provenance) $
      ReceiverParameter
        (map resolveAstNode receiverDocs)
        (map resolveAstNode receiverBorrow)

  resolveSignedPauliTerm : SignedPauliTerm CanonicalAstPhase -> SignedPauliTerm ResolvedAstPhase
  resolveSignedPauliTerm (MkAstNode termInfo (MkProvenanceMetadata provenance) (MkSignedPauliTermNode sign pauliString)) =
    resolveNode termInfo (MkProvenanceMetadata provenance) $
      MkSignedPauliTermNode sign (resolveAstNode pauliString)

  resolveContractPredicate : CanonicalContractPredicate -> ResolvedContractPredicate
  resolveContractPredicate (MkAstNode predicateInfo (MkProvenanceMetadata provenance) predicateNode) =
    resolveNode predicateInfo (MkProvenanceMetadata provenance) $
      case predicateNode of
        ContractClean qubitArgument =>
          ContractClean (resolveExpression qubitArgument)
        ContractBasis qubitArgument pauliString =>
          ContractBasis
            (resolveExpression qubitArgument)
            (resolveAstNode pauliString)
        ContractSeparable qubitArgument =>
          ContractSeparable (resolveExpression qubitArgument)
        ContractIsolated qubitArgument =>
          ContractIsolated (resolveExpression qubitArgument)
        ContractProduct firstQubitSet otherQubitSets =>
          ContractProduct
            (resolveExpression firstQubitSet)
            (map resolveExpression otherQubitSets)
        ContractStabilized qubitArgument stabilizerTerms =>
          ContractStabilized
            (resolveExpression qubitArgument)
            (map resolveSignedPauliTerm stabilizerTerms)

  resolveContractClause : ContractClause CanonicalAstPhase (Expr CanonicalAstPhase) -> ContractClause ResolvedAstPhase (Expr ResolvedAstPhase) 
  resolveContractClause (MkAstNode contractAstInfo (MkProvenanceMetadata provenance) contractClauseNode) =
    resolveNode contractAstInfo (MkProvenanceMetadata provenance) $
      case contractClauseNode of
        RequiresClause predicate => RequiresClause (resolveContractPredicate predicate)
        EnsuresClause predicate => EnsuresClause (resolveContractPredicate predicate)

  resolveLetInitializer : LetInitializerNode CanonicalAstPhase -> LetInitializerNode ResolvedAstPhase
  resolveLetInitializer (MkLetInitializerNode marker value) =
    MkLetInitializerNode (resolveAstNode marker) (resolveExpression value)

  resolveAssignmentTarget : CanonicalAstNode (AssignmentTargetNode CanonicalAstPhase) -> ResolvedAstNode (AssignmentTargetNode ResolvedAstPhase)
  resolveAssignmentTarget (MkAstNode assignmentTargetAstInfo (MkProvenanceMetadata provenance) assignmentTargetNode) =
    resolveNode assignmentTargetAstInfo (MkProvenanceMetadata provenance) $
      case assignmentTargetNode of
        AssignTargetName targetName =>
          AssignTargetName (resolveName targetName)
        AssignTargetIndex targetObject indexExpression =>
          AssignTargetIndex
            (resolveExpression targetObject)
            (resolveExpression indexExpression)
        AssignTargetField targetObject fieldName =>
          AssignTargetField
            (resolveExpression targetObject)
            (resolveName fieldName)
        AssignTargetTupleIndex targetObject tupleIndexRawText =>
          AssignTargetTupleIndex
            (resolveExpression targetObject)
            tupleIndexRawText

  resolveStatement : Statement CanonicalAstPhase -> Statement ResolvedAstPhase
  resolveStatement (MkAstNode statementAstInfo (MkProvenanceMetadata provenance) statementNode) =
    resolveNode statementAstInfo (MkProvenanceMetadata provenance) $
      case statementNode of
        StatementLet (MkLetBindingNode qualifiers pattern typeAnnotation initializer) =>
          StatementLet $
            MkLetBindingNode
              (map resolveAstNode qualifiers)
              (resolvePattern pattern)
              (map (\ty => resolveType (assert_smaller statementNode ty)) typeAnnotation)
              (map (\init => resolveLetInitializer (assert_smaller statementNode init)) initializer)
        StatementAssignment (MkAssignmentNode assignmentTarget assignmentOperator assignmentValue) =>
          StatementAssignment $
            MkAssignmentNode
              (resolveAssignmentTarget assignmentTarget)
              (resolveAstNode assignmentOperator)
              (resolveExpression assignmentValue)
        StatementSemiExpression statementExpression =>
          StatementSemiExpression (resolveExpression statementExpression)
        StatementExpression statementExpression =>
          StatementExpression (resolveExpression statementExpression)
 
resolveFunctionBody : Block CanonicalAstPhase -> Block ResolvedAstPhase
resolveFunctionBody (MkAstNode functionBodyAstInfo (MkProvenanceMetadata provenance) (MkBlockNode blockInnerDocs blockStatements finalExpression)) =
  resolveNode functionBodyAstInfo (MkProvenanceMetadata provenance) $
    MkBlockNode
      (map resolveAstNode blockInnerDocs)
      (map resolveStatement blockStatements)
      (map resolveExpression finalExpression)

resolveItem : CanonicalItem -> ResolvedItem
resolveItem (MkAstNode itemInfo (MkProvenanceMetadata provenance) item) =
  resolveNode itemInfo (MkProvenanceMetadata provenance) $
    case item of
      ItemModule declaration => assert_total $ idris_crash "Resolve.idr: resolveItem: ItemModule not implemented."
      ItemUse declaration => assert_total $ idris_crash "Resolve.idr: resolveItem: ItemUse not implemented."
      ItemConst declaration => ItemConst $ resolveConstDeclaration declaration
      ItemEnum declaration => assert_total $ idris_crash "Resolve.idr: resolveItem: ItemEnum not implemented"
      ItemQEnum declaration => assert_total $ idris_crash "Resolve.idr: resolveItem: ItemQEnum not implemented"
      ItemStruct declaration => assert_total $ idris_crash "Resolve.idr: resolveItem: ItemStruct not implemented"
      ItemImpl declaration => assert_total $ idris_crash "Resolve.idr: resolveItem: ItemImpl not implemented"
      ItemFunction declaration => ItemFunction $ resolveFunctionDeclaration declaration
    where
      resolveConstDeclaration : ConstDeclarationNode CanonicalAstPhase -> ConstDeclarationNode ResolvedAstPhase
      resolveConstDeclaration
          (MkConstDeclarationNode
            constDocs
            constVisibility
            (MkAstNode constNameInfo constNameMetadata constNameNode)
            constType
            constValue) =
              MkConstDeclarationNode
                (map resolveAstNode constDocs)
                (map resolveAstNode constVisibility)
                (resolveName (MkAstNode constNameInfo constNameMetadata constNameNode))
                (resolveType constType)
                (resolveExpression constValue)
      resolveFunctionDeclaration : FunctionDeclarationNode CanonicalAstPhase -> FunctionDeclarationNode ResolvedAstPhase
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
            functionBody
          ) = MkFunctionDeclarationNode
                (map resolveAstNode functionDocs)
                (map resolveAttribute functionAttributes)
                (map resolveAstNode functionVisibility)
                (map resolveAstNode functionConstness)
                (map resolveAstNode functionEffect)
                (resolveName functionName)
                (map resolveFunctionParameter functionParameters)
                (map resolveType returnType)
                (map resolveAstNode supportClause)
                (map resolveContractClause contractClauses)
                (resolveFunctionBody functionBody)


-- Desugar := and scratch qubits by adding a uncompute() when variables go out of scope and are not returned
resolveCanonicalSyntax : CanonicalSourceFile -> Either ResolutionError ResolvedModule
resolveCanonicalSyntax
    (MkAstNode fileInfo (MkProvenanceMetadata provenance) (MkSourceFileNode docs items)) =
  Right $
    MkResolvedModule
      (resolveNode fileInfo (MkProvenanceMetadata provenance) $
        MkSourceFileNode
          (map resolveAstNode docs)
          (map resolveItem items))
      (MkScopeId 0)
      empty
      empty
      empty

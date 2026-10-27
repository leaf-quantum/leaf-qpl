module Compiler.TypeChecker.InitialTypeCheckPass

import Data.List1
import Data.SortedMap

import Control.Monad.State
import Compiler.ScopeAndNameResolution.Data
import Compiler.Type
import Compiler.TypeChecker.Data
import Compiler.TypeChecker.Helper
import Compiler.TypeChecker.State
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

typecheckNode : AstInfo -> ProvenanceMetadata -> a -> TypedAstNode a
typecheckNode astInfo (MkProvenanceMetadata provenance) = typedAstNode astInfo provenance

typecheckAstNode : {a : Type} -> AstNode ResolvedAstPhase a -> AstNode TypedAstPhase a
typecheckAstNode (MkAstNode docInfo (MkProvenanceMetadata provenance) value) = typecheckNode docInfo (MkProvenanceMetadata provenance) value

typecheckName : ResolvedName -> TypedName
typecheckName (MkAstNode nameInfo (MkProvenanceMetadata provenance) (MkResolvedNameNode nameText symbolId)) =
  typecheckNode nameInfo (MkProvenanceMetadata provenance) $
    MkResolvedNameNode nameText symbolId

typecheckMemberName : AstNode ResolvedAstPhase (MemberNameFor ResolvedAstPhase) -> TypedName
typecheckMemberName = ?typecheckMemberNameH

typecheckAttribute : ResolvedAttribute -> TypedAttribute
typecheckAttribute (MkAstNode attributeInfo (MkProvenanceMetadata provenance) (MkAttributeNode name arguments)) =
  typecheckNode attributeInfo (MkProvenanceMetadata provenance) $
    MkAttributeNode
      (typecheckAstNode name)
      (map (map typecheckAstNode) arguments)

typecheckPath : ResolvedPath -> TypedPath
typecheckPath (MkAstNode pathAstInfo (MkProvenanceMetadata provenance) (MkResolvedPathNode firstSegmentText remainingSegmentTexts targetSymbolId)) =
  typecheckNode pathAstInfo (MkProvenanceMetadata provenance) $
    MkResolvedPathNode firstSegmentText remainingSegmentTexts targetSymbolId

typecheckPattern : ResolvedPattern -> TypedPattern
typecheckPattern (MkAstNode patternInfo (MkProvenanceMetadata provenance) patternNode) =
  typecheckNode patternInfo (MkProvenanceMetadata provenance) $
    case patternNode of
      PatternWildcard =>
        PatternWildcard
      PatternName mutability binderName =>
        PatternName mutability (typecheckName binderName)
      PatternPath valuePath =>
        PatternPath (typecheckPath valuePath)
      PatternLiteral literal =>
        PatternLiteral (typecheckAstNode literal)
      PatternParenthesized innerPattern =>
        unreachable {function = "typecheckPattern"} {reason = "parenthesized patterns should have been removed during desugaring"}
      PatternTuple elementPatterns =>
        PatternTuple (map recur elementPatterns)
      PatternArray elementPatterns =>
        PatternArray (map recur elementPatterns)
      PatternStruct structPath fieldPatterns =>
        PatternStruct
          (typecheckPath structPath)
          (map typecheckStructPatternField fieldPatterns)
      PatternEnumTuple variantPath argumentPatterns =>
        PatternEnumTuple
          (typecheckPath variantPath)
          (map recur argumentPatterns)
  where
    recur : ResolvedPattern -> TypedPattern
    recur pattern =
      typecheckPattern (assert_smaller patternNode pattern)

    typecheckStructPatternField : ResolvedStructPatternField -> TypedStructPatternField
    typecheckStructPatternField (MkAstNode fieldInfo (MkProvenanceMetadata provenance) fieldNode) =
      typecheckNode fieldInfo (MkProvenanceMetadata provenance) $
        case fieldNode of
          StructPatternFieldShorthand mutability fieldAndBinderName =>
            StructPatternFieldShorthand
              mutability
              (typecheckName fieldAndBinderName)
          StructPatternFieldExplicit fieldName fieldPattern =>
            StructPatternFieldExplicit
              (typecheckName fieldName)
              (recur fieldPattern)

mutual
  typecheckExpressionNode : ExpressionNode ResolvedAstPhase -> ExpressionNode TypedAstPhase
  typecheckExpressionNode expression =
    ?xxx9999
--    case expression of
--      ExprLiteral literal => ExprLiteral (typecheckAstNode literal)
--      ExprName name => ExprName (typecheckName name)
--      ExprPath path => ExprPath (typecheckPath path)
--      ExprBuiltin builtin => ExprBuiltin builtin
--      ExprSelf selfReceiver => ExprSelf selfReceiver
--      ExprParenthesized inner => unreachable {function = "typecheckExpressionNode"} {reason = "parenthesized expressions should have been removed during desugaring"}
--      ExprTuple elements => ExprTuple (map typecheckNestedExpression elements)
--      ExprArray elements => ExprArray (map typecheckNestedExpression elements)
--      ExprRepeatedArray element count => ExprRepeatedArray (typecheckNestedExpression element) (typecheckNestedExpression count)
--      ExprStructLiteral path fields => notImplemented {function = "typecheckExpressionNode"} {feature = "ExprStructLiteral"}
--      ExprCall callee arguments => ExprCall (typecheckNestedExpression callee) (map typecheckNestedExpression arguments)
--      ExprMethodCall receiver name arguments => ExprMethodCall (typecheckNestedExpression receiver) (typecheckMemberName name) (map typecheckNestedExpression arguments)
--      ExprField object name => ExprField (typecheckNestedExpression object) (typecheckMemberName name)
--      ExprTupleIndex tuple indexText => ExprTupleIndex (typecheckNestedExpression tuple) indexText
--      ExprIndex object index => ExprIndex (typecheckNestedExpression object) (typecheckNestedExpression index)
--      ExprUnary operator operand => ExprUnary (typecheckAstNode operator) (typecheckNestedExpression operand)
--      ExprBinary operator left right => ExprBinary (typecheckAstNode operator) (typecheckNestedExpression left) (typecheckNestedExpression right)
--      ExprRange start operator end => ExprRange (map typecheckNestedExpression start) (typecheckAstNode operator) (map typecheckNestedExpression end)
--      ExprCast operand target => ExprCast (typecheckNestedExpression operand) (typecheckType target)
--      ExprBlock block => ExprBlock (typecheckBlockExpression block)
--      ExprIf ifNode => ExprIf (typecheckIfNode ifNode)
--      ExprQIf ifNode => notImplemented {function = "typecheckExpressionNode"} {feature = "ExprQIf"}
--      ExprSIf ifNode => notImplemented {function = "typecheckExpressionNode"} {feature = "ExprSIf"}
--      ExprMatch matchNode => notImplemented {function = "typecheckExpressionNode"} {feature = "ExprMatch"}
--      ExprQMatch matchNode => notImplemented {function = "typecheckExpressionNode"} {feature = "ExprQMatch"}
--      ExprSMatch matchNode => notImplemented {function = "typecheckExpressionNode"} {feature = "ExprSMatch"}
--      ExprLoop body => ExprLoop (typecheckBlockExpression body)
--      ExprWhile condition body => ExprWhile (typecheckNestedExpression condition) (typecheckBlockExpression body)
--      ExprFor pattern iterator body => ExprFor (typecheckPattern pattern) (typecheckNestedExpression iterator) (typecheckBlockExpression body)
--      ExprBreak value => ExprBreak (map typecheckNestedExpression value)
--      ExprContinue => ExprContinue
--      ExprReturn value => ExprReturn (map typecheckNestedExpression value)
--      ExprCtrl control => ExprCtrl (typecheckControlExpressionNode control)
--      ExprAdjoint adjoint => ExprAdjoint (typecheckAdjointExpressionNode adjoint)
--    where
--      typecheckNestedExpression : ResolvedExpr -> TypedExpr
--      typecheckNestedExpression nestedExpression =
--        typecheckExpression (assert_smaller expression nestedExpression)
--      typecheckBlockExpression : ResolvedBlock -> TypedBlock
--      typecheckBlockExpression 
--        (MkAstNode blockAstInfo (MkProvenanceMetadata provenance) (MkBlockNode blockInnerDocs blockStatements finalExpression)) =
--        typecheckNode blockAstInfo (MkProvenanceMetadata provenance) $
--          MkBlockNode 
--            (map typecheckAstNode blockInnerDocs) 
--            (map (\statement => typecheckStatement (assert_smaller expression statement)) blockStatements) 
--            (map typecheckNestedExpression finalExpression)
--      typecheckIfNode : ClassicalIfNode ResolvedAstPhase -> ClassicalIfNode TypedAstPhase
--      typecheckIfNode ifNode@(MkClassicalIfNode ifCondition ifThenBlock ifElseBranch) =
--        MkClassicalIfNode
--          (typecheckNestedExpression ifCondition)
--          (typecheckBlockExpression ifThenBlock)
--          (map typecheckElseNode ifElseBranch)
--        where
--          typecheckElseNode : ClassicalElseNode ResolvedAstPhase -> ClassicalElseNode TypedAstPhase
--          typecheckElseNode (ElseBlock elseBlock) =
--            ElseBlock (typecheckBlockExpression elseBlock)
--          typecheckElseNode (ElseChainedIf (MkAstNode chainedIfInfo (MkProvenanceMetadata provenance) chainedIfNode)) =
--            ElseChainedIf $
--              typecheckNode chainedIfInfo (MkProvenanceMetadata provenance) $
--                typecheckIfNode (assert_smaller ifNode chainedIfNode)
--      typecheckControlExpressionNode : ControlExpressionNode ResolvedAstPhase -> ControlExpressionNode TypedAstPhase
--      typecheckControlExpressionNode (ControlledCallable controlQubits onBasisRaw controlledCallable) =
--        ControlledCallable
--          (map typecheckNestedExpression controlQubits)
--          (map typecheckAstNode onBasisRaw)
--          (typecheckNestedExpression controlledCallable)
--      typecheckControlExpressionNode (ControlledBlock controlQubits onBasisRaw controlledBlock) =
--        ControlledBlock
--          (map typecheckNestedExpression controlQubits)
--          (map typecheckAstNode onBasisRaw)
--          (typecheckBlockExpression controlledBlock)
--      typecheckAdjointExpressionNode : AdjointExpressionNode ResolvedAstPhase -> AdjointExpressionNode TypedAstPhase
--      typecheckAdjointExpressionNode (AdjointOfCallable adjointedCallable) = AdjointOfCallable (typecheckNestedExpression adjointedCallable)
--      typecheckAdjointExpressionNode (AdjointBlock adjointedBlock) = AdjointBlock (typecheckBlockExpression adjointedBlock)
--
  typecheckExpression : ResolvedExpr ->  StateT CheckerState (Either TypeError) TypedExpr
  typecheckExpression (MkAstNode expressionInfo (MkProvenanceMetadata provenance) expressionNode) =
    ?xxx88
    --typecheckNode expressionInfo (MkProvenanceMetadata provenance) (typecheckExpressionNode expressionNode)

  typecheckType : Ty ResolvedAstPhase (Expr ResolvedAstPhase) -> Ty TypedAstPhase (Expr TypedAstPhase)
  typecheckType (MkAstNode tyAstInfo (MkProvenanceMetadata provenance) typeNode) =
    ?xxx0002
--    typecheckNode tyAstInfo (MkProvenanceMetadata provenance) $
--      case typeNode of
--        TyPrimitive primitiveName =>
--          TyPrimitive primitiveName
--        TyPath typePath =>
--          TyPath (typecheckPath typePath)
--        TyUnit =>
--          TyUnit
--        TyParenthesized innerType =>
--          unreachable {function = "typecheckType"} {reason = "parenthesized types should have been removed during desugaring"}
--        TyTuple elementTypes =>
--          TyTuple (map typecheckNestedType elementTypes)
--        TyArray elementType sizeExpression =>
--          TyArray 
--            (typecheckNestedType elementType) 
--            (typecheckExpression sizeExpression)
--        TySlice elementType =>
--          TySlice (typecheckNestedType elementType)
--        TyReference borrowKind referencedType =>
--          TyReference 
--            (typecheckAstNode borrowKind) 
--            (typecheckNestedType referencedType)
--        TyQualified ownershipQualifier qualifiedType =>
--          TyQualified (typecheckAstNode ownershipQualifier) (typecheckNestedType qualifiedType)
--        TyFunction functionEffect functionParameters returnType =>
--          TyFunction
--            (map typecheckAstNode functionEffect)
--            (map typecheckParameter functionParameters)
--            (map typecheckNestedType returnType)
--      where
--        typecheckNestedType : ResolvedTy -> TypedTy
--        typecheckNestedType nestedType =
--          typecheckType (assert_smaller typeNode nestedType)
--        typecheckParameter : ResolvedAstNode (FunctionTypeParameterNode ResolvedAstPhase (ResolvedAstNode (ExpressionNode ResolvedAstPhase))) ->
--          TypedAstNode (FunctionTypeParameterNode TypedAstPhase (TypedAstNode (ExpressionNode TypedAstPhase)))
--        typecheckParameter (MkAstNode parameterAstInfo (MkProvenanceMetadata provenance) (MkFunctionTypeParameterNode parameterName parameterType)) =
--          typecheckNode parameterAstInfo (MkProvenanceMetadata provenance) $
--            -- Not typecheckName: a function-type parameter name is never a
--            -- symbol (see the comment on FunctionTypeParameterNode in
--            -- Syntax/Type.idr), so only its AstNode wrapping is updated.
--            MkFunctionTypeParameterNode (typecheckAstNode parameterName) (typecheckNestedType parameterType)
--
  typecheckFunctionParameter: AstNode ResolvedAstPhase (FunctionParameterNode ResolvedAstPhase) -> AstNode TypedAstPhase (FunctionParameterNode TypedAstPhase)
  typecheckFunctionParameter (MkAstNode parameterInfo (MkProvenanceMetadata provenance) (NormalParameter parameterDocs parameterMutability parameterName parameterType)) =
    typecheckNode parameterInfo (MkProvenanceMetadata provenance) $
      NormalParameter
        (map typecheckAstNode parameterDocs)
        (map typecheckAstNode parameterMutability)
        (typecheckName parameterName)
        (typecheckType parameterType)
  typecheckFunctionParameter (MkAstNode parameterInfo (MkProvenanceMetadata provenance) (ReceiverParameter receiverDocs receiverBorrow)) =
    typecheckNode parameterInfo (MkProvenanceMetadata provenance) $
      ReceiverParameter
        (map typecheckAstNode receiverDocs)
        (map typecheckAstNode receiverBorrow)

  typecheckSignedPauliTerm : SignedPauliTerm ResolvedAstPhase -> SignedPauliTerm TypedAstPhase
  typecheckSignedPauliTerm (MkAstNode termInfo (MkProvenanceMetadata provenance) (MkSignedPauliTermNode sign pauliString)) =
    typecheckNode termInfo (MkProvenanceMetadata provenance) $
      MkSignedPauliTermNode sign (typecheckAstNode pauliString)

  typecheckContractPredicate : ResolvedContractPredicate -> TypedContractPredicate
  typecheckContractPredicate (MkAstNode predicateInfo (MkProvenanceMetadata provenance) predicateNode) =
    ?xxx22
    --typecheckNode predicateInfo (MkProvenanceMetadata provenance) $
    --  case predicateNode of
    --    ContractClean qubitArgument =>
    --      ContractClean (typecheckExpression qubitArgument)
    --    ContractBasis qubitArgument pauliString =>
    --      ContractBasis
    --        (typecheckExpression qubitArgument)
    --        (typecheckAstNode pauliString)
    --    ContractSeparable qubitArgument =>
    --      ContractSeparable (typecheckExpression qubitArgument)
    --    ContractIsolated qubitArgument =>
    --      ContractIsolated (typecheckExpression qubitArgument)
    --    ContractProduct firstQubitSet otherQubitSets =>
    --      ContractProduct
    --        (typecheckExpression firstQubitSet)
    --        (map typecheckExpression otherQubitSets)
    --    ContractStabilized qubitArgument stabilizerTerms =>
    --      ContractStabilized
    --        (typecheckExpression qubitArgument)
    --        (map typecheckSignedPauliTerm stabilizerTerms)

  typecheckContractClause : ContractClause ResolvedAstPhase (Expr ResolvedAstPhase) -> ContractClause TypedAstPhase (Expr TypedAstPhase)  
  typecheckContractClause (MkAstNode contractAstInfo (MkProvenanceMetadata provenance) contractClauseNode) =
    ?typecheckContractClauseHole
  --  typecheckNode contractAstInfo (MkProvenanceMetadata provenance) $
  --    case contractClauseNode of
  --         l
  --      RequiresClause predicate => RequiresClause (typecheckContractPredicate predicate)
  --      EnsuresClause predicate => EnsuresClause (typecheckContractPredicate predicate)

  --typecheckLetInitializer : LetInitializerNode ResolvedAstPhase -> LetInitializerNode TypedAstPhase
  --typecheckLetInitializer (MkLetInitializerNode marker value) =
  --  MkLetInitializerNode (typecheckAstNode marker) (typecheckExpression value)

  typecheckAssignmentTarget : ResolvedAstNode (AssignmentTargetNode ResolvedAstPhase) -> TypedAstNode (AssignmentTargetNode TypedAstPhase)
  typecheckAssignmentTarget (MkAstNode assignmentTargetAstInfo (MkProvenanceMetadata provenance) assignmentTargetNode) =
    ?typecheckAssignmentTargetHole
  --  typecheckNode assignmentTargetAstInfo (MkProvenanceMetadata provenance) $
  --    case assignmentTargetNode of
  --      AssignTargetName targetName =>
  --        AssignTargetName (typecheckName targetName)
  --      AssignTargetIndex targetObject indexExpression =>
  --        AssignTargetIndex
  --          (typecheckExpression targetObject)
  --          (typecheckExpression indexExpression)
  --      AssignTargetField targetObject fieldName =>
  --        AssignTargetField
  --          (typecheckExpression targetObject)
  --          (typecheckMemberName fieldName)
  --      AssignTargetTupleIndex targetObject tupleIndexRawText =>
  --        AssignTargetTupleIndex
  --          (typecheckExpression targetObject)
  --          tupleIndexRawText

  typecheckStatement : Statement ResolvedAstPhase -> Statement TypedAstPhase
  typecheckStatement (MkAstNode statementAstInfo (MkProvenanceMetadata provenance) statementNode) = ?typeCheckStatementHole
  --typecheckNode statementAstInfo (MkProvenanceMetadata provenance) $
  --    case statementNode of
  --      StatementLet (MkLetBindingNode qualifiers pattern typeAnnotation initializer) =>
  --        StatementLet $
  --          MkLetBindingNode
  --            (map typecheckAstNode qualifiers)
  --            (typecheckPattern pattern)
  --            (map (\ty => typecheckType (assert_smaller statementNode ty)) typeAnnotation)
  --            (map (\init => typecheckLetInitializer (assert_smaller statementNode init)) initializer)
  --      StatementAssignment (MkAssignmentNode assignmentTarget assignmentOperator assignmentValue) =>
  --        StatementAssignment $
  --          MkAssignmentNode
  --            (typecheckAssignmentTarget assignmentTarget)
  --            (typecheckAstNode assignmentOperator)
  --            (typecheckExpression assignmentValue)
  --      StatementSemiExpression statementExpression =>
  --        StatementSemiExpression (typecheckExpression statementExpression)
  --      StatementExpression statementExpression =>
  --        StatementExpression (typecheckExpression statementExpression)
 
typecheckFunctionBody : Block ResolvedAstPhase -> Block TypedAstPhase
typecheckFunctionBody (MkAstNode functionBodyAstInfo (MkProvenanceMetadata provenance) (MkBlockNode blockInnerDocs blockStatements finalExpression)) =
  ?typecheckFunctionBodyHole
  --typecheckNode functionBodyAstInfo (MkProvenanceMetadata provenance) $
  --  MkBlockNode
  --    (map typecheckAstNode blockInnerDocs)
  --    (map typecheckStatement blockStatements)
  --    (map typecheckExpression finalExpression)

typecheckItem : ResolvedItem -> StateT CheckerState (Either TypeError) TypedItem
typecheckItem (MkAstNode itemInfo metadata item) = do
  resolvedItem <- case item of
      ItemModule declaration => notImplemented {function = "typecheckItem"} {feature = "ItemModule"}
      ItemUse declaration => notImplemented {function = "typecheckItem"} {feature = "ItemUse"}
      ItemConst declaration => do
        typedDeclaration <- typecheckConstDeclaration declaration
        pure $ ItemConst typedDeclaration
      ItemEnum declaration => notImplemented {function = "typecheckItem"} {feature = "ItemEnum"}
      ItemQEnum declaration => notImplemented {function = "typecheckItem"} {feature = "ItemQEnum"}
      ItemStruct declaration => notImplemented {function = "typecheckItem"} {feature = "ItemStruct"}
      ItemImpl declaration => notImplemented {function = "typecheckItem"} {feature = "ItemImpl"}
      ItemFunction declaration => do
        typedDeclaration <- typecheckFunctionDeclaration declaration
        pure $ ItemFunction typedDeclaration
  pure $ typecheckNode itemInfo metadata resolvedItem
  where
    typecheckConstDeclaration : ConstDeclarationNode ResolvedAstPhase ->  StateT CheckerState (Either TypeError) (ConstDeclarationNode TypedAstPhase)
    typecheckConstDeclaration (MkConstDeclarationNode constDocs constVisibility constName constType constValue) = do
      ?xxxxxxxxxxxxxxxxxx1
      -- MkConstDeclarationNode
      --   (map typecheckAstNode constDocs)
      --   (map typecheckAstNode constVisibility)
      --   (typecheckName constName)
      --   (typecheckType constType)
      --   typedConstValue

    typecheckFunctionDeclaration : FunctionDeclarationNode ResolvedAstPhase -> StateT CheckerState (Either TypeError) (FunctionDeclarationNode TypedAstPhase)
    typecheckFunctionDeclaration
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
        ) = ?xxxxxxxxxxxxxxxxxx2
            --MkFunctionDeclarationNode
            --  (map typecheckAstNode functionDocs)
            --  (map typecheckAttribute functionAttributes)
            --  (map typecheckAstNode functionVisibility)
            --  (map typecheckAstNode functionConstness)
            --  (map typecheckAstNode functionEffect)
            --  (typecheckName functionName)
            --  (map typecheckFunctionParameter functionParameters)
            --  (map typecheckType returnType)
            --  (map typecheckAstNode supportClause)
            --  (map typecheckContractClause contractClauses)
            --  (typecheckFunctionBody functionBody)

export
initialTypeCheckPass : ResolvedModule -> Either TypeError TypeTables
initialTypeCheckPass (
  MkResolvedModule
    _                                                     -- rootModule
    _                                                     -- rootScope
    (MkAstNode _ _ (MkSourceFileNode _ items))            -- astInfo, metadata, sourceFileInnerDocs
    (MkScopeTables
      _                                                   -- resolver traversal state is not carried over:
      _                                                   -- currentScope, currentScopeKind,
      _                                                   -- currentModule, constContextBoundary
      _
      nodeScopes
      symbols
      localVariables
      references
      scopes
      memberScopes)
  ) = do
    let initialTypeTables = MkTypeTables
          scopes
          nodeScopes
          (map (\symbol => { symbolType :=  TypeNotYetResolved } symbol) symbols)
          localVariables
          memberScopes
          references
          empty
          empty
          empty
          empty
          empty
    let initialCheckerState = MkCheckerState initialTypeTables Nothing emptyInferenceState
    (checkerState, _) <- runStateT initialCheckerState $ do
      traverse_ typecheckItem items
    pure checkerState.tables

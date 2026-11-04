module Compiler.TypeChecker.Phases.SignatureCheck

import Data.List1
import Data.SortedMap

import Control.Monad.State
import Compiler.ScopeAndNameResolution.Data
import Compiler.TypeChecker.Data
import Compiler.TypeChecker.Helper
import Compiler.TypeChecker.State
import Compiler.TypeChecker.Type
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

checkNode : AstInfo -> ProvenanceMetadata -> a -> TypedAstNode a
checkNode astInfo (MkProvenanceMetadata provenance) = typedAstNode astInfo provenance

checkAstNode : {a : Type} -> AstNode ResolvedAstPhase a -> AstNode TypedAstPhase a
checkAstNode (MkAstNode docInfo (MkProvenanceMetadata provenance) value) = checkNode docInfo (MkProvenanceMetadata provenance) value

checkName : ResolvedName -> TypedName
checkName (MkAstNode nameInfo (MkProvenanceMetadata provenance) (MkResolvedNameNode nameText symbolId)) =
  checkNode nameInfo (MkProvenanceMetadata provenance) $
    MkResolvedNameNode nameText symbolId

checkMemberName : AstNode ResolvedAstPhase (MemberNameFor ResolvedAstPhase) -> TypedName
checkMemberName = ?checkMemberNameH

checkAttribute : ResolvedAttribute -> TypedAttribute
checkAttribute (MkAstNode attributeInfo (MkProvenanceMetadata provenance) (MkAttributeNode name arguments)) =
  checkNode attributeInfo (MkProvenanceMetadata provenance) $
    MkAttributeNode
      (checkAstNode name)
      (map (map checkAstNode) arguments)

checkPath : ResolvedPath -> TypedPath
checkPath (MkAstNode pathAstInfo (MkProvenanceMetadata provenance) (MkResolvedPathNode firstSegmentText remainingSegmentTexts targetSymbolId)) =
  checkNode pathAstInfo (MkProvenanceMetadata provenance) $
    MkResolvedPathNode firstSegmentText remainingSegmentTexts targetSymbolId

checkPattern : ResolvedPattern -> TypedPattern
checkPattern (MkAstNode patternInfo (MkProvenanceMetadata provenance) patternNode) =
  checkNode patternInfo (MkProvenanceMetadata provenance) $
    case patternNode of
      PatternWildcard =>
        PatternWildcard
      PatternName mutability binderName =>
        PatternName mutability (checkName binderName)
      PatternPath valuePath =>
        PatternPath (checkPath valuePath)
      PatternLiteral literal =>
        PatternLiteral (checkAstNode literal)
      PatternParenthesized innerPattern =>
        unreachable {function = "checkPattern"} {reason = "parenthesized patterns should have been removed during desugaring"}
      PatternTuple elementPatterns =>
        PatternTuple (map recur elementPatterns)
      PatternArray elementPatterns =>
        PatternArray (map recur elementPatterns)
      PatternStruct structPath fieldPatterns =>
        PatternStruct
          (checkPath structPath)
          (map checkStructPatternField fieldPatterns)
      PatternEnumTuple variantPath argumentPatterns =>
        PatternEnumTuple
          (checkPath variantPath)
          (map recur argumentPatterns)
  where
    recur : ResolvedPattern -> TypedPattern
    recur pattern =
      checkPattern (assert_smaller patternNode pattern)

    checkStructPatternField : ResolvedStructPatternField -> TypedStructPatternField
    checkStructPatternField (MkAstNode fieldInfo (MkProvenanceMetadata provenance) fieldNode) =
      checkNode fieldInfo (MkProvenanceMetadata provenance) $
        case fieldNode of
          StructPatternFieldShorthand mutability fieldAndBinderName =>
            StructPatternFieldShorthand
              mutability
              (checkName fieldAndBinderName)
          StructPatternFieldExplicit fieldName fieldPattern =>
            StructPatternFieldExplicit
              (checkName fieldName)
              (recur fieldPattern)

mutual
  checkExpressionNode : ExpressionNode ResolvedAstPhase -> ExpressionNode TypedAstPhase
  checkExpressionNode expression =
    ?xxx9999
--    case expression of
--      ExprLiteral literal => ExprLiteral (checkAstNode literal)
--      ExprName name => ExprName (checkName name)
--      ExprPath path => ExprPath (checkPath path)
--      ExprBuiltin builtin => ExprBuiltin builtin
--      ExprSelf selfReceiver => ExprSelf selfReceiver
--      ExprParenthesized inner => unreachable {function = "checkExpressionNode"} {reason = "parenthesized expressions should have been removed during desugaring"}
--      ExprTuple elements => ExprTuple (map checkNestedExpression elements)
--      ExprArray elements => ExprArray (map checkNestedExpression elements)
--      ExprRepeatedArray element count => ExprRepeatedArray (checkNestedExpression element) (checkNestedExpression count)
--      ExprStructLiteral path fields => notImplemented {function = "checkExpressionNode"} {feature = "ExprStructLiteral"}
--      ExprCall callee arguments => ExprCall (checkNestedExpression callee) (map checkNestedExpression arguments)
--      ExprMethodCall receiver name arguments => ExprMethodCall (checkNestedExpression receiver) (checkMemberName name) (map checkNestedExpression arguments)
--      ExprField object name => ExprField (checkNestedExpression object) (checkMemberName name)
--      ExprTupleIndex tuple indexText => ExprTupleIndex (checkNestedExpression tuple) indexText
--      ExprIndex object index => ExprIndex (checkNestedExpression object) (checkNestedExpression index)
--      ExprUnary operator operand => ExprUnary (checkAstNode operator) (checkNestedExpression operand)
--      ExprBinary operator left right => ExprBinary (checkAstNode operator) (checkNestedExpression left) (checkNestedExpression right)
--      ExprRange start operator end => ExprRange (map checkNestedExpression start) (checkAstNode operator) (map checkNestedExpression end)
--      ExprCast operand target => ExprCast (checkNestedExpression operand) (checkType target)
--      ExprBlock block => ExprBlock (checkBlockExpression block)
--      ExprIf ifNode => ExprIf (checkIfNode ifNode)
--      ExprQIf ifNode => notImplemented {function = "checkExpressionNode"} {feature = "ExprQIf"}
--      ExprSIf ifNode => notImplemented {function = "checkExpressionNode"} {feature = "ExprSIf"}
--      ExprMatch matchNode => notImplemented {function = "checkExpressionNode"} {feature = "ExprMatch"}
--      ExprQMatch matchNode => notImplemented {function = "checkExpressionNode"} {feature = "ExprQMatch"}
--      ExprSMatch matchNode => notImplemented {function = "checkExpressionNode"} {feature = "ExprSMatch"}
--      ExprLoop body => ExprLoop (checkBlockExpression body)
--      ExprWhile condition body => ExprWhile (checkNestedExpression condition) (checkBlockExpression body)
--      ExprFor pattern iterator body => ExprFor (checkPattern pattern) (checkNestedExpression iterator) (checkBlockExpression body)
--      ExprBreak value => ExprBreak (map checkNestedExpression value)
--      ExprContinue => ExprContinue
--      ExprReturn value => ExprReturn (map checkNestedExpression value)
--      ExprCtrl control => ExprCtrl (checkControlExpressionNode control)
--      ExprAdjoint adjoint => ExprAdjoint (checkAdjointExpressionNode adjoint)
--    where
--      checkNestedExpression : ResolvedExpr -> TypedExpr
--      checkNestedExpression nestedExpression =
--        checkExpression (assert_smaller expression nestedExpression)
--      checkBlockExpression : ResolvedBlock -> TypedBlock
--      checkBlockExpression 
--        (MkAstNode blockAstInfo (MkProvenanceMetadata provenance) (MkBlockNode blockInnerDocs blockStatements finalExpression)) =
--        checkNode blockAstInfo (MkProvenanceMetadata provenance) $
--          MkBlockNode 
--            (map checkAstNode blockInnerDocs) 
--            (map (\statement => checkStatement (assert_smaller expression statement)) blockStatements) 
--            (map checkNestedExpression finalExpression)
--      checkIfNode : ClassicalIfNode ResolvedAstPhase -> ClassicalIfNode TypedAstPhase
--      checkIfNode ifNode@(MkClassicalIfNode ifCondition ifThenBlock ifElseBranch) =
--        MkClassicalIfNode
--          (checkNestedExpression ifCondition)
--          (checkBlockExpression ifThenBlock)
--          (map checkElseNode ifElseBranch)
--        where
--          checkElseNode : ClassicalElseNode ResolvedAstPhase -> ClassicalElseNode TypedAstPhase
--          checkElseNode (ElseBlock elseBlock) =
--            ElseBlock (checkBlockExpression elseBlock)
--          checkElseNode (ElseChainedIf (MkAstNode chainedIfInfo (MkProvenanceMetadata provenance) chainedIfNode)) =
--            ElseChainedIf $
--              checkNode chainedIfInfo (MkProvenanceMetadata provenance) $
--                checkIfNode (assert_smaller ifNode chainedIfNode)
--      checkControlExpressionNode : ControlExpressionNode ResolvedAstPhase -> ControlExpressionNode TypedAstPhase
--      checkControlExpressionNode (ControlledCallable controlQbits onBasisRaw controlledCallable) =
--        ControlledCallable
--          (map checkNestedExpression controlQbits)
--          (map checkAstNode onBasisRaw)
--          (checkNestedExpression controlledCallable)
--      checkControlExpressionNode (ControlledBlock controlQbits onBasisRaw controlledBlock) =
--        ControlledBlock
--          (map checkNestedExpression controlQbits)
--          (map checkAstNode onBasisRaw)
--          (checkBlockExpression controlledBlock)
--      checkAdjointExpressionNode : AdjointExpressionNode ResolvedAstPhase -> AdjointExpressionNode TypedAstPhase
--      checkAdjointExpressionNode (AdjointOfCallable adjointedCallable) = AdjointOfCallable (checkNestedExpression adjointedCallable)
--      checkAdjointExpressionNode (AdjointBlock adjointedBlock) = AdjointBlock (checkBlockExpression adjointedBlock)
--
  checkExpression : ResolvedExpr ->  StateT TypeCheckerState (Either TypeError) TypedExpr
  checkExpression (MkAstNode expressionInfo (MkProvenanceMetadata provenance) expressionNode) =
    ?xxx88
    --checkNode expressionInfo (MkProvenanceMetadata provenance) (checkExpressionNode expressionNode)

  checkType : Ty ResolvedAstPhase (Expr ResolvedAstPhase) -> Ty TypedAstPhase (Expr TypedAstPhase)
  checkType (MkAstNode tyAstInfo (MkProvenanceMetadata provenance) typeNode) =
    ?xxx0002
--    checkNode tyAstInfo (MkProvenanceMetadata provenance) $
--      case typeNode of
--        TyPrimitive primitiveName =>
--          TyPrimitive primitiveName
--        TyPath typePath =>
--          TyPath (checkPath typePath)
--        TyUnit =>
--          TyUnit
--        TyParenthesized innerType =>
--          unreachable {function = "checkType"} {reason = "parenthesized types should have been removed during desugaring"}
--        TyTuple elementTypes =>
--          TyTuple (map checkNestedType elementTypes)
--        TyArray elementType sizeExpression =>
--          TyArray 
--            (checkNestedType elementType) 
--            (checkExpression sizeExpression)
--        TySlice elementType =>
--          TySlice (checkNestedType elementType)
--        TyReference borrowKind referencedType =>
--          TyReference 
--            (checkAstNode borrowKind) 
--            (checkNestedType referencedType)
--        TyQualified ownershipQualifier qualifiedType =>
--          TyQualified (checkAstNode ownershipQualifier) (checkNestedType qualifiedType)
--        TyFunction functionEffect functionParameters returnType =>
--          TyFunction
--            (map checkAstNode functionEffect)
--            (map checkParameter functionParameters)
--            (map checkNestedType returnType)
--      where
--        checkNestedType : ResolvedTy -> TypedTy
--        checkNestedType nestedType =
--          checkType (assert_smaller typeNode nestedType)
--        checkParameter : ResolvedAstNode (FunctionTypeParameterNode ResolvedAstPhase (ResolvedAstNode (ExpressionNode ResolvedAstPhase))) ->
--          TypedAstNode (FunctionTypeParameterNode TypedAstPhase (TypedAstNode (ExpressionNode TypedAstPhase)))
--        checkParameter (MkAstNode parameterAstInfo (MkProvenanceMetadata provenance) (MkFunctionTypeParameterNode parameterName parameterType)) =
--          checkNode parameterAstInfo (MkProvenanceMetadata provenance) $
--            -- Not checkName: a function-type parameter name is never a
--            -- symbol (see the comment on FunctionTypeParameterNode in
--            -- Syntax/Type.idr), so only its AstNode wrapping is updated.
--            MkFunctionTypeParameterNode (checkAstNode parameterName) (checkNestedType parameterType)
--
  checkFunctionParameter: AstNode ResolvedAstPhase (FunctionParameterNode ResolvedAstPhase) -> AstNode TypedAstPhase (FunctionParameterNode TypedAstPhase)
  checkFunctionParameter (MkAstNode parameterInfo (MkProvenanceMetadata provenance) (NormalParameter parameterDocs parameterMutability parameterName parameterType)) =
    checkNode parameterInfo (MkProvenanceMetadata provenance) $
      NormalParameter
        (map checkAstNode parameterDocs)
        (map checkAstNode parameterMutability)
        (checkName parameterName)
        (checkType parameterType)
  checkFunctionParameter (MkAstNode parameterInfo (MkProvenanceMetadata provenance) (ReceiverParameter receiverDocs receiverBorrow)) =
    checkNode parameterInfo (MkProvenanceMetadata provenance) $
      ReceiverParameter
        (map checkAstNode receiverDocs)
        (map checkAstNode receiverBorrow)

  checkSignedPauliTerm : SignedPauliTerm ResolvedAstPhase -> SignedPauliTerm TypedAstPhase
  checkSignedPauliTerm (MkAstNode termInfo (MkProvenanceMetadata provenance) (MkSignedPauliTermNode sign pauliString)) =
    checkNode termInfo (MkProvenanceMetadata provenance) $
      MkSignedPauliTermNode sign (checkAstNode pauliString)

  checkContractPredicate : ResolvedContractPredicate -> TypedContractPredicate
  checkContractPredicate (MkAstNode predicateInfo (MkProvenanceMetadata provenance) predicateNode) =
    ?xxx22
    --checkNode predicateInfo (MkProvenanceMetadata provenance) $
    --  case predicateNode of
    --    ContractClean qbitArgument =>
    --      ContractClean (checkExpression qbitArgument)
    --    ContractBasis qbitArgument pauliString =>
    --      ContractBasis
    --        (checkExpression qbitArgument)
    --        (checkAstNode pauliString)
    --    ContractSeparable qbitArgument =>
    --      ContractSeparable (checkExpression qbitArgument)
    --    ContractIsolated qbitArgument =>
    --      ContractIsolated (checkExpression qbitArgument)
    --    ContractProduct firstQbitSet otherQbitSets =>
    --      ContractProduct
    --        (checkExpression firstQbitSet)
    --        (map checkExpression otherQbitSets)
    --    ContractStabilized qbitArgument stabilizerTerms =>
    --      ContractStabilized
    --        (checkExpression qbitArgument)
    --        (map checkSignedPauliTerm stabilizerTerms)

  checkContractClause : ContractClause ResolvedAstPhase (Expr ResolvedAstPhase) -> ContractClause TypedAstPhase (Expr TypedAstPhase)  
  checkContractClause (MkAstNode contractAstInfo (MkProvenanceMetadata provenance) contractClauseNode) =
    ?checkContractClauseHole
  --  checkNode contractAstInfo (MkProvenanceMetadata provenance) $
  --    case contractClauseNode of
  --         l
  --      RequiresClause predicate => RequiresClause (checkContractPredicate predicate)
  --      EnsuresClause predicate => EnsuresClause (checkContractPredicate predicate)

  --checkLetInitializer : LetInitializerNode ResolvedAstPhase -> LetInitializerNode TypedAstPhase
  --checkLetInitializer (MkLetInitializerNode marker value) =
  --  MkLetInitializerNode (checkAstNode marker) (checkExpression value)

  checkAssignmentTarget : ResolvedAstNode (AssignmentTargetNode ResolvedAstPhase) -> TypedAstNode (AssignmentTargetNode TypedAstPhase)
  checkAssignmentTarget (MkAstNode assignmentTargetAstInfo (MkProvenanceMetadata provenance) assignmentTargetNode) =
    ?checkAssignmentTargetHole
  --  checkNode assignmentTargetAstInfo (MkProvenanceMetadata provenance) $
  --    case assignmentTargetNode of
  --      AssignTargetName targetName =>
  --        AssignTargetName (checkName targetName)
  --      AssignTargetIndex targetObject indexExpression =>
  --        AssignTargetIndex
  --          (checkExpression targetObject)
  --          (checkExpression indexExpression)
  --      AssignTargetField targetObject fieldName =>
  --        AssignTargetField
  --          (checkExpression targetObject)
  --          (checkMemberName fieldName)
  --      AssignTargetTupleIndex targetObject tupleIndexRawText =>
  --        AssignTargetTupleIndex
  --          (checkExpression targetObject)
  --          tupleIndexRawText

  checkStatement : Statement ResolvedAstPhase -> Statement TypedAstPhase
  checkStatement (MkAstNode statementAstInfo (MkProvenanceMetadata provenance) statementNode) = ?typeCheckStatementHole
  --checkNode statementAstInfo (MkProvenanceMetadata provenance) $
  --    case statementNode of
  --      StatementLet (MkLetBindingNode qualifiers pattern typeAnnotation initializer) =>
  --        StatementLet $
  --          MkLetBindingNode
  --            (map checkAstNode qualifiers)
  --            (checkPattern pattern)
  --            (map (\ty => checkType (assert_smaller statementNode ty)) typeAnnotation)
  --            (map (\init => checkLetInitializer (assert_smaller statementNode init)) initializer)
  --      StatementAssignment (MkAssignmentNode assignmentTarget assignmentOperator assignmentValue) =>
  --        StatementAssignment $
  --          MkAssignmentNode
  --            (checkAssignmentTarget assignmentTarget)
  --            (checkAstNode assignmentOperator)
  --            (checkExpression assignmentValue)
  --      StatementSemiExpression statementExpression =>
  --        StatementSemiExpression (checkExpression statementExpression)
  --      StatementExpression statementExpression =>
  --        StatementExpression (checkExpression statementExpression)
 
checkFunctionBody : Block ResolvedAstPhase -> Block TypedAstPhase
checkFunctionBody (MkAstNode functionBodyAstInfo (MkProvenanceMetadata provenance) (MkBlockNode blockInnerDocs blockStatements finalExpression)) =
  ?checkFunctionBodyHole
  --checkNode functionBodyAstInfo (MkProvenanceMetadata provenance) $
  --  MkBlockNode
  --    (map checkAstNode blockInnerDocs)
  --    (map checkStatement blockStatements)
  --    (map checkExpression finalExpression)

checkFunctionDeclaration : FunctionDeclarationNode ResolvedAstPhase -> StateT TypeCheckerState (Either CheckFailure) ()
checkFunctionDeclaration
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
        --  (map checkAstNode functionDocs)
        --  (map checkAttribute functionAttributes)
        --  (map checkAstNode functionVisibility)
        --  (map checkAstNode functionConstness)
        --  (map checkAstNode functionEffect)
        --  (checkName functionName)
        --  (map checkFunctionParameter functionParameters)
        --  (map checkType returnType)
        --  (map checkAstNode supportClause)
        --  (map checkContractClause contractClauses)
        --  (checkFunctionBody functionBody)

checkConstDeclaration : ConstDeclarationNode ResolvedAstPhase ->  StateT TypeCheckerState (Either CheckFailure) ()
checkConstDeclaration (MkConstDeclarationNode constDocs constVisibility constName constType constValue) = do
  typeCheckerState <- get
  inferredLeafType <- case toInferredType constType of
    TypeNotYetResolved => assert_total idris_crash "Ups"
    ResolvedType leafType => pure leafType
    NoValueType => lift $ Left $ Failed (CannotInferType ?constTypesourceSpan)
  modify $ \typeCheckerState =>
    {
      tables.symbols := update ?symbolid (?SymbolInfo inferredLeafType) typeCheckerState.tables.symbols,
      tables.expressionTypes := insert ?nodeid inferredLeafType typeCheckerState.tables.expressionTypes
    } typeCheckerState
  ?xxx

export
checkSignature : ResolvedItem -> StateT TypeCheckerState (Either CheckFailure) ()
checkSignature (MkAstNode itemInfo metadata item) = do
  case item of
      ItemModule declaration => notImplemented {function = "checkItem"} {feature = "ItemModule"}
      ItemUse declaration => notImplemented {function = "checkItem"} {feature = "ItemUse"}
      ItemConst declaration => checkConstDeclaration declaration
      ItemEnum declaration => notImplemented {function = "checkItem"} {feature = "ItemEnum"}
      ItemQEnum declaration => notImplemented {function = "checkItem"} {feature = "ItemQEnum"}
      ItemStruct declaration => notImplemented {function = "checkItem"} {feature = "ItemStruct"}
      ItemImpl declaration => notImplemented {function = "checkItem"} {feature = "ItemImpl"}
      ItemFunction declaration => checkFunctionDeclaration declaration


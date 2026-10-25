module Compiler.Desugar.Desugar

import Compiler.Desugar.Helper
import Data.List
import Data.List1
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

--- TODO deusgar bit conditions in typechecked one we know b is not a boolean
-- if b { fun(&q); } -> if b == 1 { fun(&q); }

%default total

desugarAstNode : {a : Type} -> AstNode SurfaceAstPhase a -> AstNode CanonicalAstPhase a
desugarAstNode (MkAstNode docInfo metadata value) = canonicalAstNode docInfo WrittenCode value

||| If the attribute is missing argument(s), the name of the function is set as attrribute argument.
||| Unsupported attributes names are ignored, meaning no desugaring is performed for those.
desugarAttribute : String -> Nat -> SurfaceAttribute -> (CanonicalAttribute, Nat)
desugarAttribute defaultArgName nextId (MkAstNode attributeInfo metadata (MkAttributeNode name arguments)) =
  let (desugaredArguments, followingId) = desugarArguments arguments
      attribute = canonicalAstNode attributeInfo WrittenCode $
        MkAttributeNode
          (desugarAstNode name)
          desugaredArguments
  in (attribute, followingId)
  where
    argInfo : AstInfo
    argInfo = incrementedAstInfo attributeInfo nextId
    defaultArg : Maybe (List (AttributeArgument CanonicalAstPhase))
    defaultArg = Just [canonicalAstNode argInfo DesugaredDefaultAttributeArgument (AttributeArgumentStringLit ("\"" ++ defaultArgName ++ "\""))]
    desugarArguments : Maybe (List(AttributeArgument SurfaceAstPhase)) -> (Maybe (List (AttributeArgument CanonicalAstPhase)), Nat)
    desugarArguments (Just args) = (Just ((map desugarAstNode) args), nextId)
    desugarArguments Nothing =
      case recognizeKnownAttribute name.value.nameNodeText of
        Just KnownQasmGate => (defaultArg, S nextId)
        Just KnownQasmDef  => (defaultArg, S nextId)
        Nothing            => (Nothing, nextId)

desugarPath : SurfacePath -> CanonicalPath
desugarPath (MkAstNode pathAstInfo metadata (MkPathNode firstSegment remainingSegments)) =
  canonicalAstNode pathAstInfo WrittenCode $
    MkPathNode (desugarAstNode firstSegment) (map desugarAstNode remainingSegments)

-- Perenthesized patterns will be removed
desugarPattern : SurfacePattern -> CanonicalPattern
desugarPattern (MkAstNode patternInfo _ patternNode) =
  canonicalAstNode patternInfo WrittenCode $
    case patternNode of
      PatternWildcard =>
        PatternWildcard
      PatternName mutability binderName =>
        PatternName mutability (desugarAstNode binderName)
      PatternPath valuePath =>
        PatternPath (desugarPath valuePath)
      PatternLiteral literal =>
        PatternLiteral (desugarAstNode literal)
      PatternParenthesized innerPattern =>
        (recur innerPattern).value
      PatternTuple elementPatterns =>
        PatternTuple (map recur elementPatterns)
      PatternArray elementPatterns =>
        PatternArray (map recur elementPatterns)
      PatternStruct structPath fieldPatterns =>
        PatternStruct
          (desugarPath structPath)
          (map desugarStructPatternField fieldPatterns)
      PatternEnumTuple variantPath argumentPatterns =>
        PatternEnumTuple
          (desugarPath variantPath)
          (map recur argumentPatterns)
  where
    recur : SurfacePattern -> CanonicalPattern
    recur pattern =
      desugarPattern (assert_smaller patternNode pattern)

    desugarStructPatternField : SurfaceStructPatternField -> CanonicalStructPatternField
    desugarStructPatternField (MkAstNode fieldInfo _ fieldNode) =
      canonicalAstNode fieldInfo WrittenCode $
        case fieldNode of
          -- { x } becomes { x: x }, and { mut x } becomes { x: mut x }.
          -- The field refers to a member, while the pattern introduces a local
          -- binding: they must be separate name nodes before name resolution.
          -- TODO: add tests one parser supports structs
          StructPatternFieldShorthand mutability (MkAstNode nameInfo _ name) =>
            StructPatternFieldExplicit
              (canonicalAstNode nameInfo WrittenCode name)
              (canonicalAstNode
                (MkAstInfo (incrementedAstInfo nameInfo 2).nodeId fieldInfo.span)
                DesugaredFieldShorthand $
                PatternName mutability $
                  canonicalAstNode (incrementedAstInfo nameInfo 1) DesugaredFieldShorthand name)
          StructPatternFieldExplicit fieldName fieldPattern =>
            StructPatternFieldExplicit
              (desugarAstNode fieldName)
              (recur fieldPattern)

mutual
  -- Perenthesized expressions will be removed
  desugarExpressionNode : AstInfo -> ExpressionNode SurfaceAstPhase -> ExpressionNode CanonicalAstPhase
  desugarExpressionNode expressionInfo expression =
    case expression of
      ExprLiteral literal => ExprLiteral (desugarAstNode literal)
      ExprName name => ExprName (desugarAstNode name)
      ExprPath path => ExprPath (desugarPath path)
      ExprBuiltin builtin => ExprBuiltin builtin
      ExprSelf selfReceiver => ExprSelf selfReceiver
      ExprParenthesized inner => (desugarNestedExpression inner).value
      ExprTuple elements => ExprTuple (map desugarNestedExpression elements)
      ExprArray elements => ExprArray (map desugarNestedExpression elements)
      ExprRepeatedArray element count => ExprRepeatedArray (desugarNestedExpression element) (desugarNestedExpression count)
      ExprStructLiteral path fields => ExprStructLiteral (desugarPath path) (map desugarFieldInitializer fields)
      ExprCall callee arguments => ExprCall (desugarNestedExpression callee) (map desugarNestedExpression arguments)
      ExprMethodCall receiver name arguments => ExprMethodCall (desugarNestedExpression receiver) (desugarAstNode name) (map desugarNestedExpression arguments)
      ExprField object name => ExprField (desugarNestedExpression object) (desugarAstNode name)
      ExprTupleIndex tuple indexText => ExprTupleIndex (desugarNestedExpression tuple) indexText
      ExprIndex object index => ExprIndex (desugarNestedExpression object) (desugarNestedExpression index)
      ExprUnary operator operand => ExprUnary (desugarAstNode operator) (desugarNestedExpression operand)
      ExprBinary operator left right => ExprBinary (desugarAstNode operator) (desugarNestedExpression left) (desugarNestedExpression right)
      ExprRange start operator end => ExprRange (map desugarNestedExpression start) (desugarAstNode operator) (map desugarNestedExpression end)
      ExprCast operand target => ExprCast (desugarNestedExpression operand) (desugarType target)
      ExprBlock block => ExprBlock (desugarBlockExpression block)
      ExprIf ifNode => ExprIf (desugarIfNode expressionInfo ifNode)
      ExprQIf ifNode => assert_total $ idris_crash "Desugar.idr: desugarExpressionNode: ExprQIf not implemented"
      ExprSIf ifNode => assert_total $ idris_crash "Desugar.idr: desugarExpressionNode: ExprSIf not implemented"
      ExprMatch matchNode => assert_total $ idris_crash "Desugar.idr: desugarExpressionNode: ExprMatch not implemented"
      ExprQMatch matchNode => assert_total $ idris_crash "Desugar.idr: desugarExpressionNode: ExprQMatch not implemented"
      ExprSMatch matchNode => assert_total $ idris_crash "Desugar.idr: desugarExpressionNode: ExprSMatch not implemented"
      ExprLoop body => ExprLoop (desugarBlockExpression body)
      ExprWhile condition body => ExprWhile (desugarNestedExpression condition) (desugarBlockExpression body)
      ExprFor pattern iterator body => ExprFor (desugarPattern pattern) (desugarNestedExpression iterator) (desugarBlockExpression body)
      ExprBreak value => ExprBreak (map desugarNestedExpression value)
      ExprContinue => ExprContinue
      ExprReturn Nothing =>
        ExprReturn $ Just $
          canonicalAstNode
            (incrementedAstInfo expressionInfo 1)
            DesugaredExpression $
            ExprLiteral $
              canonicalAstNode
                (incrementedAstInfo expressionInfo 2)
                DesugaredUnitValue
                LiteralUnit
      ExprReturn (Just value) => ExprReturn (Just (desugarNestedExpression value))
      ExprCtrl control => ExprCtrl (desugarControlExpressionNode expressionInfo control)
      ExprAdjoint adjoint => ExprAdjoint (desugarAdjointExpressionNode adjoint)
    where
      desugarNestedExpression : SurfaceExpr -> CanonicalExpr
      desugarNestedExpression nestedExpression =
        desugarExpression (assert_smaller expression nestedExpression)

      desugarFieldInitializer : AstNode SurfaceAstPhase (FieldInitializerNode SurfaceAstPhase) ->
        AstNode CanonicalAstPhase (FieldInitializerNode CanonicalAstPhase)
      desugarFieldInitializer (MkAstNode fieldInfo _ fieldNode) =
        canonicalAstNode fieldInfo WrittenCode $
          case fieldNode of
            -- TODO: add tests one parser supports structs
            -- Point { x } becomes Point { x: x }. Keep the original name for
            -- the field and create a separate name for the local value lookup.
            FieldInitShorthand (MkAstNode nameInfo _ name) =>
              FieldInitExplicit
                (canonicalAstNode nameInfo WrittenCode name)
                (canonicalAstNode (incrementedAstInfo nameInfo 2) DesugaredFieldShorthand $
                  ExprName $
                    canonicalAstNode (incrementedAstInfo nameInfo 1) DesugaredFieldShorthand name)
            FieldInitExplicit fieldName fieldValue =>
              FieldInitExplicit (desugarAstNode fieldName) (desugarNestedExpression fieldValue)

      desugarBlockExpression : SurfaceBlock -> CanonicalBlock
      desugarBlockExpression 
        (MkAstNode blockAstInfo _ (MkBlockNode blockInnerDocs blockStatements finalExpression)) =
        canonicalAstNode blockAstInfo WrittenCode $
          MkBlockNode 
            (map desugarAstNode blockInnerDocs) 
            (map (\statement => desugarStatement (assert_smaller expression statement)) blockStatements) 
            (map desugarNestedExpression finalExpression)
      mutual
        -- in case the else statement branch is missing, desugaring adds a default "else { () }" block
        desugarIfNode : AstInfo -> ClassicalIfNode SurfaceAstPhase -> ClassicalIfNode CanonicalAstPhase
        desugarIfNode ifExpressionInfo ifNode@(MkClassicalIfNode ifCondition ifThenBlock Nothing) =
          MkClassicalIfNode
            (desugarNestedExpression ifCondition)
            (desugarBlockExpression ifThenBlock)
            (Just $ ElseBlock (canonicalAstNode desugaredElseBlockAstInfo DesugaredElseBlock unitBlockNode))
          where
            desugaredElseBlockAstInfo = incrementedAstInfo ifExpressionInfo 1
            desugaredUnitExpressionAstInfo = incrementedAstInfo ifExpressionInfo 2
            desugaredDefaultUnitValueAstInfo = incrementedAstInfo ifExpressionInfo 3
            unitBlockNode : BlockNode CanonicalAstPhase
            unitBlockNode =
              MkBlockNode [] [] $
                Just (canonicalAstNode 
                  desugaredUnitExpressionAstInfo
                  DesugaredExpression
                  (ExprLiteral $ canonicalAstNode desugaredDefaultUnitValueAstInfo DesugaredUnitValue LiteralUnit)
                )
        desugarIfNode _ ifNode@(MkClassicalIfNode ifCondition ifThenBlock ifElseBranch) =
          MkClassicalIfNode
            (desugarNestedExpression ifCondition)
            (desugarBlockExpression ifThenBlock)
            (map (desugarElseNode ifNode) ifElseBranch)
        desugarElseNode : ClassicalIfNode SurfaceAstPhase -> ClassicalElseNode SurfaceAstPhase -> ClassicalElseNode CanonicalAstPhase
        desugarElseNode _ (ElseBlock elseBlock) =
          ElseBlock (desugarBlockExpression elseBlock)
        desugarElseNode ifNode (ElseChainedIf (MkAstNode chainedIfInfo _ chainedIfNode)) =
          ElseChainedIf $
            canonicalAstNode chainedIfInfo WrittenCode $
              desugarIfNode chainedIfInfo (assert_smaller ifNode chainedIfNode)

      -- Desugar control invocation by adding on() invocation to ctrl() if missing,
      -- in order to obtain the default control syntax: ctrl(&q0, &q1).on(bs"11")
      desugarOnBasis : Nat -> AstInfo -> Maybe (AstNode SurfaceAstPhase String) -> Maybe (AstNode CanonicalAstPhase String)
      desugarOnBasis controls controlExpressionAstInfo Nothing =
        Just $ canonicalAstNode onBasisAstInfo DesugaredCtrlDefaultOnInvocation onBasisString
        where
          onBasisAstInfo = incrementedAstInfo controlExpressionAstInfo 1
          onBasisString = "bs\"" ++ pack (replicate controls '1') ++ "\""
      desugarOnBasis _ _ (Just onBasis) = Just $ desugarAstNode onBasis

      desugarControlExpressionNode : AstInfo -> ControlExpressionNode SurfaceAstPhase -> ControlExpressionNode CanonicalAstPhase
      desugarControlExpressionNode expressionAstInfo (ControlledCallable controlQubits onBasisRaw controlledCallable) =
        ControlledCallable
          (map desugarNestedExpression controlQubits)
          (desugarOnBasis (length controlQubits) expressionAstInfo onBasisRaw)
          (desugarNestedExpression controlledCallable)
      desugarControlExpressionNode expressionAstInfo (ControlledBlock controlQubits onBasisRaw controlledBlock) =
        ControlledBlock
          (map desugarNestedExpression controlQubits)
          (desugarOnBasis (length controlQubits) expressionAstInfo onBasisRaw)
          (desugarBlockExpression controlledBlock)

      desugarAdjointExpressionNode : AdjointExpressionNode SurfaceAstPhase -> AdjointExpressionNode CanonicalAstPhase
      desugarAdjointExpressionNode (AdjointOfCallable adjointedCallable) = AdjointOfCallable (desugarNestedExpression adjointedCallable)
      desugarAdjointExpressionNode (AdjointBlock adjointedBlock) = AdjointBlock (desugarBlockExpression adjointedBlock)

  desugarExpression : SurfaceExpr -> CanonicalExpr
  desugarExpression (MkAstNode expressionInfo metadata expressionNode) =
    canonicalAstNode expressionInfo WrittenCode (desugarExpressionNode expressionInfo expressionNode)

  desugarType : Ty SurfaceAstPhase (Expr SurfaceAstPhase) -> Ty CanonicalAstPhase (Expr CanonicalAstPhase)
  desugarType writtenType = defaultQubitOwnership (desugarWrittenType writtenType)

  -- Perenthesized types will be removed. The parameters and result of a
  -- function type own their values, so they get the default `linear`; the
  -- rest of the type's owned positions are left to the caller.
  desugarWrittenType : Ty SurfaceAstPhase (Expr SurfaceAstPhase) -> Ty CanonicalAstPhase (Expr CanonicalAstPhase)
  desugarWrittenType (MkAstNode tyAstInfo metadata typeNode) =
    canonicalAstNode tyAstInfo WrittenCode $
      case typeNode of
        TyPrimitive primitiveName =>
          TyPrimitive primitiveName
        TyPath typePath =>
          TyPath (desugarPath typePath)
        TyUnit =>
          TyUnit
        TyParenthesized innerType =>
          (desugarNestedType innerType).value
        TyTuple elementTypes =>
          TyTuple (map desugarNestedType elementTypes)
        TyArray elementType sizeExpression =>
          TyArray 
            (desugarNestedType elementType) 
            (desugarExpression sizeExpression)
        TySlice elementType =>
          TySlice (desugarNestedType elementType)
        TyReference borrowKind referencedType =>
          TyReference 
            (desugarAstNode borrowKind) 
            (desugarNestedType referencedType)
        TyQualified ownershipQualifier qualifiedType =>
          TyQualified (desugarAstNode ownershipQualifier) (desugarNestedType qualifiedType)
        TyFunction functionEffect functionParameters returnType =>
          TyFunction
            (map desugarAstNode functionEffect)
            (map desugarParameter functionParameters)
            (map desugarSignatureType returnType)
      where
        desugarNestedType : SurfaceTy -> CanonicalTy
        desugarNestedType nestedType =
          desugarWrittenType (assert_smaller typeNode nestedType)
        desugarSignatureType : SurfaceTy -> CanonicalTy
        desugarSignatureType nestedType =
          desugarType (assert_smaller typeNode nestedType)
        desugarParameter : SurfaceAstNode (FunctionTypeParameterNode SurfaceAstPhase (SurfaceAstNode (ExpressionNode SurfaceAstPhase))) ->
          CanonicalAstNode (FunctionTypeParameterNode CanonicalAstPhase (CanonicalAstNode (ExpressionNode CanonicalAstPhase)))
        desugarParameter (MkAstNode parameterAstInfo metadata (MkFunctionTypeParameterNode parameterName parameterType)) =
          canonicalAstNode parameterAstInfo WrittenCode $
            MkFunctionTypeParameterNode (desugarAstNode parameterName) (desugarSignatureType parameterType)

  desugarFunctionParameter: AstNode SurfaceAstPhase (FunctionParameterNode SurfaceAstPhase) -> AstNode CanonicalAstPhase (FunctionParameterNode CanonicalAstPhase)
  desugarFunctionParameter (MkAstNode parameterInfo metadata (NormalParameter parameterDocs parameterMutability parameterName parameterType)) =
    canonicalAstNode parameterInfo WrittenCode $
      NormalParameter
        (map desugarAstNode parameterDocs)
        (map desugarAstNode parameterMutability)
        (desugarAstNode parameterName)
        (desugarType parameterType)
  desugarFunctionParameter (MkAstNode parameterInfo metadata (ReceiverParameter receiverDocs receiverBorrow)) =
    canonicalAstNode parameterInfo WrittenCode $
      ReceiverParameter
        (map desugarAstNode receiverDocs)
        (map desugarAstNode receiverBorrow)

  desugarSignedPauliTerm : SurfaceSignedPauliTerm -> SignedPauliTerm CanonicalAstPhase
  desugarSignedPauliTerm (MkAstNode termInfo metadata (MkSignedPauliTermNode sign pauliString)) =
    canonicalAstNode termInfo WrittenCode $
      MkSignedPauliTermNode sign (desugarAstNode pauliString)

  desugarContractPredicate : SurfaceContractPredicate -> CanonicalContractPredicate
  desugarContractPredicate (MkAstNode predicateInfo metadata predicateNode) =
    canonicalAstNode predicateInfo WrittenCode $
      case predicateNode of
        ContractClean qubitArgument =>
          ContractClean (desugarExpression qubitArgument)
        ContractBasis qubitArgument pauliString =>
          ContractBasis
            (desugarExpression qubitArgument)
            (desugarAstNode pauliString)
        ContractSeparable qubitArgument =>
          ContractSeparable (desugarExpression qubitArgument)
        ContractIsolated qubitArgument =>
          ContractIsolated (desugarExpression qubitArgument)
        ContractProduct firstQubitSet otherQubitSets =>
          ContractProduct
            (desugarExpression firstQubitSet)
            (map desugarExpression otherQubitSets)
        ContractStabilized qubitArgument stabilizerTerms =>
          ContractStabilized
            (desugarExpression qubitArgument)
            (map desugarSignedPauliTerm stabilizerTerms)

  desugarContractClause : ContractClause SurfaceAstPhase (Expr SurfaceAstPhase) -> ContractClause CanonicalAstPhase (Expr CanonicalAstPhase) 
  desugarContractClause (MkAstNode contractAstInfo metadata contractClauseNode) =
    canonicalAstNode contractAstInfo WrittenCode $
      case contractClauseNode of
        RequiresClause predicate => RequiresClause (desugarContractPredicate predicate)
        EnsuresClause predicate => EnsuresClause (desugarContractPredicate predicate)

  desugarLetInitializer : LetInitializerNode SurfaceAstPhase -> LetInitializerNode CanonicalAstPhase
  desugarLetInitializer (MkLetInitializerNode marker value) =
    MkLetInitializerNode (desugarAstNode marker) (desugarExpression value)

  desugarAssignmentTarget : SurfaceAstNode (AssignmentTargetNode SurfaceAstPhase) -> CanonicalAstNode (AssignmentTargetNode CanonicalAstPhase)
  desugarAssignmentTarget (MkAstNode assignmentTargetAstInfo metadata assignmentTargetNode) =
    canonicalAstNode assignmentTargetAstInfo WrittenCode $
      case assignmentTargetNode of
        AssignTargetName targetName =>
          AssignTargetName (desugarAstNode targetName)
        AssignTargetIndex targetObject indexExpression =>
          AssignTargetIndex
            (desugarExpression targetObject)
            (desugarExpression indexExpression)
        AssignTargetField targetObject fieldName =>
          AssignTargetField
            (desugarExpression targetObject)
            (desugarAstNode fieldName)
        AssignTargetTupleIndex targetObject tupleIndexRawText =>
          AssignTargetTupleIndex
            (desugarExpression targetObject)
            tupleIndexRawText

  ||| A `let`'s `linear`/`affine` is moved into the owned positions of its
  ||| annotation, keeping the keyword's span, and the default `linear` is
  ||| added where none was written.
  ||| Desugar each assignment target and value once, preserving the operator.
  ||| Compound assignment lowering must wait until types and places are known:
  ||| copying a target into the RHS would duplicate evaluation and any scopes
  ||| introduced by its subexpressions, while reusing their node IDs.
  desugarStatement : Statement SurfaceAstPhase -> Statement CanonicalAstPhase
  desugarStatement (MkAstNode statementAstInfo metadata statementNode) =
    canonicalAstNode statementAstInfo WrittenCode $
      case statementNode of
        StatementLet (MkLetBindingNode qualifiers pattern typeAnnotation initializer) =>
          let (letQualifiers, letTypeAnnotation) =
                moveLetOwnershipIntoType
                  (map desugarAstNode qualifiers)
                  (map (\ty => desugarWrittenType (assert_smaller statementNode ty)) typeAnnotation)
          in StatementLet $
               MkLetBindingNode
                 letQualifiers
                 (desugarPattern pattern)
                 letTypeAnnotation
                 (map (\init => desugarLetInitializer (assert_smaller statementNode init)) initializer)
        StatementAssignment (MkAssignmentNode assignmentTarget assignmentOperator assignmentValue) =>
          StatementAssignment $
            MkAssignmentNode
              (desugarAssignmentTarget assignmentTarget)
              (desugarAstNode assignmentOperator)
              (desugarExpression assignmentValue)
        StatementSemiExpression statementExpression =>
          StatementSemiExpression (desugarExpression statementExpression)
        StatementExpression statementExpression =>
          StatementExpression (desugarExpression statementExpression)

||| A final expression is desugared to a return statement. If there is no
||| final expression, an explicit `return ();` statement is generated.
||| Also "return 2" is desugared to "return 2;"
||| Also "(return 2)" is desugared to "return 2;"
desugarFunctionBody : Block SurfaceAstPhase -> Block CanonicalAstPhase
desugarFunctionBody (MkAstNode functionBodyAstInfo metadata (MkBlockNode blockInnerDocs blockStatements finalExpression)) =
  canonicalAstNode functionBodyAstInfo WrittenCode $
    MkBlockNode
      (map desugarAstNode blockInnerDocs)
      (map desugarStatement blockStatements ++ desugarFinalExpression finalExpression)
      Nothing
    where
      desugarFinalExpression : Maybe (AstNode SurfaceAstPhase (ExpressionNode SurfaceAstPhase)) -> List (AstNode CanonicalAstPhase (StatementNode CanonicalAstPhase))
      desugarFinalExpression Nothing =
        let statementSemiExpressionInfo = incrementedAstInfo functionBodyAstInfo 1
            expressionReturnInfo = incrementedAstInfo functionBodyAstInfo 2
            unitExpressionInfo = incrementedAstInfo functionBodyAstInfo 3
            unitValueInfo = incrementedAstInfo functionBodyAstInfo 4
        in
          [canonicalAstNode statementSemiExpressionInfo DesugaredReturnStatement
            (StatementSemiExpression $
              canonicalAstNode expressionReturnInfo DesugaredReturnStatement $
                ExprReturn $ Just $
                  canonicalAstNode unitExpressionInfo DesugaredExpression $
                    ExprLiteral $
                      canonicalAstNode unitValueInfo DesugaredUnitValue LiteralUnit)]
      desugarFinalExpression (Just finalExpression@(MkAstNode finalExpressionInfo _ _)) =
        let statementSemiExpressionInfo = { span := finalExpressionInfo.span } (incrementedAstInfo functionBodyAstInfo 1)
            desugaredFinalExpression = desugarExpression finalExpression
        in case desugaredFinalExpression.value of
          ExprReturn _ =>
            [canonicalAstNode statementSemiExpressionInfo DesugaredReturnStatement (StatementSemiExpression desugaredFinalExpression)]
          _ =>
            let expressionReturnInfo = { span := finalExpressionInfo.span } (incrementedAstInfo functionBodyAstInfo 2)
            in
              [canonicalAstNode statementSemiExpressionInfo DesugaredReturnStatement
                (StatementSemiExpression $ canonicalAstNode expressionReturnInfo DesugaredReturnStatement (ExprReturn (Just desugaredFinalExpression)))]

desugarItem : SurfaceItem -> CanonicalItem
desugarItem (MkAstNode itemInfo metadata item) =
  canonicalAstNode itemInfo WrittenCode $
    case item of
      ItemModule declaration => assert_total $ idris_crash "Desugar.idr: desugarItem: ItemModule not implemented."
      ItemUse declaration => assert_total $ idris_crash "Desugar.idr: desugarItem: ItemUse not implemented."
      ItemConst declaration => ItemConst $ desugarConstDeclaration declaration
      ItemEnum declaration => assert_total $ idris_crash "Desugar.idr: desugarItem: ItemEnum not implemented"
      ItemQEnum declaration => assert_total $ idris_crash "Desugar.idr: desugarItem: ItemQEnum not implemented"
      ItemStruct declaration => assert_total $ idris_crash "Desugar.idr: desugarItem: ItemStruct not implemented"
      ItemImpl declaration => assert_total $ idris_crash "Desugar.idr: desugarItem: ItemImpl not implemented"
      ItemFunction declaration => ItemFunction $ desugarFunctionDeclaration declaration
    where
      desugarConstDeclaration : ConstDeclarationNode SurfaceAstPhase -> ConstDeclarationNode CanonicalAstPhase
      desugarConstDeclaration
          (MkConstDeclarationNode
            constDocs
            constVisibility
            constName
            constType
            constValue) =
              MkConstDeclarationNode
                (map desugarAstNode constDocs)
                (map desugarAstNode constVisibility)
                (desugarAstNode constName)
                (desugarType constType)
                (desugarExpression constValue)
      -- if function effect is missing, desugaring adds the default "general" function effect
      -- if return type is missing, the default "unit" return type is added to function declaration
      -- if function does not return anything, desugaring chnages function body to return the "unit" data
      desugarFunctionDeclaration : FunctionDeclarationNode SurfaceAstPhase -> FunctionDeclarationNode CanonicalAstPhase
      desugarFunctionDeclaration
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
          ) = let
                functionNameString = functionName.value.nameNodeText
                (desugaredAttributes, increment) = mapWithId (desugarAttribute functionNameString) 1 functionAttributes
                (desugaredFunctionEffect, increment) = desugarFunctionEffect functionEffect increment
                desugaredReturnType = desugarFunctionType returnType increment
              in 
                MkFunctionDeclarationNode
                (map desugarAstNode functionDocs)
                desugaredAttributes
                (map desugarAstNode functionVisibility)
                (map desugarAstNode functionConstness)
                desugaredFunctionEffect
                (desugarAstNode functionName)
                (map desugarFunctionParameter functionParameters)
                desugaredReturnType
                (map desugarAstNode supportClause)
                (map desugarContractClause contractClauses)
                (desugarFunctionBody functionBody)
              where
                desugarFunctionEffect : Maybe (AstNode SurfaceAstPhase FunctionEffect) -> Nat -> (Maybe (AstNode CanonicalAstPhase FunctionEffect), Nat)
                desugarFunctionEffect Nothing inc = (Just $ canonicalAstNode (incrementedAstInfo itemInfo inc) DesugaredDefaultFunctionEffect EffectGeneral, inc + 1)
                desugarFunctionEffect (Just functionEffectNode) inc = (Just $ desugarAstNode functionEffectNode, inc)
                desugarFunctionType : Maybe (Ty SurfaceAstPhase (Expr SurfaceAstPhase)) -> Nat -> Maybe (Ty CanonicalAstPhase (Expr CanonicalAstPhase))
                desugarFunctionType Nothing inc = Just $ canonicalAstNode (incrementedAstInfo itemInfo inc) DesugaredDefaultFunctionReturnType TyUnit
                desugarFunctionType (Just functionTypeNode) _ = Just $ desugarType functionTypeNode

export
desugarSurfaceSyntax : SurfaceSourceFile -> CanonicalSourceFile
desugarSurfaceSyntax
    (MkAstNode fileInfo metadata (MkSourceFileNode docs items)) =
  canonicalAstNode fileInfo WrittenCode $
    MkSourceFileNode
      (map desugarAstNode docs)
      (map desugarItem items)

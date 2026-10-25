module Frontend.Parser.Helper

import Text.Bounds
import Text.Parse.Manual

import Frontend.Source
import Frontend.Token
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Parser.Error
import Frontend.Syntax.Attribute
import Frontend.Syntax.AST
import Frontend.Syntax.Common
import Frontend.Syntax.Doc
import Frontend.Syntax.Literal
import Frontend.Syntax.Name
import Frontend.Syntax.Operator
import Frontend.Syntax.Pattern
import Frontend.Syntax.Type

%default total

||| Creates a NodeId with current Id, and returns the next Id for the next node.
public export
reserveNodeId : Nat -> (NodeId, Nat)
reserveNodeId current = (MkNodeId current 0, S current)

public export
snocList1 : List1 a -> a -> List1 a
snocList1 (first ::: rest) value = first ::: (rest ++ [value])

-- Text.Bounds positions use zero-based lines and columns, while Leaf's
-- SourcePos uses one-based lines and columns. There is also an endpoint
-- mismatch specific to bounds emitted by ILex: they originate as ByteBounds,
-- whose end is the position of the token's last byte, and integer literal preserves
-- that inclusive end. Leaf's SourceSpan instead uses a half-open end position.
--
-- Start and end must consequently be converted differently. The start only
-- changes index base; the end changes index base and advances past the final
-- character. This conversion is for ILex-produced Bounds, not arbitrary
-- Text.Bounds values. Advancing the column is safe as long as tokens do not
-- end with a newline which is actually the case for tokens in Token.idr.

sourceStartPos : Position -> SourcePos
sourceStartPos (P line column) =
  MkSourcePos (S line) (S column)

sourceEndPos : Position -> SourcePos
sourceEndPos (P line column) =
  MkSourcePos (S line) (S (S column))

public export
sourceSpan : Bounds -> SourceSpan
sourceSpan NoBounds =
  let start = MkSourcePos 1 1
  in MkSourceSpan "" start start
sourceSpan (BS start end) =
  MkSourceSpan "" (sourceStartPos start) (sourceEndPos end)

lastItemSpan : SurfaceItem -> List SurfaceItem -> SourceSpan
lastItemSpan item [] =
    item.astInfo.span
lastItemSpan _ (item :: rest) =
    lastItemSpan item rest

public export
sourceFileInfo : String -> NodeId -> List SurfaceItem -> AstInfo
sourceFileInfo sourceFileName nodeId [] =
    let start = MkSourcePos 1 1 in
        MkAstInfo nodeId (MkSourceSpan sourceFileName start start)
sourceFileInfo sourceFileName nodeId (first :: rest) =
    let firstSpan = first.astInfo.span
        lastSpan = lastItemSpan first rest
        fileSpan : SourceSpan =
          { file := sourceFileName } (mergeSpans firstSpan lastSpan)
     in MkAstInfo nodeId fileSpan

||| Legal states reached while collecting a top-level item's declaration prefix.
||| Each constructor represents one accepted modifier sequence and retains the
||| visibility that may precede it. `PrefixConstEffect` represents
||| `const <effect> fn`; the reverse order is deliberately not constructible.
public export
data ItemPrefixState
  = PrefixOrdinary (Maybe (SurfaceAstNode VisibilityQualifier))
  | PrefixConst (Maybe (SurfaceAstNode VisibilityQualifier)) Bounds
  | PrefixEffect
      (Maybe (SurfaceAstNode VisibilityQualifier))
      (SurfaceAstNode FunctionEffect)
  | PrefixConstEffect
      (Maybe (SurfaceAstNode VisibilityQualifier))
      Bounds
      (SurfaceAstNode FunctionEffect)

||| Decomposes an accumulated prefix state into its visibility, `const`
||| bounds, and effect components for uniform `fn` dispatch.
public export
prefixComponents :
     ItemPrefixState
  -> ( Maybe (SurfaceAstNode VisibilityQualifier)
     , Maybe Bounds
     , Maybe (SurfaceAstNode FunctionEffect))
prefixComponents (PrefixOrdinary visibility) =
  (visibility, Nothing, Nothing)
prefixComponents (PrefixConst visibility constBounds) =
  (visibility, Just constBounds, Nothing)
prefixComponents (PrefixEffect visibility effect) =
  (visibility, Nothing, Just effect)
prefixComponents (PrefixConstEffect visibility constBounds effect) =
  (visibility, Just constBounds, Just effect)

public export
record CommaList a where
  constructor MkCommaList
  values : List a
  closeBounds : Bounds

public export
record TypePathTail where
    constructor MkTypePathTail
    pathSegments : List SurfacePathSegment
    lastBounds : Bounds

public export
record ItemPrefix where
  constructor MkItemPrefix
  itemNodeId : NodeId
  declarationStart : Bounds
  attributes : SnocList SurfaceAttribute
  state : ItemPrefixState

public export
failWithCustomError : CustomParseError -> Bounds -> Res isStrict Token tokens CustomParseError a
failWithCustomError customParseError bounds = Fail0 (B (Custom customParseError) bounds)

public export
parameterStartSpan :
     List SurfaceDocComment
  -> Maybe (SurfaceAstNode Mutability)
  -> SurfaceName
  -> SourceSpan
parameterStartSpan (doc :: _) _ _ = doc.astInfo.span
parameterStartSpan [] (Just mutability) _ = mutability.astInfo.span
parameterStartSpan [] Nothing name = name.astInfo.span

public export
assignmentOperator : Symbol -> Maybe AssignmentOperator
assignmentOperator SymEq        = Just AssignValue
assignmentOperator SymPlusEq    = Just AssignAdd
assignmentOperator SymMinusEq   = Just AssignSubtract
assignmentOperator SymStarEq    = Just AssignMultiply
assignmentOperator SymSlashEq   = Just AssignDivide
assignmentOperator SymPercentEq = Just AssignRemainder
assignmentOperator SymAndEq     = Just AssignBitAnd
assignmentOperator SymOrEq      = Just AssignBitOr
assignmentOperator SymCaretEq   = Just AssignBitXor
assignmentOperator SymShlEq     = Just AssignShiftLeft
assignmentOperator SymShrEq     = Just AssignShiftRight
assignmentOperator _            = Nothing

public export
unaryOperator : Symbol -> Maybe UnaryOperator
unaryOperator SymMinus = Just UnaryNegate
unaryOperator SymBang  = Just UnaryLogicalNot
unaryOperator SymAmp   = Just (UnaryBorrow SharedBorrow)
unaryOperator _        = Nothing

public export
binaryOperator : Symbol -> Maybe (BinaryOperator, Nat)
binaryOperator SymStar   = Just (BinaryMultiply, 80)
binaryOperator SymSlash  = Just (BinaryDivide, 80)
binaryOperator SymPercent = Just (BinaryRemainder, 80)
binaryOperator SymPlus   = Just (BinaryAdd, 75)
binaryOperator SymMinus  = Just (BinarySubtract, 75)
binaryOperator SymShl    = Just (BinaryShiftLeft, 70)
binaryOperator SymShr    = Just (BinaryShiftRight, 70)
binaryOperator SymAmp    = Just (BinaryBitAnd, 65)
binaryOperator SymCaret  = Just (BinaryBitXor, 60)
binaryOperator SymPipe   = Just (BinaryBitOr, 55)
binaryOperator SymLt     = Just (BinaryLess, 50)
binaryOperator SymLe     = Just (BinaryLessEqual, 50)
binaryOperator SymGt     = Just (BinaryGreater, 50)
binaryOperator SymGe     = Just (BinaryGreaterEqual, 50)
binaryOperator SymEqEq   = Just (BinaryEqual, 50)
binaryOperator SymNotEq  = Just (BinaryNotEqual, 50)
binaryOperator SymAndAnd = Just (BinaryLogicalAnd, 45)
binaryOperator SymOrOr   = Just (BinaryLogicalOr, 40)
binaryOperator _         = Nothing

public export
rangeOperator : Symbol -> Maybe RangeOperator
rangeOperator SymDotDot   = Just RangeExclusive
rangeOperator SymDotDotEq = Just RangeInclusive
rangeOperator _           = Nothing

public export
initializerMarker : Symbol -> Maybe InitializerMarker
initializerMarker SymEq       = Just InitializerEquals
initializerMarker SymWalrusEq = Just InitializerAutoUncompute
initializerMarker _           = Nothing

public export
functionEffectFromKeyword : Keyword -> Maybe FunctionEffect
functionEffectFromKeyword KwClassical  = Just EffectClassical
functionEffectFromKeyword KwUncompsafe = Just EffectUncompsafe
functionEffectFromKeyword KwUnitary    = Just EffectUnitary
functionEffectFromKeyword KwIsometry   = Just EffectIsometry
functionEffectFromKeyword KwCoisometry = Just EffectCoisometry
functionEffectFromKeyword KwGeneral    = Just EffectGeneral
functionEffectFromKeyword _            = Nothing

public export
storageQualifierFromKeyword : Keyword -> Maybe QuantumStorageQualifier
storageQualifierFromKeyword KwLinear  = Just QualifierLinear
storageQualifierFromKeyword KwAffine  = Just QualifierAffine
storageQualifierFromKeyword KwScratch = Just QualifierScratch
storageQualifierFromKeyword _         = Nothing

public export
storageQualifierFromToken : Token -> Maybe QuantumStorageQualifier
storageQualifierFromToken (TokKw keyword) = storageQualifierFromKeyword keyword
storageQualifierFromToken _               = Nothing

||| The ownership qualifier a `linear` or `affine` token denotes.
public export
ownershipQualifierFromToken : Token -> Maybe OwnershipQualifier
ownershipQualifierFromToken token =
  case storageQualifierFromToken token of
    Just qualifier => storageOwnership qualifier
    Nothing => Nothing

public export
unsupportedTopLevelItem : Keyword -> Maybe CustomParseError
unsupportedTopLevelItem KwMod =
  Just (UnsupportedFeature "Modules are not yet supported.")
unsupportedTopLevelItem KwUse =
  Just (UnsupportedFeature "Use statements are not yet supported.")
unsupportedTopLevelItem KwEnum =
  Just (UnsupportedFeature "Enums are not yet supported.")
unsupportedTopLevelItem KwQenum =
  Just (UnsupportedFeature "Qenums are not yet supported.")
unsupportedTopLevelItem KwImpl =
  Just (UnsupportedFeature "Impl blocks and structs are not yet supported.")
unsupportedTopLevelItem KwStruct =
  Just (UnsupportedFeature "Structs are not yet supported.")
unsupportedTopLevelItem _ = Nothing

public export
startsWithUppercase : String -> Bool
startsWithUppercase text =
  case unpack text of
    character :: _ => character >= 'A' && character <= 'Z'
    [] => False

public export
makeLiteralExpression : LiteralNode -> Bounds -> Nat -> (SurfaceExpr, Nat)
makeLiteralExpression literalValue bounds nodeId =
  let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId
      (literalNodeId, nextNodeId) = reserveNodeId afterExpressionNodeId
      literal = surfaceAstNode (MkAstInfo literalNodeId (sourceSpan bounds))
                               literalValue
      expression = surfaceAstNode (MkAstInfo expressionNodeId (sourceSpan bounds))
                                  (ExprLiteral literal)
   in (expression, nextNodeId)

public export
makeName : String -> Bounds -> Nat -> (SurfaceName, Nat)
makeName nameText bounds nodeId =
  let (nameNodeId, nextNodeId) = reserveNodeId nodeId
      name = surfaceAstNode (MkAstInfo nameNodeId (sourceSpan bounds)) (MkNameNode nameText)
   in (name, nextNodeId)

public export
makeNameExpression : String -> Bounds -> Nat -> (SurfaceExpr, Nat)
makeNameExpression nameText bounds nodeId =
  let (expressionNodeId, afterExpressionNodeId) = reserveNodeId nodeId
      (name, nextNodeId) = makeName nameText bounds afterExpressionNodeId
      expression = surfaceAstNode (MkAstInfo expressionNodeId (sourceSpan bounds))
                                  (ExprName name)
   in (expression, nextNodeId)

public export
makeBuiltinExpression : Builtin -> Bounds -> Nat -> (SurfaceExpr, Nat)
makeBuiltinExpression builtin bounds nodeId =
  let (expressionNodeId, nextNodeId) = reserveNodeId nodeId
      expression = surfaceAstNode (MkAstInfo expressionNodeId (sourceSpan bounds))
                                  (ExprBuiltin builtin)
   in (expression, nextNodeId)


public export
assignmentTargetFromExpression : SurfaceExpr -> Maybe (AssignmentTargetNode SurfaceAstPhase)
assignmentTargetFromExpression (MkAstNode _ _ expression) =
  case expression of
    ExprName name => Just (AssignTargetName name)
    ExprIndex object index => Just (AssignTargetIndex object index)
    ExprField object field => Just (AssignTargetField object field)
    ExprTupleIndex object indexRaw => Just (AssignTargetTupleIndex object indexRaw)
    _ => Nothing

public export
isBlockLikeExpression : SurfaceExpr -> Bool
isBlockLikeExpression (MkAstNode _ _ expression) =
  case expression of
    ExprBlock _ => True
    ExprIf _ => True
    ExprQIf _ => True
    ExprSIf _ => True
    ExprMatch _ => True
    ExprQMatch _ => True
    ExprSMatch _ => True
    ExprLoop _ => True
    ExprWhile _ _ => True
    ExprFor _ _ _ => True
    ExprCtrl (ControlledBlock _ _ _) => True
    ExprAdjoint (AdjointBlock _) => True
    _ => False

public export
isComparisonOperator : BinaryOperator -> Bool
isComparisonOperator BinaryEqual = True
isComparisonOperator BinaryNotEqual = True
isComparisonOperator BinaryGreater = True
isComparisonOperator BinaryGreaterEqual = True
isComparisonOperator BinaryLess = True
isComparisonOperator BinaryLessEqual = True
isComparisonOperator _ = False

public export
isUnparenthesizedComparison : SurfaceExpr -> Bool
isUnparenthesizedComparison (MkAstNode _ _ (ExprBinary operator _ _)) =
  isComparisonOperator operator.value
isUnparenthesizedComparison _ = False

public export
isOpenRangeTerminator : Token -> Bool
isOpenRangeTerminator (TokSym SymSemi) = True
isOpenRangeTerminator (TokSym SymComma) = True
isOpenRangeTerminator (TokSym SymRParen) = True
isOpenRangeTerminator (TokSym SymRBracket) = True
isOpenRangeTerminator (TokSym SymRBrace) = True
isOpenRangeTerminator _ = False

public export
isOptionalValueTerminator : Token -> Bool
isOptionalValueTerminator (TokSym SymSemi) = True
isOptionalValueTerminator (TokSym SymComma) = True
isOptionalValueTerminator (TokSym SymRBrace) = True
isOptionalValueTerminator _ = False

public export
nextTokenSatisfies :
  (Token -> Bool) -> List (Bounded Token) -> Bool
nextTokenSatisfies predicate ((B token _) :: _) = predicate token
nextTokenSatisfies _ [] = False

||| Valid quantum-storage qualifiers collected in source order. Ownership and
||| scratch occupy separate slots so duplicates and conflicting ownership
||| qualifiers can be rejected consistently by every grammar that uses them.
public export
record StorageQualifiers where
  constructor MkStorageQualifiers
  ownership : Maybe (SurfaceAstNode QuantumStorageQualifier)
  scratch : Maybe (SurfaceAstNode QuantumStorageQualifier)
  ordered : SnocList (SurfaceAstNode QuantumStorageQualifier)

public export
emptyStorageQualifiers : StorageQualifiers
emptyStorageQualifiers = MkStorageQualifiers Nothing Nothing [<]

||| Diagnostic for a qualifier written after one occupying the same slot.
secondQualifierMessage : (Eq qualifier, Show qualifier) => qualifier -> qualifier -> String
secondQualifierMessage first second =
  if first == second
    then "Duplicate `" ++ show second ++ "` storage qualifier."
    else "Cannot combine `" ++ show first ++ "` and `" ++ show second ++ "` storage qualifiers."

||| Adds one located qualifier or returns the diagnostic for an invalid combination.
public export
addStorageQualifier :
     StorageQualifiers
  -> SurfaceAstNode QuantumStorageQualifier
  -> Either String StorageQualifiers
addStorageQualifier qualifiers located =
  case located.value of
    QualifierScratch =>
      case qualifiers.scratch of
        Just existing => Left (secondQualifierMessage existing.value located.value)
        Nothing => Right $ MkStorageQualifiers qualifiers.ownership
          (Just located) (qualifiers.ordered :< located)
    QualifierLinear => addOwnership
    QualifierAffine => addOwnership
  where
    addOwnership : Either String StorageQualifiers
    addOwnership =
      case qualifiers.ownership of
        Nothing => Right $ MkStorageQualifiers (Just located)
          qualifiers.scratch (qualifiers.ordered :< located)
        Just existing => Left (secondQualifierMessage existing.value located.value)

||| `scratch` describes cleanup at the end of a binding's scope, so it is only
||| valid on `let` bindings, never inside a type.
public export
scratchInTypeMessage : String
scratchInTypeMessage = "The `scratch` qualifier is only allowed on `let` bindings, not in types: write `let scratch q: qubit = ...`."

||| The ownership qualifier a storage keyword denotes inside a type, or the
||| diagnostic for `scratch`.
public export
typeOwnershipQualifier : QuantumStorageQualifier -> Either String OwnershipQualifier
typeOwnershipQualifier qualifier =
  maybe (Left scratchInTypeMessage) Right (storageOwnership qualifier)

||| Diagnostic for a second storage keyword following an ownership qualifier
||| inside a type: a type holds exactly one ownership qualifier.
secondTypeQualifierMessage : OwnershipQualifier -> QuantumStorageQualifier -> String
secondTypeQualifierMessage first second =
  either id (secondQualifierMessage first) (typeOwnershipQualifier second)

||| Diagnostic for a token other than `qubit` following an ownership qualifier
||| inside a type: a qualifier applies to a single qubit, so a qubit array or
||| tuple qualifies each of its qubits instead. A slice is only ever borrowed,
||| and nothing behind a reference is qualified, so no slice suggestion.
public export
qualifiedNonQubitMessage : OwnershipQualifier -> Token -> String
qualifiedNonQubitMessage qualifier token =
  case storageQualifierFromToken token of
    Just second => secondTypeQualifierMessage qualifier second
    Nothing =>
      case token of
        TokSym SymLBracket =>
          written ++ " cannot qualify an array or slice: qualify the qubits of an array instead, e.g. `[" ++
          qualifiedQubit ++ "; 2]`."
        TokSym SymLParen =>
          written ++ " cannot qualify a parenthesized type or tuple: qualify each qubit inside it instead, e.g. `" ++
          qualifiedQubit ++ "` or `(" ++ qualifiedQubit ++ ", " ++ qualifiedQubit ++ ")`."
        _ => written ++ " can only qualify `qubit`, not " ++ describeToken token ++ "."
  where
    written : String
    written = "The `" ++ show qualifier ++ "` qualifier"

    qualifiedQubit : String
    qualifiedQubit = show qualifier ++ " qubit"

||| Diagnostic for an ownership qualifier written directly after `&` or `&mut`.
public export
qualifierBehindReferenceMessage : OwnershipQualifier -> String
qualifierBehindReferenceMessage qualifier =
  "The `" ++ show qualifier ++ "` qualifier cannot be written behind a reference: " ++
  "a reference borrows its referent without owning it, so remove the qualifier."

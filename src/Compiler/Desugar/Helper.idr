module Compiler.Desugar.Helper

import Data.List1
import Data.Maybe
import Frontend.ASTData
import Frontend.ASTPhases
import Frontend.Source
import Frontend.Syntax.AST
import Frontend.Syntax.Common
import Frontend.Syntax.Name
import Frontend.Syntax.Operator
import Frontend.Syntax.Type
import Frontend.Token

%default total

export
mapWithId :
  {a : Type} ->
  {b : Type} ->
  (fun : Nat -> a -> (b, Nat)) ->
  (startingId : Nat) ->
  (values : List a) ->
  (List b, Nat)
mapWithId fun fstId [] = ([], fstId)
mapWithId fun fstId (x :: xs) =
  let (result, sndId) = fun fstId x
      (remaining, finalId) = mapWithId fun sndId xs
  in (result :: remaining, finalId)

export
incrementedAstInfo : AstInfo -> Nat -> AstInfo
incrementedAstInfo astInfo inc =
  MkAstInfo (MkNodeId astInfo.nodeId.surfaceId (astInfo.nodeId.desugarId + inc)) astInfo.span

||| A multiplicity qualifier to insert into a type, and where it came from.
public export
record MultiplicityInsertion where
  constructor MkMultiplicityInsertion
  multiplicity : QuantumMultiplicityQualifier
  provenance   : NodeProvenance
  keywordSpan  : Maybe SourceSpan  -- the `let` keyword it was moved from; Nothing for the default

defaultLinearInsertion : MultiplicityInsertion
defaultLinearInsertion =
  MkMultiplicityInsertion QuantumMultiplicityLinear DesugaredDefaultQubitQualifier Nothing

-- The wrapper and qualifier take the next two desugar ids of the wrapped type
-- node. The wrapper spans the wrapped type; a qualifier moved from a `let`
-- spans the keyword it was written as, so diagnostics point at that keyword
-- (and so lies outside its wrapper's span), while a default one spans the type.
wrapInMultiplicity : MultiplicityInsertion -> CanonicalTy -> CanonicalTy
wrapInMultiplicity insertion qualifiedType@(MkAstNode typeInfo _ _) =
  let qualifierInfo =
        { span := fromMaybe typeInfo.span insertion.keywordSpan } (incrementedAstInfo typeInfo 2)
  in canonicalAstNode (incrementedAstInfo typeInfo 1) insertion.provenance $
       TyQualified
         (canonicalAstNode qualifierInfo insertion.provenance insertion.multiplicity)
         qualifiedType

-- Qualifies every owned position of a type that has no multiplicity qualifier
-- yet (see "Owned positions" in Frontend.Syntax.Type).
qualifyOwnedQubits : MultiplicityInsertion -> CanonicalTy -> CanonicalTy
qualifyOwnedQubits insertion = mapOwnedPositions qualify
  where
    qualify : CanonicalTy -> CanonicalTy
    qualify position =
      case positionQualifier position of
        Just _ => position
        Nothing => wrapInMultiplicity insertion position

||| Adds the default `linear` to every unqualified owned position of a type.
export
defaultQubitMultiplicity : CanonicalTy -> CanonicalTy
defaultQubitMultiplicity = qualifyOwnedQubits defaultLinearInsertion

||| Moves a `let` binding's `linear`/`affine` into the owned positions of its
||| annotation, or adds the default `linear` when none was written. Each moved
||| qualifier keeps the span of the keyword written on the `let`. The qualifier
||| stays on the `let` when there is no annotation, or when the annotation has
||| no unqualified owned position (typechecking reports that case). `scratch`
||| always stays on the `let`.
export
moveLetMultiplicityIntoType :
     List (CanonicalAstNode QuantumStorageQualifier)
  -> Maybe CanonicalTy
  -> (List (CanonicalAstNode QuantumStorageQualifier), Maybe CanonicalTy)
moveLetMultiplicityIntoType qualifiers Nothing = (qualifiers, Nothing)
moveLetMultiplicityIntoType qualifiers (Just annotation) =
  case mapMaybe writtenMultiplicity qualifiers of
    [] => (qualifiers, Just (defaultQubitMultiplicity annotation))
    insertion :: _ =>
      if any (isNothing . positionQualifier) (ownedPositions annotation)
        then
          ( filter (\qualifier => qualifier.value == QualifierScratch) qualifiers
          , Just (qualifyOwnedQubits insertion annotation)
          )
        else (qualifiers, Just annotation)
  where
    writtenMultiplicity : CanonicalAstNode QuantumStorageQualifier -> Maybe MultiplicityInsertion
    writtenMultiplicity (MkAstNode keywordInfo _ keyword) =
      map (\multiplicity => MkMultiplicityInsertion multiplicity DesugaredMovedQubitQualifier (Just keywordInfo.span))
          (storageMultiplicity keyword)

export
assignmentOperatorToBinary : AssignmentOperator -> Maybe BinaryOperator
assignmentOperatorToBinary AssignValue = Nothing
assignmentOperatorToBinary AssignAdd = Just BinaryAdd
assignmentOperatorToBinary AssignSubtract = Just BinarySubtract
assignmentOperatorToBinary AssignMultiply = Just BinaryMultiply
assignmentOperatorToBinary AssignDivide = Just BinaryDivide
assignmentOperatorToBinary AssignRemainder = Just BinaryRemainder
assignmentOperatorToBinary AssignBitAnd = Just BinaryBitAnd
assignmentOperatorToBinary AssignBitOr = Just BinaryBitOr
assignmentOperatorToBinary AssignBitXor = Just BinaryBitXor
assignmentOperatorToBinary AssignShiftLeft = Just BinaryShiftLeft
assignmentOperatorToBinary AssignShiftRight = Just BinaryShiftRight

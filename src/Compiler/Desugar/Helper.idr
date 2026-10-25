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

||| An ownership qualifier to insert into a type, and where it came from.
public export
record OwnershipInsertion where
  constructor MkOwnershipInsertion
  ownership   : OwnershipQualifier
  provenance  : NodeProvenance
  keywordSpan : Maybe SourceSpan  -- the `let` keyword it was moved from; Nothing for the default

defaultLinearInsertion : OwnershipInsertion
defaultLinearInsertion =
  MkOwnershipInsertion OwnershipLinear DesugaredDefaultQubitQualifier Nothing

-- The wrapper and qualifier take the next two desugar ids of the wrapped type
-- node. The wrapper spans the wrapped type; a qualifier moved from a `let`
-- spans the keyword it was written as, so diagnostics point at that keyword
-- (and so lies outside its wrapper's span), while a default one spans the type.
wrapInOwnership : OwnershipInsertion -> CanonicalTy -> CanonicalTy
wrapInOwnership insertion qualifiedType@(MkAstNode typeInfo _ _) =
  let qualifierInfo =
        { span := fromMaybe typeInfo.span insertion.keywordSpan } (incrementedAstInfo typeInfo 2)
  in canonicalAstNode (incrementedAstInfo typeInfo 1) insertion.provenance $
       TyQualified
         (canonicalAstNode qualifierInfo insertion.provenance insertion.ownership)
         qualifiedType

-- Qualifies every owned position of a type that has no ownership qualifier
-- yet (see "Owned positions" in Frontend.Syntax.Type).
qualifyOwnedQubits : OwnershipInsertion -> CanonicalTy -> CanonicalTy
qualifyOwnedQubits insertion = mapOwnedPositions qualify
  where
    qualify : CanonicalTy -> CanonicalTy
    qualify position =
      case positionQualifier position of
        Just _ => position
        Nothing => wrapInOwnership insertion position

||| Adds the default `linear` to every unqualified owned position of a type.
export
defaultQubitOwnership : CanonicalTy -> CanonicalTy
defaultQubitOwnership = qualifyOwnedQubits defaultLinearInsertion

||| Moves a `let` binding's `linear`/`affine` into the owned positions of its
||| annotation, or adds the default `linear` when none was written. Each moved
||| qualifier keeps the span of the keyword written on the `let`. The qualifier
||| stays on the `let` when there is no annotation, or when the annotation has
||| no unqualified owned position (typechecking reports that case). `scratch`
||| always stays on the `let`.
export
moveLetOwnershipIntoType :
     List (CanonicalAstNode QuantumStorageQualifier)
  -> Maybe CanonicalTy
  -> (List (CanonicalAstNode QuantumStorageQualifier), Maybe CanonicalTy)
moveLetOwnershipIntoType qualifiers Nothing = (qualifiers, Nothing)
moveLetOwnershipIntoType qualifiers (Just annotation) =
  case mapMaybe writtenOwnership qualifiers of
    [] => (qualifiers, Just (defaultQubitOwnership annotation))
    insertion :: _ =>
      if any (isNothing . positionQualifier) (ownedPositions annotation)
        then
          ( filter (\qualifier => qualifier.value == QualifierScratch) qualifiers
          , Just (qualifyOwnedQubits insertion annotation)
          )
        else (qualifiers, Just annotation)
  where
    writtenOwnership : CanonicalAstNode QuantumStorageQualifier -> Maybe OwnershipInsertion
    writtenOwnership (MkAstNode keywordInfo _ keyword) =
      map (\ownership => MkOwnershipInsertion ownership DesugaredMovedQubitQualifier (Just keywordInfo.span))
          (storageOwnership keyword)

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

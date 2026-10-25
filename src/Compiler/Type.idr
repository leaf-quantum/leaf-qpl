module Compiler.Type

import Data.List1

import Frontend.ASTData
import Frontend.Token
import Frontend.Syntax.Common
import Frontend.Syntax.Operator

%default total

--------------------------------------------------------------------------------
-- Semantic Leaf types
--------------------------------------------------------------------------------
-- Unlike Frontend.Syntax.Type.TyNode, LeafType describes a checked type rather
-- than preserving how a type was written. In particular, named types refer to
-- resolved symbols and array lengths are evaluated natural numbers.
--------------------------------------------------------------------------------LeafNamed

public export
data LeafType
  = LeafPrimitive TypPrimName
  | LeafNamed SymbolId
  | LeafUnit
  | LeafTuple (List1 LeafType)
  | LeafArray LeafType Nat
  | LeafSlice LeafType
  | LeafReference BorrowKind LeafType
  | LeafFunction FunctionEffect (List LeafType) LeafType
  | LeafQualified OwnershipQualifier LeafType

--------------------------------------------------------------------------------
-- References
--------------------------------------------------------------------------------
-- A reference borrows its referent without owning it, so the referent of a
-- LeafReference holds no LeafQualified at an owned position: its qubits,
-- found through tuples, arrays and slices but not inside function types or
-- nested references (as in "Owned positions" in Frontend.Syntax.Type). A
-- borrow of a linear qubit and a borrow of an affine qubit then both have type
-- `&qubit`, and compare equal structurally. Build every LeafReference with
-- referenceTo to keep it so.
--------------------------------------------------------------------------------

||| A type without the ownership qualifiers at its owned positions.
export
withoutOwnership : LeafType -> LeafType
withoutOwnership leafType =
  case leafType of
    LeafQualified _ qualifiedType => qualifiedType
    LeafTuple elementTypes => LeafTuple (map recur elementTypes)
    LeafArray elementType arrayLength => LeafArray (recur elementType) arrayLength
    LeafSlice elementType => LeafSlice (recur elementType)
    _ => leafType
  where
    recur : LeafType -> LeafType
    recur nestedType = withoutOwnership (assert_smaller leafType nestedType)

||| The type of a reference to a value of the given type.
export
referenceTo : BorrowKind -> LeafType -> LeafType
referenceTo borrowKind referent = LeafReference borrowKind (withoutOwnership referent)

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
--------------------------------------------------------------------------------

public export
data LeafType
  = LeafPrimitiveType TypPrimName
  | LeafNamedType SymbolId
  | LeafUnitType
  | LeafTupleType (List1 LeafType)
  | LeafArrayType LeafType Nat
  | LeafSliceType LeafType
  | LeafRangeType LeafType
  | LeafReferenceType BorrowKind LeafType
  | LeafFunctionType FunctionEffect (List LeafType) LeafType
  | LeafQualifiedType QuantumMultiplicityQualifier LeafType
  | LeafNeverType     -- expressions that never finish: return, break, continue, loop with no break
                      -- none of them ever produce a value at the point where they appear: control jumps somewhere else

--------------------------------------------------------------------------------
-- References
--------------------------------------------------------------------------------
-- A reference borrows its referent without owning it, so the referent of a
-- LeafReferenceType holds no LeafQualifiedType at an owned position: its
-- qubits, found through tuples, arrays and slices but not inside function
-- types or nested references (as in "Owned positions" in
-- Frontend.Syntax.Type). A borrow of a linear qubit and a borrow of an affine
-- qubit then both have type `&qubit`, and compare equal structurally.
--------------------------------------------------------------------------------

export
removeMultiplicity : LeafType -> LeafType
removeMultiplicity leafType =
  case leafType of
    LeafQualifiedType _ qualifiedType => qualifiedType
    LeafTupleType elementTypes => LeafTupleType (map recur elementTypes)
    LeafArrayType elementType arrayLength => LeafArrayType (recur elementType) arrayLength
    LeafSliceType elementType => LeafSliceType (recur elementType)
    _ => leafType
  where
    recur : LeafType -> LeafType
    recur nestedType = removeMultiplicity (assert_smaller leafType nestedType)

export
quantumMultiplicityFreeReference : BorrowKind -> LeafType -> LeafType
quantumMultiplicityFreeReference borrowKind referent = LeafReferenceType borrowKind (removeMultiplicity referent)

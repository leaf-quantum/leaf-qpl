module Compiler.TypeChecker.Type

import Data.List1
import Data.String
import Derive.Prelude
import Language.Reflection

import Frontend.ASTData
import Frontend.Token
import Frontend.Syntax.Common
import Frontend.Syntax.Operator

%default total
%language ElabReflection

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

%runElab derive "LeafType" [Eq]

export
showLeafType : LeafType -> String
showLeafType ty =
  case ty of
    LeafPrimitiveType primitive => show primitive
    LeafNamedType (MkSymbolId symbolId) => "type#" ++ show symbolId
    LeafUnitType => "()"
    LeafTupleType (element ::: []) => "(" ++ recur element ++ ",)"
    LeafTupleType elements => "(" ++ joinBy ", " (map recur (forget elements)) ++ ")"
    LeafArrayType element count => "[" ++ recur element ++ "; " ++ show count ++ "]"
    LeafSliceType element => "[" ++ recur element ++ "]"
    LeafRangeType element => "Range<" ++ recur element ++ ">"
    LeafReferenceType SharedBorrow referent =>
      (case referent of
         LeafReferenceType _ _ => "& "
         _ => "&") ++ recur referent
    LeafReferenceType MutableBorrow referent => "&mut " ++ recur referent
    LeafFunctionType effect parameterTypes result =>
      show effect ++ " fn(" ++ joinBy ", " (map recur parameterTypes) ++ ") -> " ++ recur result
    LeafQualifiedType qualifier qualifiedType => show qualifier ++ " " ++ recur qualifiedType
    LeafNeverType => "!"
  where
    recur : LeafType -> String
    recur nestedType = showLeafType (assert_smaller ty nestedType)

public export
implementation Show LeafType where
  show = showLeafType

--------------------------------------------------------------------------------
-- References
--------------------------------------------------------------------------------
-- A reference borrows its referent without owning it, so the referent of a
-- LeafReferenceType holds no LeafQualifiedType at an owned position: its
-- qbits, found through tuples, arrays and slices but not inside function
-- types or nested references (as in "Owned positions" in
-- Frontend.Syntax.Type). A borrow of a linear qbit and a borrow of an affine
-- qbit then both have type `&qbit`, and compare equal structurally.
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

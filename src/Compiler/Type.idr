module Compiler.Type

import Data.List1

import Frontend.ASTData
import Frontend.QuantumProperties
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
  | LeafQualified QuantumStorageProperties LeafType

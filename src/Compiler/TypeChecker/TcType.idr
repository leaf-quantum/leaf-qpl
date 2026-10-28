module Compiler.TypeChecker.TcType

import Data.List1

import Compiler.Type
import Frontend.ASTData
import Frontend.Token
import Frontend.Syntax.Common
import Frontend.Syntax.Operator

%default total

--------------------------------------------------------------------------------
-- Checker-internal types
--------------------------------------------------------------------------------
-- TcType mirrors LeafType constructor for constructor, but may still contain
-- unknowns while a function body or const initializer is being checked: the
-- type of an unsuffixed literal (TcVariable) and the multiplicity of a
-- `qalloc` qbit (MultiplicityVariable). Writeback replaces every unknown,
-- by what unification fixed it to or by its default, and turns the TcType
-- into a LeafType. TypeTables hold only LeafType, so no unknown reaches
-- lowering.
--------------------------------------------------------------------------------

public export
data TcMultiplicity
  = KnownMultiplicity QuantumMultiplicityQualifier
  | MultiplicityVariable Nat                  -- μ: defaults to linear

public export
data TcType
  = TcPrimitiveType TypPrimName
  | TcNamedType SymbolId
  | TcUnitType
  | TcTupleType (List1 TcType)
  | TcArrayType TcType Nat
  | TcSliceType TcType
  | TcRangeType TcType
  | TcReferenceType BorrowKind TcType
  | TcFunctionType FunctionEffect (List SupportKind) (List TcType) TcType
  | TcQualifiedType TcMultiplicity TcType
  | TcNeverType
  | TcVariable Nat                            -- an unsuffixed literal's type, {integer} or {float}

public export
data LiteralKind
  = IntegerLiteral                            -- {integer}: any integer type or bit, defaults to i32
  | FloatLiteral                              -- {float}: f32, f64, angle32 or angle64, defaults to f64

-- What an inference variable stands for, keyed by its Nat in
-- InferenceState.variables. Type variables and multiplicity variables
-- share one numbering.
public export
data VariableState
  = OpenTypeVariable LiteralKind
  | FixedTypeVariable TcType
  | OpenMultiplicity
  | FixedMultiplicity QuantumMultiplicityQualifier

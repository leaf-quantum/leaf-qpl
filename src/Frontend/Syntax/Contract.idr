module Frontend.Syntax.Contract

import Data.List1
import Derive.Prelude
import Language.Reflection
import Frontend.ASTPhases

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Quantum contract clauses
--------------------------------------------------------------------------------
-- Preserves the requires/ensures annotations between a function signature and
-- its body, WITHOUT validating them:
--
--   requires clean(q)
--   requires basis([q1, q2], XX)
--   requires isolated(qs)
--   ensures separable([q1, q2])
--   ensures product([q1, q2], [q3, q4], qs)
--   ensures stabilized([q0, q1, q2], [+XXX, +ZZI, +IZZ])
--
-- Qbit arguments are ordinary EXPRESSIONS (a name `q1`, an array literal
-- `[q1, q2]`, an index `qs[2]`), so this module is parameterized over the
-- expression type exactly like TyNode's arraySizeExpr -- Decl.idr ties the
-- knot with the concrete Expr phase. Which expressions are ACCEPTABLE
-- contract arguments (lvalue-ish qbit designators, not arbitrary
-- computation) is a validation pass's check against the preserved spans.
--
-- Pauli strings: BY LANGUAGE RULING, contract Pauli strings use only the
-- single-letter alphabet I, X, Y, Z. That makes segmentation of a term like
-- ZZI trivial (one operator per character) and lets the AST store Pauli
-- strings DECODED rather than as raw text: a PauliStringNode is a non-empty
-- list of PauliOperator, so a malformed string ("XQZ") is UNREPRESENTABLE --
-- the parser rejects the bad character with its exact position. Nothing is
-- lost versus raw text: each operator prints as exactly one character, so
-- decoded strings round-trip verbatim.
--
-- (Lexically, XX and ZZI arrive as plain identifier tokens and +XXX as a
-- plus symbol followed by an identifier; the parser reinterprets them in
-- contract position.
--
-- Deliberately representable, rejected later:
--   * Pauli string length vs. qbit count      (basis([q1, q2], XXX))
--   * ensures preceding requires               (spec: requires come first)
--   * non-designator argument expressions      (clean(1 + 2))
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Pauli operators, strings, and signed stabilizer terms
--------------------------------------------------------------------------------

-- One single-qbit Pauli operator, as ruled: I, X, Y, Z only.
public export
data PauliOperator
  = PauliI
  | PauliX
  | PauliY
  | PauliZ

%runElab derive "PauliOperator" [Eq]

public export
showPauliOperatorLeaf : PauliOperator -> String
showPauliOperatorLeaf p =
  case p of
    PauliI => "I"
    PauliX => "X"
    PauliY => "Y"
    PauliZ => "Z"

public export
implementation Show PauliOperator where
  show = showPauliOperatorLeaf

-- The single authoritative character classification, for the parser
-- production that decodes an identifier token into a Pauli string.
public export
pauliOperatorFromChar : Char -> Maybe PauliOperator
pauliOperatorFromChar c =
  case c of
    'I' => Just PauliI
    'X' => Just PauliX
    'Y' => Just PauliY
    'Z' => Just PauliZ
    _   => Nothing

-- A Pauli string as written: X, XX, ZZI, XYZ. Decoded and non-empty; the
-- written spelling is recovered exactly by concatenating the operators'
-- one-character spellings. Phase-invariant payload -- no phase ever
-- rewrites a decoded Pauli string.
public export
record PauliStringNode where
  constructor MkPauliStringNode
  pauliOperators : List1 PauliOperator

public export
PauliString : AstPhase -> Type
PauliString phase = AstNode phase PauliStringNode

public export
SurfacePauliString : Type
SurfacePauliString = PauliString SurfaceAstPhase

-- The sign of a stabilizer term. MANDATORY, because the spec writes it on
-- every term ([ +ZI, -ZZ ], [ -Z ]); if unsigned terms defaulting to + are
-- ever ruled legal, this field on SignedPauliTermNode becomes a Maybe.
public export
data StabilizerSign
  = StabilizerPlus   -- +
  | StabilizerMinus  -- -

%runElab derive "StabilizerSign" [Eq]

-- One signed stabilizer term: +XXX, -ZZ. The sign is stored plain (the
-- term's own span starts at the sign character); the Pauli string is
-- located so length-mismatch diagnostics can point at it precisely.
public export
record SignedPauliTermNode (phase : AstPhase) where
  constructor MkSignedPauliTermNode
  stabilizerSign  : StabilizerSign
  stabilizerPauli : PauliString phase

public export
SignedPauliTerm : AstPhase -> Type
SignedPauliTerm phase = AstNode phase (SignedPauliTermNode phase)

public export
SurfaceSignedPauliTerm : Type
SurfaceSignedPauliTerm = SignedPauliTerm SurfaceAstPhase

--------------------------------------------------------------------------------
-- Contract predicates
--------------------------------------------------------------------------------
-- The six predicate forms, each with its own correctly-shaped argument list.
-- `expr` is the (located) expression type, supplied by Decl.idr; `phase`
-- indexes the located children defined in THIS module (Pauli strings,
-- stabilizer terms).
--------------------------------------------------------------------------------

public export
data ContractPredicateNode : (phase : AstPhase) -> (expr : Type) -> Type where

  -- clean(q) / clean([q1, q2]) -- qbits in |0>, separated from the rest.
  ContractClean :
       (qbitArgument : expr)
    -> ContractPredicateNode phase expr

  -- basis(q1, X) / basis([q1, q2], XX) -- separable eigenstate of the
  -- given Pauli string, separated from the rest.
  ContractBasis :
       (qbitArgument : expr)
    -> (pauliString   : PauliString phase)
    -> ContractPredicateNode phase expr

  -- separable(qs) -- not entangled among themselves, separated from rest.
  ContractSeparable :
       (qbitArgument : expr)
    -> ContractPredicateNode phase expr

  -- isolated(qs) -- not entangled with the REST of the program, though
  -- possibly entangled among themselves.
  ContractIsolated :
       (qbitArgument : expr)
    -> ContractPredicateNode phase expr

  -- product(q1, q2, qs) / product([q1, q2], [q3, q4], qs) -- the given
  -- qbit sets are mutually unentangled. Product is a relation between AT
  -- LEAST TWO sets, and the first + List1 shape encodes exactly that:
  -- a one-argument product(x) is unrepresentable.
  ContractProduct :
       (firstQbitSet  : expr)
    -> (otherQbitSets : List1 expr)
    -> ContractPredicateNode phase expr

  -- stabilized(qs, [ +ZI, -ZZ ]) -- exact stabilizer state. At least one
  -- stabilizer term (an empty bracket list would assert nothing). Note the
  -- bracket list is contract-specific syntax parsed by a dedicated
  -- production, NOT an ordinary array-literal expression: +ZI is not an
  -- expression.
  ContractStabilized :
       (qbitArgument   : expr)
    -> (stabilizerTerms : List1 (SignedPauliTerm phase))
    -> ContractPredicateNode phase expr

-- The regular AST-wrapped predicate. In addition to the predicate payload,
-- this carries its node ID, source span, and phase metadata.
public export
ContractPredicate : (phase : AstPhase) -> (expr : Type) -> Type
ContractPredicate phase expr =
  AstNode phase (ContractPredicateNode phase expr)

--------------------------------------------------------------------------------
-- Contract clauses
--------------------------------------------------------------------------------
-- requires <predicate> / ensures <predicate>. A function declaration stores
-- `List` of located clauses IN SOURCE ORDER: the spec's rule that requires
-- clauses precede ensures clauses is a validation check (with the offending
-- clause's span), not an AST shape -- encoding it as two separate lists
-- would erase the written interleaving that the diagnostic needs to show.
--------------------------------------------------------------------------------

public export
data ContractClauseNode : (phase : AstPhase) -> (expr : Type) -> Type where

  RequiresClause :
       (predicate : ContractPredicate phase expr)
    -> ContractClauseNode phase expr

  EnsuresClause :
       (predicate : ContractPredicate phase expr)
    -> ContractClauseNode phase expr

-- The regular AST-wrapped clause. In addition to the clause payload, this
-- carries its node ID, source span, and phase metadata.
public export
ContractClause : (phase : AstPhase) -> (expr : Type) -> Type
ContractClause phase expr = AstNode phase (ContractClauseNode phase expr)

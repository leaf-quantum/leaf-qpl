module Frontend.Syntax.Operator

import Derive.Prelude
import Language.Reflection

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Operator vocabulary
--------------------------------------------------------------------------------
-- Centralizes the operator names used by expression, assignment, and type
-- nodes. These are VOCABULARY, not located AST nodes: an operator by itself
-- has no phase-dependent content, so there are no SurfaceAstPhase/CanonicalAstPhase/...
-- wrappers here. If a diagnostic needs to point at the operator itself
-- ("cannot apply `+` to operands of type `qbit`"), the owning expression
-- node should carry the operator's SourceSpan alongside the operator value --
-- that decision belongs to Expr.idr / Stmt.idr, not here.
--
-- Each enum comes with a `show...Leaf` function giving the exact source
-- spelling, following the Token.idr convention, so diagnostics can quote the
-- operator as written. There are no `fromString` inverses: operators are
-- recognized by the parser from `Symbol` tokens (via its precedence table),
-- never from strings. Precedence and associativity are likewise parser
-- concerns and deliberately absent from this module.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Borrows
--------------------------------------------------------------------------------

public export
data BorrowKind
  = SharedBorrow   -- &x
  | MutableBorrow  -- &mut x

%runElab derive "BorrowKind" [Eq]

public export
showBorrowKindLeaf : BorrowKind -> String
showBorrowKindLeaf b =
  case b of
    SharedBorrow  => "&"
    MutableBorrow => "&mut"

public export
implementation Show BorrowKind where
  show = showBorrowKindLeaf

--------------------------------------------------------------------------------
-- Unary operators
--------------------------------------------------------------------------------

public export
data UnaryOperator
  = UnaryNegate             -- -x
  | UnaryLogicalNot         -- !x   (spec shows `!` only on booleans; if a
                            --       bitwise-not reading is ever added, it is
                            --       an overload resolved later, not a new
                            --       surface operator)
  | UnaryBorrow BorrowKind  -- &x / &mut x

%runElab derive "UnaryOperator" [Eq]

public export
showUnaryOperatorLeaf : UnaryOperator -> String
showUnaryOperatorLeaf op =
  case op of
    UnaryNegate     => "-"
    UnaryLogicalNot => "!"
    UnaryBorrow b   => showBorrowKindLeaf b

public export
implementation Show UnaryOperator where
  show = showUnaryOperatorLeaf

--------------------------------------------------------------------------------
-- Binary operators
--------------------------------------------------------------------------------
-- Everything that appears between two expressions, EXCEPT:
--   * ranges (.. / ..=)      -- see RangeOperator; range endpoints are
--                               optional (a.., ..5, ..), which no ordinary
--                               binary node can express
--   * `as` casts             -- right operand is a TYPE, not an expression;
--                               Expr.idr gives casts their own node
--   * `.tensor(...)` etc.    -- method-call syntax, not an operator
--
-- Note `+`, `-`, `*` also build qstate expressions
-- (zero - phase(turns(1.0/3.0)) * one); surface-syntactically they are the
-- same operators, and the quantum reading is a typing concern.
--------------------------------------------------------------------------------

public export
data BinaryOperator
  = BinaryAdd           -- +
  | BinarySubtract      -- -
  | BinaryMultiply      -- *
  | BinaryDivide        -- /
  | BinaryRemainder     -- %
  | BinaryEqual         -- ==
  | BinaryNotEqual      -- !=
  | BinaryGreater       -- >
  | BinaryGreaterEqual  -- >=
  | BinaryLess          -- <
  | BinaryLessEqual     -- <=
  | BinaryLogicalAnd    -- &&
  | BinaryLogicalOr     -- ||
  | BinaryBitAnd        -- &
  | BinaryBitOr         -- |
  | BinaryBitXor        -- ^
  | BinaryShiftLeft     -- <<
  | BinaryShiftRight    -- >>

%runElab derive "BinaryOperator" [Eq]

public export
showBinaryOperatorLeaf : BinaryOperator -> String
showBinaryOperatorLeaf op =
  case op of
    BinaryAdd          => "+"
    BinarySubtract     => "-"
    BinaryMultiply     => "*"
    BinaryDivide       => "/"
    BinaryRemainder    => "%"
    BinaryEqual        => "=="
    BinaryNotEqual     => "!="
    BinaryGreater      => ">"
    BinaryGreaterEqual => ">="
    BinaryLess         => "<"
    BinaryLessEqual    => "<="
    BinaryLogicalAnd   => "&&"
    BinaryLogicalOr    => "||"
    BinaryBitAnd       => "&"
    BinaryBitOr        => "|"
    BinaryBitXor       => "^"
    BinaryShiftLeft    => "<<"
    BinaryShiftRight   => ">>"

public export
implementation Show BinaryOperator where
  show = showBinaryOperatorLeaf

--------------------------------------------------------------------------------
-- Assignment operators
--------------------------------------------------------------------------------
-- Operators of assignment STATEMENTS (x = 5; x += 1; x <<= 1; ...), used
-- together with an assignment-target node in Stmt.idr.
--
-- Compound assignments are preserved as themselves in the surface AST; the
-- rewrite of `x += e` into `x = x + e` is canonical-phase desugaring
-- (CompoundAssignmentDesugar in Common.idr), not a parsing step.
--------------------------------------------------------------------------------

public export
data AssignmentOperator
  = AssignValue       -- =
  | AssignAdd         -- +=
  | AssignSubtract    -- -=
  | AssignMultiply    -- *=
  | AssignDivide      -- /=
  | AssignRemainder   -- %=
  | AssignBitAnd      -- &=
  | AssignBitOr       -- |=
  | AssignBitXor      -- ^=
  | AssignShiftLeft   -- <<=
  | AssignShiftRight  -- >>=

%runElab derive "AssignmentOperator" [Eq]

public export
showAssignmentOperatorLeaf : AssignmentOperator -> String
showAssignmentOperatorLeaf op =
  case op of
    AssignValue      => "="
    AssignAdd        => "+="
    AssignSubtract   => "-="
    AssignMultiply   => "*="
    AssignDivide     => "/="
    AssignRemainder  => "%="
    AssignBitAnd     => "&="
    AssignBitOr      => "|="
    AssignBitXor     => "^="
    AssignShiftLeft  => "<<="
    AssignShiftRight => ">>="

public export
implementation Show AssignmentOperator where
  show = showAssignmentOperatorLeaf

--------------------------------------------------------------------------------
-- Let-binding operators
--------------------------------------------------------------------------------
-- The operator between a let-binder and its initializer:
--
--   let q: qbit = f(q);    -- ordinary binding
--   let q: qbit := f(q);   -- := marks the binding for AUTOMATIC UNCOMPUTATION
--                           -- when the enclosing function returns
--
-- `:=` is deliberately NOT an AssignmentOperator: it is legal only in `let`
-- bindings, never in assignment statements (there is no `x := e;`), and it
-- changes the binding's semantics rather than performing a different
-- operation. Keeping it in a separate two-value enum lets the Let node in
-- Stmt.idr require exactly one of these two markers, and makes `x := 5;`
-- unrepresentable as an assignment statement by construction.
--------------------------------------------------------------------------------

public export
data LetBindingOperator
  = LetBindEquals         -- =
  | LetBindAutoUncompute  -- :=

%runElab derive "LetBindingOperator" [Eq]

public export
showLetBindingOperatorLeaf : LetBindingOperator -> String
showLetBindingOperatorLeaf op =
  case op of
    LetBindEquals        => "="
    LetBindAutoUncompute => ":="

public export
implementation Show LetBindingOperator where
  show = showLetBindingOperatorLeaf

--------------------------------------------------------------------------------
-- Range operators
--------------------------------------------------------------------------------
-- Distinguishes only inclusive vs. exclusive. The optionality of the
-- endpoints (a..b, a.., ..b, ..=b, ..) is represented on the range
-- EXPRESSION node in Expr.idr as `Maybe` start / `Maybe` end -- the operator
-- itself is the same `..` in `1..6` and in a bare `..`.
--
-- (`..= ` with no end, i.e. `a..=`, is not valid source; that is a parser
-- rejection, not an AST-level impossibility.)
--------------------------------------------------------------------------------

public export
data RangeOperator
  = RangeExclusive  -- ..
  | RangeInclusive  -- ..=

%runElab derive "RangeOperator" [Eq]

public export
showRangeOperatorLeaf : RangeOperator -> String
showRangeOperatorLeaf op =
  case op of
    RangeExclusive => ".."
    RangeInclusive => "..="

public export
implementation Show RangeOperator where
  show = showRangeOperatorLeaf
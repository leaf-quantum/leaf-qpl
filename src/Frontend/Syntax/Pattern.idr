module Frontend.Syntax.Pattern

import Data.List1
import Frontend.ASTPhases
import Frontend.Syntax.Common
import Frontend.Syntax.Literal
import Frontend.Syntax.Name

%default total

--------------------------------------------------------------------------------
-- Patterns
--------------------------------------------------------------------------------
-- Two SEPARATE pattern grammars live here:
--
--   1. PatternNode -- classical patterns, used by `let` binders, function
--      parameters, destructuring, and classical `match` arms.
--   2. QuantumMatchPatternNode -- the much smaller grammar of qmatch/smatch
--      arms. Deliberately NOT a reuse of PatternNode: quantum match arms
--      admit only basis strings, integers, wildcard, and qenum variants,
--      and reusing the classical type would make `qmatch x { (a, b) => .. }`
--      representable for every later pass to defend against.
--
-- This module depends on Literal and Name but NOT on Expr -- deliberately:
--
--   * Match GUARDS (`n if n > 0`) are expressions, so they live on the match
--     ARM (in Expr.idr), not inside the pattern. The guard belongs to the
--     arm anyway: it conditions the whole arm, it is not part of what the
--     scrutinee is matched against.
--   * There are no range patterns and no const-expression patterns in the
--     spec, so nothing else drags Expr in.
--
-- Consequently PatternNode needs no `arraySizeExpr`-style parameter, and the
-- concrete SurfacePattern alias can be defined right here.
--
-- Both grammars are recursive (or reference located children), so they are
-- indexed by `phase : AstPhase` -- the RECURSIVE occurrences are wrapped in
-- the concrete `AstNode phase`, which is strictly positive (see Type.idr's
-- header for why this differs from the abstract-wrapper construction that
-- does NOT typecheck).
--
-- Deliberately REPRESENTABLE here, rejected by later passes with good spans:
--
--   * non-exhaustive / overlapping matches         -- semantic
--   * binding the same name twice in one pattern   -- semantic
--   * struct pattern naming a nonexistent field    -- resolution
--
-- Deliberately NOT representable (parser rejections pending a language
-- ruling, since the spec never shows them):
--
--   * negative literal patterns    `-1 => ...`   (guards cover the use case)
--   * range patterns               `1..=5 => ...`
--   * rest patterns                `[first, .., last]`, `Point { x, .. }`
--
-- If any of these are ruled legal Leaf, PatternNode grows a constructor; the
-- omission is tracking the spec, not forgetting Rust.
--------------------------------------------------------------------------------

mutual

  public export
  data PatternNode : (phase : AstPhase) -> Type where

    -- The wildcard `_`: matches anything, binds nothing.
    --   let (x, _, z) = (1, 2, 3);
    PatternWildcard :
         PatternNode phase

    -- A single-identifier pattern, optionally `mut`:
    --   let q = ...          let mut x = ...          fn f(mut x: i32)
    --
    -- Mutability is stored plain (not located): when `mut` is written, the
    -- pattern's own span starts at the `mut` keyword, so no separate span is
    -- needed to point at it.
    --
    -- PARSER RULE, not an AST rule: a lone identifier is ALWAYS PatternName.
    -- Resolution distinguishes new bindings from references to constants.
    -- An immutable constant name becomes a single-segment resolved PatternPath.
    -- Quantum storage qualifiers (`let scratch linear q = ...`) do NOT live
    -- here: the spec only ever writes them directly after `let`, so they
    -- belong to the Let statement node, applying to its whole binder.
    PatternName :
         (mutability  : Maybe Mutability)
      -> (binderName  : Name phase)
      -> PatternNode phase

    -- A path pattern: unit enum variants and
    -- named constants:
    --   ResultBit::Zero => ...
    -- The parser only puts multi-segment paths here (single identifiers are
    -- PatternName). Resolution also puts bare constant names here. What the path denotes --
    -- variant vs. constant -- is resolution's job.
    PatternPath :
         (valuePath : Path phase)
      -> PatternNode phase

    -- A literal pattern:
    --   1 => ...     true => ...     bs"01" is NOT here (quantum grammar)
    -- Note `()` as a pattern (`let () = f();`) is simply
    -- PatternLiteral of LiteralUnit -- no separate constructor, consistent
    -- with `()` being the unit value everywhere.
    PatternLiteral :
         (literal : Literal phase)
      -> PatternNode phase

    -- A parenthesized pattern `(p)`. Explicit for the same reason as
    -- TyParenthesized / the planned ExprParenthesized: Leaf has one-element
    -- tuple patterns `(p,)`, so `(p)` vs `(p,)` is a one-token distinction
    -- diagnostics must be able to see. Discarded during canonicalization.
    PatternParenthesized :
         (innerPattern : AstNode phase (PatternNode phase))
      -> PatternNode phase

    -- Tuple pattern with AT LEAST one element:
    --   let (a, _, c) = (1, 2, 3);         let (q,) = ...;
    -- The List1 shape keeps `()` unrepresentable as an empty tuple pattern
    -- (that source form is PatternLiteral LiteralUnit).
    PatternTuple :
         (elementPatterns : List1 (AstNode phase (PatternNode phase)))
      -> PatternNode phase

    -- Array pattern:
    --   let [b0, b1, b2] = measr(qs);
    -- Plain List: `[]` is legitimate syntax (matching a [T; 0]), however
    -- rarely useful.
    PatternArray :
         (elementPatterns : List (AstNode phase (PatternNode phase)))
      -> PatternNode phase

    -- Struct pattern, which also covers STRUCT-LIKE ENUM VARIANTS
    -- (the path distinguishes them only after resolution):
    --   let Pair { q0: q3, q1: q4 } = mypair;
    --   Message::Move { x, y } => ...
    PatternStruct :
         (structPath    : Path phase)
      -> (fieldPatterns : List (AstNode phase (StructPatternFieldNode phase)))
      -> PatternNode phase

    -- Tuple-like enum/qenum variant pattern:
    --   Data::Left(a) => ...        Data::Right(b, c) => ...
    -- Arguments are full patterns, so nesting (Data::Left((a, b))) is
    -- representable; whether the arity matches the declaration is checked
    -- after resolution.
    PatternEnumTuple :
         (variantPath      : Path phase)
      -> (argumentPatterns : List (AstNode phase (PatternNode phase)))
      -> PatternNode phase

  -- One field inside a struct pattern. The shorthand/explicit split is the
  -- pattern-side mirror of the FieldInit split on struct EXPRESSIONS:
  --
  --   Pair { q0, q1 }            -- shorthand: field name IS the binder
  --   Pair { q0: q3, q1: q4 }    -- explicit: field q0 matched against a
  --                              --   full subpattern (here a binder q3,
  --                              --   but any pattern is allowed:
  --                              --   Point { x: 0, y })
  --
  -- `mut` is only meaningful on the shorthand form (the explicit form puts
  -- any mutability on the subpattern's own binders), which the two shapes
  -- encode exactly.
  public export
  data StructPatternFieldNode : (phase : AstPhase) -> Type where

    StructPatternFieldShorthand :
         (mutability : Maybe Mutability) -- Nothing for { x }; Just Mutable for { mut x }.
      -> (fieldAndBinderName : Name phase)
      -> StructPatternFieldNode phase

    StructPatternFieldExplicit :
         (fieldName    : Name phase)
      -> (fieldPattern : AstNode phase (PatternNode phase))
      -> StructPatternFieldNode phase

public export
Pattern : AstPhase -> Type
Pattern phase = AstNode phase (PatternNode phase)

public export
SurfacePattern : Type
SurfacePattern = Pattern SurfaceAstPhase

public export
CanonicalPattern : Type
CanonicalPattern = Pattern CanonicalAstPhase

public export
ResolvedPattern : Type
ResolvedPattern = Pattern ResolvedAstPhase

public export
TypedPattern : Type
TypedPattern = Pattern TypedAstPhase

public export
StructPatternField : AstPhase -> Type
StructPatternField phase = AstNode phase (StructPatternFieldNode phase)

public export
SurfaceStructPatternField : Type
SurfaceStructPatternField = StructPatternField SurfaceAstPhase

public export
CanonicalStructPatternField : Type
CanonicalStructPatternField = StructPatternField CanonicalAstPhase

public export
ResolvedStructPatternField : Type
ResolvedStructPatternField = StructPatternField ResolvedAstPhase

public export
TypedStructPatternField : Type
TypedStructPatternField = StructPatternField TypedAstPhase

--------------------------------------------------------------------------------
-- Quantum match patterns (qmatch / smatch)
--------------------------------------------------------------------------------
-- The arm grammar of qmatch and smatch:
--
--   qmatch qs {                      smatch &qs {
--     bs"00" => f00(q1, q2, q3),       bs"00" => state_expression_00(data),
--     0      => ...,                   0      => ...,
--     _      => f(),                   -- no wildcard in smatch
--   }
--   qmatch x {
--     Data::Left(a)     => ...,        -- qenum variants: qmatch only
--     Data::Right(b, c) => ...,
--   }
--
-- ONE shared type for both constructs; the per-construct restrictions are
-- PARSER-enforced subsets:
--
--   * smatch never constructs QuantumPatternWildcard (the spec forbids
--     wildcards there -- no `_` token even appears in valid smatch source,
--     so this is a parse error with a perfect span, not a deferred check)
--   * smatch never constructs QuantumPatternQenumVariant (smatch scrutinees
--     are qbits/registers, not qenums)
--   * "no mixing bs-strings with integers in one qmatch/smatch" is also the
--     parser's (or an early validator's) check -- the AST does not encode
--     arm-set homogeneity
--
-- Two types instead of one would state those subsets in the AST itself, at
-- the price of duplicating the basis/integer constructors; since the
-- forbidden forms are unlexable-in-context anyway, the shared type wins.
--
-- Raw spellings are preserved (bs"01" as written, integers as written),
-- consistent with Literal.idr; validating basis characters and decoding
-- integers happens later.
--------------------------------------------------------------------------------

public export
data QuantumMatchPatternNode : (phase : AstPhase) -> Type where

  -- bs"00", bs"0+", bs"1-", ... raw spelling including the bs"..." wrapper.
  QuantumPatternBasisStringRaw :
       (rawSpelling : String)
    -> QuantumMatchPatternNode phase

  -- 0, 1, 2, 3, ... raw spelling; equivalent to the basis string of the
  -- integer's binary expansion (a later pass makes that precise).
  QuantumPatternIntegerRaw :
       (rawSpelling : String)
    -> QuantumMatchPatternNode phase

  -- `_` -- qmatch only; smatch construction sites never populate this.
  QuantumPatternWildcard :
       QuantumMatchPatternNode phase

  -- Data::Left(a), Data::Right(b, c) -- qmatch over a qenum. Arguments are
  -- plain BINDER NAMES, not nested patterns: that is all the spec shows,
  -- and qenum payloads are qbits, which deeper patterns could not usefully
  -- destructure anyway. If nested destructuring is ever ruled legal, this
  -- becomes List (Pattern phase).
  QuantumPatternQenumVariant :
       (variantPath : Path phase)
    -> (binderNames : List (Name phase))
    -> QuantumMatchPatternNode phase

public export
QuantumMatchPattern : AstPhase -> Type
QuantumMatchPattern phase = AstNode phase (QuantumMatchPatternNode phase)

public export
SurfaceQuantumMatchPattern : Type
SurfaceQuantumMatchPattern = QuantumMatchPattern SurfaceAstPhase

public export
CanonicalQuantumMatchPattern : Type
CanonicalQuantumMatchPattern = QuantumMatchPattern CanonicalAstPhase

public export
ResolvedQuantumMatchPattern : Type
ResolvedQuantumMatchPattern = QuantumMatchPattern ResolvedAstPhase

public export
TypedQuantumMatchPattern : Type
TypedQuantumMatchPattern = QuantumMatchPattern TypedAstPhase

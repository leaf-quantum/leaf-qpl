module Frontend.Syntax.Common

import Derive.Prelude
import Language.Reflection

%default total
%language ElabReflection

---------------------------------------------------------------------------------
--- Shared syntax enums
 --------------------------------------------------------------------------------
--- Small enums used across declarations, parameters, types, and let-bindings.
---
--- Each enum carries a `show...Leaf` source-spelling function in the
--- Token.idr style, so diagnostics quote exactly what the user wrote.
---------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Visibility qualifier
--------------------------------------------------------------------------------

public export
data VisibilityQualifier = VisibilityPublic

%runElab derive "VisibilityQualifier" [Eq]

public export
showVisibilityQualifierLeaf : VisibilityQualifier -> String
showVisibilityQualifierLeaf v = "pub"

public export
implementation Show VisibilityQualifier where
  show = showVisibilityQualifierLeaf

--------------------------------------------------------------------------------
-- Function constness
--
-- The optional `const` qualifier written before `fn`.
--------------------------------------------------------------------------------

public export
data FunctionConstness = ConstFunction

%runElab derive "FunctionConstness" [Eq]

public export
showFunctionConstnessLeaf : FunctionConstness -> String
showFunctionConstnessLeaf ConstFunction = "const"

public export
implementation Show FunctionConstness where
  show = showFunctionConstnessLeaf

--------------------------------------------------------------------------------
-- Mutability
--------------------------------------------------------------------------------
-- Whether a BINDING is marked `mut`:
--
--   let mut x = 0;
--   fn f(mut x: i32) -> i32 { ... }
--
-- Note mutability (&T vs. &mut T) is NOT this type: that is BorrowKind in
-- Operator.idr, kept separate because the two occupy different grammatical
-- positions and Leaf's qubit rules treat them differently.
--------------------------------------------------------------------------------

public export
data Mutability = Mutable

%runElab derive "Mutability" [Eq]

public export
showMutabilityLeaf : Mutability -> String
showMutabilityLeaf Mutable = "mut"

public export
implementation Show Mutability where
  show = showMutabilityLeaf

--------------------------------------------------------------------------------
-- Function effects
--------------------------------------------------------------------------------
-- The optional effect qualifier written before `fn`:
--
--   classical fn f(x: i32) -> i32 { ... }
--   unitary fn had(q: qubit) -> qubit { ... }
--------------------------------------------------------------------------------

public export
data FunctionEffect
  = EffectClassical   -- no quantum operations
  | EffectUncompsafe  -- only uncomputation-safe quantum operations
  | EffectUnitary     -- unitary; #outputs == #inputs
  | EffectIsometry    -- unitary; #outputs >  #inputs
  | EffectCoisometry  -- unitary; #outputs <  #inputs
  | EffectGeneral     -- may measure / reset / discard (the default)

%runElab derive "FunctionEffect" [Eq]

public export
showFunctionEffectLeaf : FunctionEffect -> String
showFunctionEffectLeaf e =
  case e of
    EffectClassical  => "classical"
    EffectUncompsafe => "uncompsafe"
    EffectUnitary    => "unitary"
    EffectIsometry   => "isometry"
    EffectCoisometry => "coisometry"
    EffectGeneral    => "general"

public export
implementation Show FunctionEffect where
  show = showFunctionEffectLeaf

--------------------------------------------------------------------------------
-- Support clauses
--------------------------------------------------------------------------------
-- The kinds that may appear after `supports` in a function signature:
--
--   unitary fn f(q: &qubit) supports adjoint, ctrl { ... }
--
-- A declaration stores the written clause as a list of these, in source
-- order. (Lexically, `adjoint` arrives as a keyword token and `ctrl` as a
-- builtin token; that asymmetry is the parser's problem, not the AST's.)
--------------------------------------------------------------------------------

public export
data SupportKind
  = SupportAdjoint  -- supports adjoint
  | SupportCtrl     -- supports ctrl

%runElab derive "SupportKind" [Eq]

public export
showSupportKindLeaf : SupportKind -> String
showSupportKindLeaf s =
  case s of
    SupportAdjoint => "adjoint"
    SupportCtrl    => "ctrl"

public export
implementation Show SupportKind where
  show = showSupportKindLeaf

--------------------------------------------------------------------------------
-- Quantum storage qualifiers
--------------------------------------------------------------------------------
-- The qualifiers that may appear between `let` and the binder:
--
--   let linear q: qubit = qalloc();
--   let affine q: qubit = qalloc();
--   let scratch q: qubit = qalloc();
--   let scratch linear qs: [qubit; 2] = qalloc(2);
--   let linear scratch q: qubit = qalloc();
--
-- Binders store `List QuantumStorageQualifier` IN SOURCE ORDER, so
-- `scratch linear` and `linear scratch` round-trip differently even though
-- they mean the same thing. 
--------------------------------------------------------------------------------

public export
data QuantumStorageQualifier
  = QualifierLinear   -- consume exactly once; discard must be explicit
  | QualifierAffine   -- consume at most once; implicit discard allowed
  | QualifierScratch  -- auto-uncomputed and reclaimed at end of scope

%runElab derive "QuantumStorageQualifier" [Eq]

public export
showQuantumStorageQualifierLeaf : QuantumStorageQualifier -> String
showQuantumStorageQualifierLeaf q =
  case q of
    QualifierLinear  => "linear"
    QualifierAffine  => "affine"
    QualifierScratch => "scratch"

public export
implementation Show QuantumStorageQualifier where
  show = showQuantumStorageQualifierLeaf

--------------------------------------------------------------------------------
-- Quantum multiplicity qualifiers
--------------------------------------------------------------------------------
-- The single qualifier that may be written inside a TYPE:
--
--   fn maybe_drop(q: affine qubit) { ... }
--   oracle: unitary fn(q: linear qubit) -> qubit
--
-- `scratch` is deliberately absent: it describes cleanup at the end of a
-- binding's scope, so it is only valid on `let` bindings (see
-- QuantumStorageQualifier above). At most one multiplicity qualifier can be
-- written, so a qualified type holds exactly one of these.
--------------------------------------------------------------------------------

public export
data QuantumMultiplicityQualifier
  = QuantumMultiplicityLinear   -- consume exactly once; discard must be explicit
  | QuantumMultiplicityAffine   -- consume at most once; implicit discard allowed

%runElab derive "QuantumMultiplicityQualifier" [Eq]

public export
showQuantumMultiplicityQualifierLeaf : QuantumMultiplicityQualifier -> String
showQuantumMultiplicityQualifierLeaf q =
  case q of
    QuantumMultiplicityLinear => "linear"
    QuantumMultiplicityAffine => "affine"

public export
implementation Show QuantumMultiplicityQualifier where
  show = showQuantumMultiplicityQualifierLeaf

||| The multiplicity a storage qualifier denotes; `scratch` denotes none.
public export
storageMultiplicity : QuantumStorageQualifier -> Maybe QuantumMultiplicityQualifier
storageMultiplicity QualifierLinear  = Just QuantumMultiplicityLinear
storageMultiplicity QualifierAffine  = Just QuantumMultiplicityAffine
storageMultiplicity QualifierScratch = Nothing

--------------------------------------------------------------------------------
-- Initializer markers
--------------------------------------------------------------------------------
-- The operator between a let-binder and its initializer:
--
--   let q: qubit = f(q);    -- ordinary binding
--   let q: qubit := f(q);   -- := marks the binding for AUTOMATIC
--                           -- UNCOMPUTATION when the enclosing fn returns
--
-- `:=` is deliberately NOT an AssignmentOperator (Operator.idr): it is legal
-- only in `let` bindings, never in assignment statements (there is no
-- `x := e;`), and it changes the binding's semantics rather than performing
-- a different operation. The Let node requires exactly one of these two
-- markers whenever an initializer is present, which makes `x := 5;`
-- unrepresentable as an assignment statement by construction.
--------------------------------------------------------------------------------

public export
data InitializerMarker
  = InitializerEquals         -- =
  | InitializerAutoUncompute  -- :=

%runElab derive "InitializerMarker" [Eq]

public export
showInitializerMarkerLeaf : InitializerMarker -> String
showInitializerMarkerLeaf m =
  case m of
    InitializerEquals        => "="
    InitializerAutoUncompute => ":="

public export
implementation Show InitializerMarker where
  show = showInitializerMarkerLeaf

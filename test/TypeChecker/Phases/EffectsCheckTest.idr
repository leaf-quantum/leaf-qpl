module TypeChecker.Phases.EffectsCheckTest

import Test.Simple

import Compiler.TypeChecker.Data
import Frontend.Syntax.Common
import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Pass E: effects, capabilities and constness
--------------------------------------------------------------------------------
-- Pass E checks each function's declared effect against its signature and
-- against every operation in its body, carrying an effect ceiling into
-- adjoint blocks, control blocks and `:=` initializers (plan §7). Widths count
-- owned qubits; a width error reports the parameters' width, then the
-- result's, at the function name. Quantum data in a classical signature, and
-- a quantum operation under a classical ceiling, report `uncompsafe`, the
-- least effect that admits quantum data. An operation error points at the
-- operation; a capability error at the callable; an attribute error at the
-- attribute's name.
--------------------------------------------------------------------------------

-- Signature claims (plan §7.1)
signatureClaimTests : List ETest
signatureClaimTests = Test.do
  test "a unitary function returns as many owned qubits as it takes" $
    typeCheckOutcome "unitary fn f(q: qbit) -> qbit { H(q) }" `shouldBe` accepted

  test "a unitary function cannot return more owned qubits than it takes" $
    typeCheckOutcome "unitary fn f(q: qbit) -> (qbit, qbit) { (q, qalloc()) }"
      `shouldBe` rejectedWith (QuantumWidthMismatch "unitary" 1 2 (spanAt 1 12))

  test "an uncompsafe function cannot return more owned qubits than it takes" $
    typeCheckOutcome "uncompsafe fn f(q: qbit) -> (qbit, qbit) { (X(q), qalloc()) }"
      `shouldBe` rejectedWith (QuantumWidthMismatch "uncompsafe" 1 2 (spanAt 1 15))

  test "an isometry returns more owned qubits than it takes" $
    typeCheckOutcome "isometry fn f(qs: [qbit; 2]) -> [qbit; 4] { let q1 = X(qs[0]); let q2 = H(qs[1]); let q3 = qalloc(); let q4 = qalloc(); let q3 = X(q3); let (q3, q4) = CX(q3, q4); [q1, q2, q3, q4] }"
      `shouldBe` accepted

  test "an isometry may allocate the qubits it returns" $
    typeCheckOutcome "isometry fn f() -> qbit { qalloc() }" `shouldBe` accepted

  test "an isometry must return more owned qubits than it takes" $
    typeCheckOutcome "isometry fn f(q: qbit) -> qbit { H(q) }"
      `shouldBe` rejectedWith (QuantumWidthMismatch "isometry" 1 1 (spanAt 1 13))

  test "a coisometry must return fewer owned qubits than it takes" $
    typeCheckOutcome "coisometry fn f(q: qbit) -> qbit { H(q) }"
      `shouldBe` rejectedWith (QuantumWidthMismatch "coisometry" 1 1 (spanAt 1 15))

  test "borrowed qubits do not count towards a function's width" $
    typeCheckOutcome "unitary fn layer(qs: &[qbit]) { H(&qs[0]); } unitary fn f(q: &qbit, r: qbit) -> qbit { CX(q, &r); r }"
      `shouldBe` accepted

  test "a general function has no width constraint" $
    typeCheckOutcome "general fn sample(q: qbit) -> bit { measr(q) }" `shouldBe` accepted

  test "a classical function cannot take a qubit reference" $
    typeCheckOutcome "classical fn f(q: &qbit) {}"
      `shouldBe` rejectedWith (EffectViolation EffectClassical EffectUncompsafe (spanAt 1 14))

  test "a classical function cannot take a qubit slice" $
    typeCheckOutcome "classical fn f(qs: &[qbit]) {}"
      `shouldBe` rejectedWith (EffectViolation EffectClassical EffectUncompsafe (spanAt 1 14))

  test "a classical function cannot return qubits" $
    typeCheckOutcome "classical fn f() -> [qbit; 0] { [] }"
      `shouldBe` rejectedWith (EffectViolation EffectClassical EffectUncompsafe (spanAt 1 14))

  test "a classical function may take a quantum function value" $
    typeCheckOutcome "classical fn f(g: unitary fn(q: qbit) -> qbit) {}" `shouldBe` accepted

  test "a const fn cannot take quantum data" $
    typeCheckOutcome "const fn f(q: &qbit) {}"
      `shouldBe` rejectedWith (EffectViolation EffectClassical EffectUncompsafe (spanAt 1 10))

  test "owned widths use evaluated constant lengths" $
    typeCheckOutcome "const N: u32 = 2; unitary fn f(qs: [qbit; N]) -> [qbit; N + 1] { [qs[0], qs[1], qalloc()] }"
      `shouldBe` rejectedWith (QuantumWidthMismatch "unitary" 2 3 (spanAt 1 30))

-- Operation effects under the declared ceiling (plan §7.2, §7.3)
operationEffectTests : List ETest
operationEffectTests = Test.do
  test "a classical function cannot allocate qubits" $
    typeCheckOutcome "classical fn f() { let q = qalloc(); discard(q); }"
      `shouldBe` rejectedWith (EffectViolation EffectClassical EffectUncompsafe (spanAt 1 28))

  test "a unitary function cannot measure" $
    typeCheckOutcome "unitary fn f(q: &qbit) { let b = measr(q); }"
      `shouldBe` rejectedWith (EffectViolation EffectUnitary EffectGeneral (spanAt 1 34))

  test "a unitary function cannot reset" $
    typeCheckOutcome "unitary fn f(q: &qbit) { reset(q); }"
      `shouldBe` rejectedWith (EffectViolation EffectUnitary EffectGeneral (spanAt 1 26))

  test "an uncompsafe function may apply basis-permuting gates" $
    typeCheckOutcome "uncompsafe fn f(a: &qbit, b: &qbit, c: &qbit) { I(a); X(a); CX(a, b); CNOT(a, b); CCX(a, b, c); SWAP(a, b); CSWAP(a, b, c); }"
      `shouldBe` accepted

  test "an uncompsafe function cannot apply H" $
    typeCheckOutcome "uncompsafe fn f(q: &qbit) { H(q); }"
      `shouldBe` rejectedWith (EffectViolation EffectUncompsafe EffectUnitary (spanAt 1 29))

  test "an uncompsafe function cannot apply a phase gate" $
    typeCheckOutcome "uncompsafe fn f(q: &qbit) { Z(q); }"
      `shouldBe` rejectedWith (EffectViolation EffectUncompsafe EffectUnitary (spanAt 1 29))

  test "a unitary function cannot call a general function" $
    typeCheckOutcome "fn helper(q: &qbit) {} unitary fn f(q: &qbit) { helper(q); }"
      `shouldBe` rejectedWith (EffectViolation EffectUnitary EffectGeneral (spanAt 1 49))

  test "a unitary function may call uncompsafe and unitary functions" $
    typeCheckOutcome "uncompsafe fn flip(q: &qbit) { X(q); } unitary fn had(q: &qbit) { H(q); } unitary fn f(q: &qbit) { flip(q); had(q); }"
      `shouldBe` accepted

  test "a classical function may call classical functions" $
    typeCheckOutcome "classical fn inc(x: i32) -> i32 { x + 1 } classical fn f() -> i32 { inc(1) }"
      `shouldBe` accepted

  test "a call through a function value has its type's effect" $
    typeCheckOutcome "unitary fn f(q: &qbit, g: general fn(q: &qbit)) { g(q); }"
      `shouldBe` rejectedWith (EffectViolation EffectUnitary EffectGeneral (spanAt 1 51))

  test "weaken and barrier are classical operations" $
    typeCheckOutcome "uncompsafe fn f(q: qbit) -> affine qbit { barrier(&q); weaken(q) }" `shouldBe` accepted

  test "qalloc is permitted in a unitary function" $
    typeCheckOutcome "unitary fn f(q: &qbit) { let scratch a = qalloc(); CX(q, &a); }" `shouldBe` accepted

  test "an uncompsafe function cannot apply Y" $
    typeCheckOutcome "uncompsafe fn f(q: &qbit) { Y(q); }"
      `shouldBe` rejectedWith (EffectViolation EffectUncompsafe EffectUnitary (spanAt 1 29))

  test "a unitary function may discard a fresh ancilla" $
    typeCheckOutcome "unitary fn f(q: &qbit) { let a = qalloc(); discard(a); }" `shouldBe` accepted

  test "a unitary function cannot discard a qubit it changed" $
    typeCheckOutcome "unitary fn f(q: &qbit) { let a = qalloc(); H(&a); discard(a); }"
      `shouldBe` rejectedWith (EffectViolation EffectUnitary EffectGeneral (spanAt 1 51))

  test "a parameter named like a gate is called with its own effect" $
    typeCheckOutcome "unitary fn f(X: fn(q: &qbit), q: &qbit) { X(q); }"
      `shouldBe` rejectedWith (EffectViolation EffectUnitary EffectGeneral (spanAt 1 43))

  test "a unitary function may uncompute and discard an ancilla" $
    typeCheckOutcome "unitary fn f(c: &qbit) { let a = qalloc(); CX(c, &a); let a = uncompute(a); discard(a); }"
      `shouldBe` accepted

  test "a coisometry cannot discard a parameter qubit without a clean-state proof" $
    typeCheckOutcome "coisometry fn f(q: qbit, a: qbit) -> qbit { discard(a); q }"
      `shouldBe` rejectedWith (EffectViolation EffectCoisometry EffectGeneral (spanAt 1 45))

-- Callable modifiers and modifier blocks (plan §7.2, §7.3)
modifierTests : List ETest
modifierTests = Test.do
  test "the adjoint of a gate is permitted in unitary code" $
    typeCheckOutcome "unitary fn f(q: &qbit) { adjoint(H)(q); adjoint(S)(q); }" `shouldBe` accepted

  test "the adjoint of a user function needs adjoint support" $
    typeCheckOutcome "unitary fn g(q: &qbit) { H(q); } unitary fn f(q: &qbit) { adjoint(g)(q); }"
      `shouldBe` rejectedWith (MissingCapability "adjoint" (spanAt 1 67))

  test "controlling a user function needs ctrl support" $
    typeCheckOutcome "unitary fn g(q: &qbit) { H(q); } unitary fn f(c: &qbit, q: &qbit) { ctrl(c).apply(g)(q); }"
      `shouldBe` rejectedWith (MissingCapability "ctrl" (spanAt 1 83))

  test "an adjoint block may call a unitary user function" $
    typeCheckOutcome "unitary fn g(q: &qbit) { H(q); } unitary fn f(q: &qbit) { adjoint { g(q); } }"
      `shouldBe` accepted

  test "a control block may call a unitary user function" $
    typeCheckOutcome "unitary fn g(q: &qbit) { H(q); } unitary fn f(c: &qbit, q: &qbit) { ctrl(c) { g(q); } }"
      `shouldBe` accepted

  test "an adjoint block admits only unitary operations" $
    typeCheckOutcome "general fn f(q: &qbit) { adjoint { let b = measr(q); } }"
      `shouldBe` rejectedWith (EffectViolation EffectUnitary EffectGeneral (spanAt 1 44))

  test "an adjoint block does not lift an enclosing classical ceiling" $
    typeCheckOutcome "classical fn f() { adjoint { let q = qalloc(); } }"
      `shouldBe` rejectedWith (EffectViolation EffectClassical EffectUncompsafe (spanAt 1 38))

  test "controls on 0 and 1 keep a controlled X uncompsafe" $
    typeCheckOutcome "uncompsafe fn f(c: &qbit, t: &qbit) { ctrl(c).on(bs\"0\").apply(X)(t); ctrl(c).on(bs\"1\").apply(X)(t); }"
      `shouldBe` accepted

  test "a control on + makes a controlled X unitary" $
    typeCheckOutcome "uncompsafe fn f(c: &qbit, t: &qbit) { ctrl(c).on(bs\"+\").apply(X)(t); }"
      `shouldBe` rejectedWith (EffectViolation EffectUncompsafe EffectUnitary (spanAt 1 39))

  test "a control block on - is a unitary operation" $
    typeCheckOutcome "uncompsafe fn f(c: &qbit, t: &qbit) { ctrl(c).on(bs\"-\") { X(t); } }"
      `shouldBe` rejectedWith (EffectViolation EffectUncompsafe EffectUnitary (spanAt 1 39))

  test "a controlled H is unitary" $
    typeCheckOutcome "uncompsafe fn f(c: &qbit, t: &qbit) { ctrl(c).apply(H)(t); }"
      `shouldBe` rejectedWith (EffectViolation EffectUncompsafe EffectUnitary (spanAt 1 39))

  test "a := initializer admits only uncompsafe operations" $
    typeCheckOutcome "general fn f() { let q: qbit := H(qalloc()); }"
      `shouldBe` rejectedWith (EffectViolation EffectUncompsafe EffectUnitary (spanAt 1 33))

  test "the adjoint of a function-typed parameter needs adjoint support" $
    typeCheckOutcome "unitary fn f(g: unitary fn(q: &qbit), q: &qbit) { adjoint(g)(q); }"
      `shouldBe` rejectedWith (MissingCapability "adjoint" (spanAt 1 59))

  test "controlling a function-typed parameter needs ctrl support" $
    typeCheckOutcome "unitary fn f(g: unitary fn(q: &qbit), c: &qbit, q: &qbit) { ctrl(c).apply(g)(q); }"
      `shouldBe` rejectedWith (MissingCapability "ctrl" (spanAt 1 75))

  test "a control block nested in an adjoint block over gates is permitted" $
    typeCheckOutcome "unitary fn f(c: &qbit, q: &qbit) { adjoint { ctrl(c) { H(q); } } }" `shouldBe` accepted

  test "a control without a selector keeps a controlled X uncompsafe" $
    typeCheckOutcome "uncompsafe fn f(c: &qbit, t: &qbit) { ctrl(c).apply(X)(t); }" `shouldBe` accepted

  test "a control block over X keeps an uncompsafe function uncompsafe" $
    typeCheckOutcome "uncompsafe fn f(c: &qbit, t: &qbit) { ctrl(c) { X(t); } }" `shouldBe` accepted

-- Leaving modifier blocks (plan §7.2)
jumpTests : List ETest
jumpTests = Test.do
  test "a return cannot leave a control block" $
    typeCheckOutcome "fn f(c: &qbit, t: &qbit) { ctrl(c) { X(t); return; } }"
      `shouldBe` rejectedWith (JumpOutOfQuantumBlock "return" (spanAt 1 44))

  test "a break cannot leave an adjoint block" $
    typeCheckOutcome "fn f(q: &qbit) { for i in 0..3 { adjoint { H(q); break; } } }"
      `shouldBe` rejectedWith (JumpOutOfQuantumBlock "break" (spanAt 1 50))

  test "a continue cannot leave a control block" $
    typeCheckOutcome "fn f(c: &qbit, t: &qbit) { for i in 0..3 { ctrl(c) { X(t); continue; } } }"
      `shouldBe` rejectedWith (JumpOutOfQuantumBlock "continue" (spanAt 1 60))

  test "a loop inside an adjoint block stays inside it" $
    typeCheckOutcome "fn f(q: &qbit) { adjoint { for i in 0..3 { H(q); } } }" `shouldBe` accepted

-- Attributes (plan §7.5): only cases on which both documented rules agree
attributeTests : List ETest
attributeTests = Test.do
  test "qasm_gate is allowed on a unitary function" $
    typeCheckOutcome "#[qasm_gate] unitary fn myfun(q: qbit) -> qbit { let q = X(q); let q = H(q); q }"
      `shouldBe` accepted

  test "qasm_gate with a name is allowed on a unitary function" $
    typeCheckOutcome "#[qasm_gate(\"qasm_subroutine_name\")] unitary fn myfun(q: qbit) -> qbit { H(q) }"
      `shouldBe` accepted

  test "qasm_def is allowed on a general function" $
    typeCheckOutcome "#[qasm_def] general fn myfun(q: qbit) -> bit { let q = X(q); let q = H(q); measr(q) }"
      `shouldBe` accepted

  test "qasm_gate is not allowed on a general function" $
    typeCheckOutcome "#[qasm_gate] general fn myfun(q: qbit) -> bit { measr(q) }"
      `shouldBe` rejectedWith (InvalidAttributeEffect "qasm_gate" EffectGeneral (spanAt 1 3))

  test "qasm_gate is not allowed on a classical function" $
    typeCheckOutcome "#[qasm_gate] classical fn myfun(x: i32) -> i32 { x }"
      `shouldBe` rejectedWith (InvalidAttributeEffect "qasm_gate" EffectClassical (spanAt 1 3))

  test "qasm_gate on a function without an effect sees the general default" $
    typeCheckOutcome "#[qasm_gate] fn myfun(q: qbit) -> qbit { H(q) }"
      `shouldBe` rejectedWith (InvalidAttributeEffect "qasm_gate" EffectGeneral (spanAt 1 3))

  test "qasm_def does not restrict a unitary function" $
    typeCheckOutcome "#[qasm_def] unitary fn f(q: qbit) -> qbit { H(q) }" `shouldBe` accepted

-- Recursive signature checks and nested ceilings (plan §7.1–§7.5; spec §53, §64).
nestedEffectTests : List ETest
nestedEffectTests = Test.do
  test "owned width traverses nested tuples and arrays" $
    typeCheckOutcome "unitary fn f(qs: ([qbit; 2], qbit)) -> [qbit; 3] { [qs.0[0], qs.0[1], qs.1] }" `shouldBe` accepted

  test "a function value does not contribute its signature qubits to owned width" $
    typeCheckOutcome "unitary fn f(g: unitary fn(q: qbit) -> qbit) {}" `shouldBe` accepted

  test "a classical signature cannot hide quantum references inside aggregates" $
    typeCheckOutcome "classical fn f(xs: (i32, [&qbit; 2])) {}"
      `shouldBe` rejectedWith (EffectViolation EffectClassical EffectUncompsafe (spanAt 1 14))

  test "a unitary function cannot lose an owned qubit" $
    typeCheckOutcome "unitary fn f(qs: (qbit, qbit)) -> qbit { discard(qs.0); qs.1 }"
      `shouldBe` rejectedWith (QuantumWidthMismatch "unitary" 2 1 (spanAt 1 12))

  test "a coisometry cannot increase the owned width" $
    typeCheckOutcome "coisometry fn f(q: qbit) -> (qbit, qbit) { (q, qalloc()) }"
      `shouldBe` rejectedWith (QuantumWidthMismatch "coisometry" 1 2 (spanAt 1 15))

  test "an adjoint block preserves the enclosing uncompsafe ceiling" $
    typeCheckOutcome "uncompsafe fn f(q: &qbit) { adjoint { H(q); } }"
      `shouldBe` rejectedWith (EffectViolation EffectUncompsafe EffectUnitary (spanAt 1 39))

  test "a control block preserves the enclosing uncompsafe ceiling" $
    typeCheckOutcome "uncompsafe fn f(c: &qbit, q: &qbit) { ctrl(c) { H(q); } }"
      `shouldBe` rejectedWith (EffectViolation EffectUncompsafe EffectUnitary (spanAt 1 49))

  test "a := initializer preserves the enclosing classical ceiling" $
    typeCheckOutcome "classical fn f() { let q: qbit := qalloc(); }"
      `shouldBe` rejectedWith (EffectViolation EffectClassical EffectUncompsafe (spanAt 1 35))

  test "an imaginary positive-basis selector raises controlled X to unitary" $
    typeCheckOutcome "uncompsafe fn f(c: &qbit, q: &qbit) { ctrl(c).on(bs\"i\").apply(X)(q); }"
      `shouldBe` rejectedWith (EffectViolation EffectUncompsafe EffectUnitary (spanAt 1 39))

  test "an imaginary negative-basis selector raises a control block to unitary" $
    typeCheckOutcome "uncompsafe fn f(c: &qbit, q: &qbit) { ctrl(c).on(bs\"I\") { X(q); } }"
      `shouldBe` rejectedWith (EffectViolation EffectUncompsafe EffectUnitary (spanAt 1 39))

  test "the adjoint of a basis permutation remains uncompsafe" $
    typeCheckOutcome "uncompsafe fn f(q: &qbit) { adjoint(X)(q); }" `shouldBe` accepted

  test "a break targeting a loop inside a control block is allowed" $
    typeCheckOutcome "fn f(c: &qbit, q: &qbit) { ctrl(c) { loop { X(q); break; } } }" `shouldBe` accepted

  test "a return cannot leave an adjoint block" $
    typeCheckOutcome "fn f(q: &qbit) { adjoint { H(q); return; } }"
      `shouldBe` rejectedWith (JumpOutOfQuantumBlock "return" (spanAt 1 34))

  test "qasm_def does not forbid a classical function" $
    typeCheckOutcome "#[qasm_def] classical fn f(x: i32) -> i32 { x + 1 }" `shouldBe` accepted


export
runEffectsCheckTests : IO ()
runEffectsCheckTests =
  runTests $ concat
    [ signatureClaimTests
    , operationEffectTests
    , modifierTests
    , jumpTests
    , attributeTests
    , nestedEffectTests
    ]

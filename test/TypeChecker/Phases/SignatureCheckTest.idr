module TypeChecker.Phases.SignatureCheckTest

import Test.Simple

import Compiler.TypeChecker.Data
import Compiler.TypeChecker.Type
import Frontend.Syntax.Common
import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Pass A: signatures
--------------------------------------------------------------------------------
-- Pass A records the type of every function and constant without entering
-- bodies (plan §4). Signatures and bodies are checked in rounds (§2.3): a
-- signature can need a constant's value, a constant's value needs its checked
-- initializer, and a constant initializer can call a const fn whose body must
-- be checked first. Every test runs the whole checker on a program that
-- passes the frontend; the expected result is acceptance or the first error
-- reported, compared through `show`. A signature diagnostic points at the
-- function's name, its effect keyword or the offending type or length.
--------------------------------------------------------------------------------

-- Function signatures (plan §4.1 item 2)
functionSignatureTests : List ETest
functionSignatureTests = Test.do
  test "a function with primitive parameters and result type-checks" $
    typeCheckOutcome "fn add(x: i32, y: i32) -> i32 { x + y }" `shouldBe` accepted

  test "an omitted return type is unit" $
    typeCheckOutcome "fn f() {} fn g() { let u: () = f(); }" `shouldBe` accepted

  test "a call has the callee's declared result type" $
    typeCheckOutcome "fn f(x: i32) -> i32 { x } fn g() -> i32 { f(1) }" `shouldBe` accepted

  test "a call's argument is checked against the declared parameter type" $
    typeCheckOutcome "fn f(x: i32) -> i32 { x } fn g() -> i32 { f(true) }"
      `shouldBe` rejectedWith (TypeMismatch i32 bool (spanAt 1 45))

  test "a call's declared result type must fit its use" $
    typeCheckOutcome "fn f() -> bool { true } fn g() -> i32 { f() }"
      `shouldBe` rejectedWith (TypeMismatch i32 bool (spanAt 1 41))

  test "parameters may be shared and mutable references to values and slices" $
    typeCheckOutcome "fn f(a: &i32, b: &mut i32, c: &[i32], d: &mut [i32]) {}" `shouldBe` accepted

  test "a parameter may be a qubit reference or a qubit slice" $
    typeCheckOutcome "fn f(q: &qbit, qs: &[qbit]) {}" `shouldBe` accepted

  test "qubit parameters and results may carry multiplicity qualifiers" $
    typeCheckOutcome "fn f(q: affine qbit, p: (linear qbit, affine qbit)) -> (affine qbit, (linear qbit, affine qbit)) { (q, p) }"
      `shouldBe` accepted

  test "a mut parameter has its declared type" $
    typeCheckOutcome "fn f(mut x: i32) -> i32 { x += 1; x }" `shouldBe` accepted

  test "a function-typed parameter records its effect, parameters and result" $
    typeCheckOutcome "general fn phase_kickback(qs: [qbit; 4], oracle: unitary fn(qs: [qbit; 4], target: qbit) -> ([qbit; 4], qbit)) -> [qbit; 4] { let ancilla = qalloc(); let (qs, ancilla) = oracle(qs, ancilla); discard(ancilla); qs }"
      `shouldBe` accepted

  test "a function type without an effect or result is general and returns unit" $
    typeCheckOutcome "fn run(g: fn(value: i32)) { g(1); }" `shouldBe` accepted

  test "a declared function is a value of its function type" $
    typeCheckOutcome "classical fn inc(x: i32) -> i32 { x + 1 } fn run(g: classical fn(x: i32) -> i32) -> i32 { g(1) } fn main() -> i32 { run(inc) }"
      `shouldBe` accepted

  test "parameter names do not take part in function type equality" $
    typeCheckOutcome "classical fn inc(y: i32) -> i32 { y + 1 } fn run(g: classical fn(x: i32) -> i32) -> i32 { g(1) } fn main() -> i32 { run(inc) }"
      `shouldBe` accepted

  test "pub items type-check like private ones" $
    typeCheckOutcome "pub const N: u32 = 2; pub fn f(a: [i32; N]) -> [i32; N] { a }" `shouldBe` accepted

  test "a qstate parameter type is unsupported" $
    typeCheckOutcome "fn f(s: qstate) {}"
      `shouldBe` rejectedWith (UnsupportedFeature "qstate" (spanAt 1 9))

  test "an owned slice parameter is unsized" $
    typeCheckOutcome "fn f(xs: [i32]) {}"
      `shouldBe` rejectedWith (UnsizedValue (slice i32) (spanAt 1 10))

  test "an owned slice result is unsized" $
    typeCheckOutcome "fn f() -> [i32] {}"
      `shouldBe` rejectedWith (UnsizedValue (slice i32) (spanAt 1 11))

  test "a qstate nested in a parameter type is unsupported" $
    typeCheckOutcome "fn f(s: [qstate; 2]) {}"
      `shouldBe` rejectedWith (UnsupportedFeature "qstate" (spanAt 1 10))

-- Forward references and recursion (plan §2.3, §9 item 3)
forwardReferenceTests : List ETest
forwardReferenceTests = Test.do
  test "a function may call a function declared later" $
    typeCheckOutcome "fn f() -> i32 { g() } fn g() -> i32 { 1 }" `shouldBe` accepted

  test "a recursive function needs only its own signature" $
    typeCheckOutcome "classical fn fact(n: u32) -> u32 { if n == 0 { 1 } else { n * fact(n - 1) } }"
      `shouldBe` accepted

  test "mutually recursive functions are not a declaration cycle" $
    typeCheckOutcome "fn even(n: u32) -> bool { if n == 0 { true } else { odd(n - 1) } } fn odd(n: u32) -> bool { if n == 0 { false } else { even(n - 1) } }"
      `shouldBe` accepted

  test "a function may read a constant declared later" $
    typeCheckOutcome "fn f() -> i32 { FIVE } const FIVE: i32 = 5;" `shouldBe` accepted

  test "a signature length may use a constant declared later" $
    typeCheckOutcome "fn f(a: [i32; N]) -> i32 { a[0] } const N: u32 = 4;" `shouldBe` accepted

  test "a signature length may call a const fn declared later" $
    typeCheckOutcome "fn f(a: [i32; square(2)]) {} const fn square(x: u32) -> u32 { x * x }"
      `shouldBe` accepted

  test "a signature length that needs several rounds is evaluated" $
    typeCheckOutcome "fn f(a: [i32; LEN]) {} const LEN: u32 = double(HALF); const HALF: u32 = 2; const fn double(x: u32) -> u32 { x * 2 } fn g() { let a: [i32; 4] = [0; 4]; f(a); }"
      `shouldBe` accepted

  test "a recursive const fn may size a signature" $
    typeCheckOutcome "const fn fact(n: u32) -> u32 { if n == 0 { 1 } else { n * fact(n - 1) } } fn f(a: [i32; fact(3)]) {} fn g() { let a: [i32; 6] = [0; 6]; f(a); }"
      `shouldBe` accepted

-- Retry boundaries and independently checked lengths (plan §2.3, §2.5, §3.3).
-- Each fixture makes a demand whose producer occurs later in source order.
signatureRetryTests : List ETest
signatureRetryTests = Test.do
  test "mutually recursive const functions can produce a finite signature length" $
    typeCheckOutcome "fn f(a: [i32; even(4)]) {} const fn even(n: u32) -> u32 { if n == 0 { 1 } else { odd(n - 1) } } const fn odd(n: u32) -> u32 { if n == 0 { 0 } else { even(n - 1) } } fn g() { f([0; 1]); }"
      `shouldBe` accepted

  test "nested function types evaluate both parameter and return array lengths" $
    typeCheckOutcome "fn run(g: fn(a: [i32; N]) -> [i32; N], a: [i32; N]) -> [i32; N] { g(a) } const N: u32 = 2; fn identity(a: [i32; 2]) -> [i32; 2] { a } fn f() { let a: [i32; 2] = run(identity, [1, 2]); }"
      `shouldBe` accepted

  test "the same dependent length can occur in several parameter and result types" $
    typeCheckOutcome "fn f(a: [i32; size()], b: [bool; size()]) -> ([i32; size()], [bool; size()]) { (a, b) } const fn size() -> u32 { COUNT } const COUNT: u32 = 2; fn g() { let pair: ([i32; 2], [bool; 2]) = f([1, 2], [true, false]); }"
      `shouldBe` accepted

  test "a blocked body retries with its return context and earlier local inference intact" $
    typeCheckOutcome "fn f() -> i16 { let result = 7; let a: [i32; N] = [0; N]; result } const N: u32 = size(); const fn size() -> u32 { 2 }"
      `shouldBe` accepted

  test "an isolated length does not default unrelated local inference variables" $
    typeCheckOutcome "fn f() -> i8 { let result = 7; let a: [u32; { let result = 2; result }] = [0; 2]; result }"
      `shouldBe` accepted

  test "several blocked constants and signatures settle without a false cycle" $
    typeCheckOutcome "fn f(a: [i32; FIRST]) -> [i32; SECOND] { a } const FIRST: u32 = next(); const SECOND: u32 = LAST; const fn next() -> u32 { SECOND } const LAST: u32 = 3; fn g() { let a: [i32; 3] = f([0; 3]); }"
      `shouldBe` accepted

-- Array lengths in signatures (plan §3.1, §3.4)
signatureLengthTests : List ETest
signatureLengthTests = Test.do
  test "a literal length in a signature type-checks" $
    typeCheckOutcome "fn f(qs: [qbit; 2]) -> [qbit; 2] { qs }" `shouldBe` accepted

  test "a constant-expression length is evaluated" $
    typeCheckOutcome "fn f(a: [i32; 2 + 2]) {} fn g() { let a: [i32; 4] = [0; 4]; f(a); }" `shouldBe` accepted

  test "a u64 constant may size an array" $
    typeCheckOutcome "const N: u64 = 4; fn f(a: [i32; N]) {} fn g() { let a: [i32; 4] = [0; 4]; f(a); }"
      `shouldBe` accepted

  test "a signed constant cannot size an array" $
    typeCheckOutcome "const N: i32 = 4; fn f(a: [i32; N]) {}"
      `shouldBe` rejectedWith (InvalidArrayLength i32 (spanAt 1 33))

  test "a bool constant cannot size an array" $
    typeCheckOutcome "const FLAG: bool = true; fn f(a: [i32; FLAG]) {}"
      `shouldBe` rejectedWith (InvalidArrayLength bool (spanAt 1 40))

  test "a length that does not fit u32 is rejected" $
    typeCheckOutcome "const N: u64 = 4294967296; fn f(a: [i32; N]) {}"
      `shouldBe` rejectedWith (ArrayLengthTooLarge 4294967296 (spanAt 1 42))

  test "a non-const call cannot size a signature" $
    typeCheckOutcome "fn g() -> u32 { 3 } fn f(a: [i32; g()]) {}"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 35))

  test "an argument's array length must equal the parameter's" $
    typeCheckOutcome "fn f(a: [i32; 3]) {} fn g() { f([1, 2]); }"
      `shouldBe` rejectedWith (TypeMismatch (array i32 3) (array i32 2) (spanAt 1 33))

  test "a returned array's length must equal the declared result's" $
    typeCheckOutcome "fn f() -> [i32; 2] { [1, 2, 3] }"
      `shouldBe` rejectedWith (TypeMismatch (array i32 2) (array i32 3) (spanAt 1 22))

-- Constant items (plan §4.1 item 3)
constantItemTests : List ETest
constantItemTests = Test.do
  test "a constant has its written type" $
    typeCheckOutcome "const FIVE: i32 = 5; fn f() -> i32 { FIVE }" `shouldBe` accepted

  test "a constant's written type is used where it is read" $
    typeCheckOutcome "const FLAG: bool = true; fn f() -> i32 { FLAG }"
      `shouldBe` rejectedWith (TypeMismatch i32 bool (spanAt 1 42))

  test "an array constant has its written type" $
    typeCheckOutcome "const A: [i32; 3] = [1, 2, 3]; fn f() -> i32 { A[0] }" `shouldBe` accepted

  test "a tuple constant has its written type" $
    typeCheckOutcome "const T: (u32, bool) = (3, true); fn f() -> bool { T.1 }" `shouldBe` accepted

-- Parameter names that resolve to constants (plan §1.4, §4.1 item 2, §5.6)
constantParameterTests : List ETest
constantParameterTests = Test.do
  test "a parameter named like a unit constant is an irrefutable pattern" $
    typeCheckOutcome "const UNIT: () = (); fn f(UNIT: ()) {} fn g() { f(()); }" `shouldBe` accepted

  test "a constant-name parameter keeps the constant's own type" $
    typeCheckOutcome "const UNIT: () = (); fn f(UNIT: ()) {} fn g() -> () { UNIT }" `shouldBe` accepted

  test "a parameter named like a non-unit constant is a refutable pattern" $
    typeCheckOutcome "const ZERO: i32 = 0; fn f(ZERO: i32) {}"
      `shouldBe` rejectedWith (RefutableBindingPattern (spanAt 1 27))

  test "a constant-name parameter must have the constant's type" $
    typeCheckOutcome "const UNIT: () = (); fn f(UNIT: i32) {}"
      `shouldBe` rejectedWith (TypeMismatch i32 unit (spanAt 1 27))

-- Const functions are classical (plan §4.1 item 2, §11.1)
constFunctionTests : List ETest
constFunctionTests = Test.do
  test "a const fn without an effect is recorded as classical" $
    typeCheckOutcome "const fn square(x: i32) -> i32 { x * x } classical fn f() -> i32 { square(3) }"
      `shouldBe` accepted

  test "a const fn may be written classical" $
    typeCheckOutcome "const classical fn square(x: i32) -> i32 { x * x } classical fn f() -> i32 { square(3) }"
      `shouldBe` accepted

  test "a const fn cannot be written unitary" $
    typeCheckOutcome "const unitary fn f() {}"
      `shouldBe` rejectedWith (EffectViolation EffectClassical EffectUnitary (spanAt 1 7))

  test "a const fn cannot be written general" $
    typeCheckOutcome "const general fn f() {}"
      `shouldBe` rejectedWith (EffectViolation EffectClassical EffectGeneral (spanAt 1 7))

  test "a const fn that is never called cannot call a non-const function" $
    typeCheckOutcome "fn g() -> u32 { 3 } const fn f() -> u32 { g() }"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 43))

-- Declaration cycles (plan §2.4): the error names the symbols on the cycle and
-- points at the name of the first item that is still waiting
declarationCycleTests : List ETest
declarationCycleTests = Test.do
  test "a constant defined by itself is a cycle" $
    typeCheckOutcome "const A: i32 = A;"
      `shouldBe` rejectedWith (CyclicDeclaration ["A"] (spanAt 1 7))

  test "two constants defined by each other are a cycle" $
    typeCheckOutcome "const A: i32 = B; const B: i32 = A;"
      `shouldBe` rejectedWith (CyclicDeclaration ["B", "A"] (spanAt 1 7))

  test "a signature length and a const fn call that need each other are a cycle" $
    typeCheckOutcome "const fn f(a: [i32; N]) -> u32 { 3 } const N: u32 = f([0; 3]);"
      `shouldBe` rejectedWith (CyclicDeclaration ["N", "f"] (spanAt 1 10))

  test "an item waiting on a cycle is not listed in it" $
    typeCheckOutcome "const N: u32 = M; const M: u32 = N; fn f(a: [i32; N]) {}"
      `shouldBe` rejectedWith (CyclicDeclaration ["N", "M"] (spanAt 1 40))

  test "a three-constant dependency cycle reports every cycle member once" $
    typeCheckOutcome "const A: u32 = B; const B: u32 = C; const C: u32 = A;"
      `shouldBe` rejectedWith (CyclicDeclaration ["B", "C", "A"] (spanAt 1 7))

  test "a constant evaluated through a const fn that reads it is a cycle" $
    typeCheckOutcome "const fn f() -> u32 { N } const N: u32 = f();"
      `shouldBe` rejectedWith (CyclicDeclaration ["N"] (spanAt 1 33))

-- Only evaluated constant reads create value dependencies (plan §2.3, §3.2).
-- The references still have to be resolved and type-checked in every branch.
lazyDependencyTests : List ETest
lazyDependencyTests = Test.do
  test "a constant reference in an unselected else branch does not create a cycle" $
    typeCheckOutcome "const A: u32 = if true { 1 } else { B }; const B: u32 = A; fn f() { let a: [i32; B] = [0; 1]; }"
      `shouldBe` accepted

  test "a constant reference in an unselected then branch does not create a cycle" $
    typeCheckOutcome "const A: u32 = if false { B } else { 2 }; const B: u32 = A; fn f() { let a: [i32; B] = [0; 2]; }"
      `shouldBe` accepted

  test "short-circuiting and avoids a cyclic constant value dependency" $
    typeCheckOutcome "const A: bool = false && B; const B: bool = A; const N: u32 = if (B) { 0 } else { 1 }; fn f() { let a: [i32; N] = [0; 1]; }"
      `shouldBe` accepted

  test "short-circuiting or avoids a cyclic constant value dependency" $
    typeCheckOutcome "const A: bool = true || B; const B: bool = A; const N: u32 = if (B) { 1 } else { 0 }; fn f() { let a: [i32; N] = [0; 1]; }"
      `shouldBe` accepted

  test "an unselected const function branch does not wait on its caller's constant" $
    typeCheckOutcome "const fn size() -> u32 { if true { 2 } else { N } } const N: u32 = size(); fn f() { let a: [i32; N] = [0; 2]; }"
      `shouldBe` accepted

  test "a constant reference in the selected branch is a cycle" $
    typeCheckOutcome "const A: u32 = if false { 1 } else { B }; const B: u32 = A;"
      `shouldBe` rejectedWith (CyclicDeclaration ["B", "A"] (spanAt 1 7))

-- Prelude functions used as values (plan §2.4, §4.2)
preludeValueTests : List ETest
preludeValueTests = Test.do
  test "a gate can be passed where a unitary function type is expected" $
    typeCheckOutcome "fn run(g: unitary fn(q: qbit) -> qbit, q: qbit) -> qbit { g(q) } fn main() -> qbit { let q = qalloc(); run(H, q) }"
      `shouldBe` accepted

  test "a basis-permuting gate satisfies an uncompsafe function type" $
    typeCheckOutcome "fn run(g: uncompsafe fn(q: qbit) -> qbit, q: qbit) -> qbit { g(q) } fn main() -> qbit { run(X, qalloc()) }"
      `shouldBe` accepted

  test "a non-permuting gate does not satisfy an uncompsafe function type" $
    typeCheckOutcome "fn run(g: uncompsafe fn(q: qbit) -> qbit, q: qbit) -> qbit { g(q) } fn main() -> qbit { run(H, qalloc()) }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectUncompsafe [linearQbit] linearQbit) (LeafFunctionType EffectUnitary [SupportAdjoint, SupportCtrl] [linearQbit] linearQbit) (spanAt 1 93))

  test "a rotation gate value takes an angle64 and a qubit" $
    typeCheckOutcome "fn run(g: unitary fn(theta: angle64, q: qbit) -> qbit, q: qbit) -> qbit { g(0.5, q) } fn main() -> qbit { run(RX, qalloc()) }"
      `shouldBe` accepted

  test "a user function may shadow a prelude gate" $
    typeCheckOutcome "fn H(x: i32) -> i32 { x } fn main() -> i32 { H(1) }" `shouldBe` accepted

  test "a user function may shadow a prelude math function" $
    typeCheckOutcome "fn sin(x: bool) -> bool { x } fn main() -> bool { sin(true) }" `shouldBe` accepted

  test "a constant may shadow a prelude gate name" $
    typeCheckOutcome "const I: i32 = 1; fn main() -> i32 { I + 1 }" `shouldBe` accepted

  test "a rotation gate value specializes to an angle32 function type" $
    typeCheckOutcome "fn run(g: unitary fn(theta: angle32, q: qbit) -> qbit, q: qbit) -> qbit { g(0.5, q) } fn main() -> qbit { run(RX, qalloc()) }"
      `shouldBe` accepted

  test "a two-qubit gate value has a tuple-returning function type" $
    typeCheckOutcome "fn run(g: unitary fn(a: qbit, b: qbit) -> (qbit, qbit), a: qbit, b: qbit) -> (qbit, qbit) { g(a, b) } fn main() -> (qbit, qbit) { run(CX, qalloc(), qalloc()) }"
      `shouldBe` accepted

  test "a math function value has its f64 signature" $
    typeCheckOutcome "fn run(g: fn(x: f64) -> f64) -> f64 { g(1.0) } fn main() -> f64 { run(sin) }"
      `shouldBe` accepted

export
runSignatureCheckTests : IO ()
runSignatureCheckTests =
  runTests $ concat
    [ functionSignatureTests
    , forwardReferenceTests
    , signatureRetryTests
    , signatureLengthTests
    , constantItemTests
    , constantParameterTests
    , constFunctionTests
    , declarationCycleTests
    , lazyDependencyTests
    , preludeValueTests
    ]

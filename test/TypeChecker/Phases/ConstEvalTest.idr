module TypeChecker.Phases.ConstEvalTest

import Test.Simple

import Compiler.TypeChecker.Data
import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Constant evaluation
--------------------------------------------------------------------------------
-- ConstEval interprets checked constant initializers, array lengths, repeat
-- counts and qalloc counts, including calls to const fns, after the shared
-- ConstRules have checked const eligibility (plan §3). A computed value is
-- observed through a length: `let a: [i32; N] = [0; 4];` type-checks exactly
-- when N evaluates to 4. An evaluation error points at the operation that
-- fails; an eligibility error at the offending call, loop or operation; the
-- step limit at the expression whose evaluation exhausted it.
--------------------------------------------------------------------------------

-- Constant values (plan §3.1, §3.5)
constantValueTests : List ETest
constantValueTests = Test.do
  test "a constant's value is its initializer's value" $
    typeCheckOutcome "const N: u32 = 2 + 2; fn f() { let a: [i32; N] = [0; 4]; }" `shouldBe` accepted

  test "a length mismatch shows the evaluated length" $
    typeCheckOutcome "const N: u32 = 2 + 2; fn f() { let a: [i32; N] = [0; 5]; }"
      `shouldBe` rejectedWith (TypeMismatch (array i32 4) (array i32 5) (spanAt 1 50))

  test "a constant may use a constant declared later" $
    typeCheckOutcome "const A: u32 = B * 2; const B: u32 = 3; fn f() { let a: [i32; A] = [0; 6]; }"
      `shouldBe` accepted

  test "a const fn call is evaluated" $
    typeCheckOutcome "const fn square(x: u32) -> u32 { x * x } const N: u32 = square(3); fn f() { let a: [i32; N] = [0; 9]; }"
      `shouldBe` accepted

  test "nested const fn calls are evaluated" $
    typeCheckOutcome "const fn double(x: u32) -> u32 { x * 2 } const fn quad(x: u32) -> u32 { double(double(x)) } fn f() { let a: [i32; quad(2)] = [0; 8]; }"
      `shouldBe` accepted

  test "a recursive const fn is evaluated" $
    typeCheckOutcome "const fn fact(n: u32) -> u32 { if n == 0 { 1 } else { n * fact(n - 1) } } fn f() { let a: [i32; fact(3)] = [0; 6]; }"
      `shouldBe` accepted

  test "a const fn can also be called at runtime" $
    typeCheckOutcome "const fn square(x: i32) -> i32 { x * x } fn f(y: i32) -> i32 { square(y) }"
      `shouldBe` accepted

  test "tuples, arrays and indexing are evaluated" $
    typeCheckOutcome "const T: (u32, u32) = (2, 3); const A: [u32; 3] = [4, 5, 6]; fn f() { let a: [i32; T.1 + A[2]] = [0; 9]; }"
      `shouldBe` accepted

  test "a repeat expression is evaluated" $
    typeCheckOutcome "const A: [u32; 3] = [2; 3]; fn f() { let a: [i32; A[0] + A[2]] = [0; 4]; }"
      `shouldBe` accepted

  test "a slice of a constant array can be passed to a const fn" $
    typeCheckOutcome "const fn second(xs: &[u32]) -> u32 { xs[1] } const A: [u32; 3] = [4, 5, 6]; fn f() { let a: [i32; second(&A)] = [0; 5]; }"
      `shouldBe` accepted

  test "a qalloc count is evaluated" $
    typeCheckOutcome "const N: u32 = 1 + 1; fn f() { let qs: [qbit; 2] = qalloc(N); discard(qs); }"
      `shouldBe` accepted

-- Statements and control flow in constants (plan §3.2)
constantControlFlowTests : List ETest
constantControlFlowTests = Test.do
  test "blocks and lets are evaluated" $
    typeCheckOutcome "const N: u32 = { let a = 2; let b = 3; a * b }; fn f() { let a: [i32; N] = [0; 6]; }"
      `shouldBe` accepted

  test "mutable locals, assignment and compound assignment are evaluated" $
    typeCheckOutcome "const fn f() -> u32 { let mut x = 1; x = x + 2; x *= 3; x } fn g() { let a: [i32; f()] = [0; 9]; }"
      `shouldBe` accepted

  test "if takes the executed branch" $
    typeCheckOutcome "const N: u32 = if 3 > 2 { 5 } else { 7 }; fn f() { let a: [i32; N] = [0; 5]; }"
      `shouldBe` accepted

  test "while loops are evaluated" $
    typeCheckOutcome "const fn sum_to(n: u32) -> u32 { let mut s = 0; let mut i = 0; while i < n { i += 1; s += i; } s } fn f() { let a: [i32; sum_to(4)] = [0; 10]; }"
      `shouldBe` accepted

  test "a loop's break value is evaluated" $
    typeCheckOutcome "const N: u32 = { let mut k = 0; loop { k += 1; if k == 3 { break k * 2; } } }; fn f() { let a: [i32; N] = [0; 6]; }"
      `shouldBe` accepted

  test "continue skips the rest of a loop body" $
    typeCheckOutcome "const fn odd_sum(n: u32) -> u32 { let mut s = 0; let mut i = 0; while i < n { i += 1; if i % 2 == 0 { continue; } s += i; } s } fn f() { let a: [i32; odd_sum(5)] = [0; 9]; }"
      `shouldBe` accepted

  test "an early return leaves a const fn" $
    typeCheckOutcome "const fn early(n: u32) -> u32 { if n > 2 { return 7; } n } fn f() { let a: [i32; early(5)] = [0; 7]; }"
      `shouldBe` accepted

  test "a mutable borrow in a const fn writes the borrowed local" $
    typeCheckOutcome "const fn f() -> u32 { let mut a = [1, 2, 3]; let r = &mut a; r[0] = 10; a[0] } fn g() { let x: [i32; f()] = [0; 10]; }"
      `shouldBe` accepted

  test "a compound assignment evaluates its target once" $
    typeCheckOutcome "const fn bump(c: &mut [u32; 1]) -> u32 { c[0] += 1; c[0] - 1 } const fn count() -> u32 { let mut a = [0, 0, 0]; let mut c = [0]; a[bump(&mut c)] += 5; c[0] } fn f() { let x: [i32; count()] = [0; 1]; }"
      `shouldBe` accepted

  test "a length may be a block with a loop" $
    typeCheckOutcome "fn f() { let a: [i32; { let mut k = 0; while k < 3 { k += 1; } k }] = [0; 3]; }"
      `shouldBe` accepted

  test "a loop inside a length may break out of itself" $
    typeCheckOutcome "fn f() { let a: [i32; 3] = [0; { let mut k = 0; loop { k += 1; if k == 3 { break; } } k }]; }"
      `shouldBe` accepted

  test "break cannot leave a length expression" $
    typeCheckOutcome "fn f() { loop { let a = [0; { break; 3 }]; } }"
      `shouldBe` rejectedWith (InvalidConstantControlFlow "break" (spanAt 1 31))

  test "continue cannot leave a length expression" $
    typeCheckOutcome "fn f() { loop { let a = [0; { continue; 3 }]; } }"
      `shouldBe` rejectedWith (InvalidConstantControlFlow "continue" (spanAt 1 31))

  test "return cannot leave a length expression" $
    typeCheckOutcome "fn f() -> i32 { let a = [0; { return 1; 3 }]; 0 }"
      `shouldBe` rejectedWith (InvalidConstantControlFlow "return" (spanAt 1 31))

-- Interpreter storage, frames and exported constants (plan §3.2, §3.5;
-- spec §9 slices, §34 tuple projection, §46 const functions and §51 references).
constantStorageTests : List ETest
constantStorageTests = Test.do
  test "each const function call gets fresh parameter and local storage" $
    typeCheckOutcome "const fn bump(n: u32) -> u32 { let mut x = n; x += 1; x } const N: u32 = bump(1) + bump(4); fn f() { let a: [i32; N] = [0; 7]; }"
      `shouldBe` accepted

  test "a const callee mutates its caller's array through a mutable reference" $
    typeCheckOutcome "const fn bump(xs: &mut [u32; 1]) { xs[0] += 1; } const fn count() -> u32 { let mut a = [1]; bump(&mut a); bump(&mut a); a[0] } fn f() { let a: [i32; count()] = [0; 3]; }"
      `shouldBe` accepted

  test "constant slicing uses a range value stored in a local" $
    typeCheckOutcome "const fn select() -> u32 { let a = [1, 4, 8, 16]; let range = 1u32..3u32; let s = &a[range]; s[0] + len(s) } fn f() { let a: [i32; select()] = [0; 6]; }"
      `shouldBe` accepted

  test "an exported constant slice retains its storage and extent" $
    typeCheckOutcome "const A: [u32; 3] = [2, 3, 4]; const S: &[u32] = &A[1..]; const N: u32 = S[0] + len(S); fn f() { let a: [i32; N] = [0; 5]; }"
      `shouldBe` accepted

  test "a reference nested in an exported constant tuple remains usable" $
    typeCheckOutcome "const A: [u32; 3] = [2, 3, 4]; const T: (&[u32], u32) = (&A, 1); const N: u32 = T.0[T.1]; fn f() { let a: [i32; N] = [0; 3]; }"
      `shouldBe` accepted

  test "a const function can return a slice borrowed from its argument" $
    typeCheckOutcome "const fn tail(xs: &[u32]) -> &[u32] { &xs[1..] } const A: [u32; 3] = [2, 3, 4]; const S: &[u32] = tail(&A); fn f() { let a: [i32; S[0] + len(S)] = [0; 5]; }"
      `shouldBe` accepted

  test "a constant can publish a function identity for a runtime call" $
    typeCheckOutcome "classical fn inc(x: u32) -> u32 { x + 1 } const F: classical fn(x: u32) -> u32 = inc; fn f(x: u32) -> u32 { F(x) }"
      `shouldBe` accepted

  test "a constant cannot hold a mutable reference" $
    typeCheckOutcome "const R: &mut [i32; 1] = &mut [5];"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 26))

  test "a constant reference to a literal is promoted" $
    typeCheckOutcome "const R: &i32 = &5; fn f() -> i32 { R + 1 }" `shouldBe` accepted

  test "mutating a copied array does not change the original constant value" $
    typeCheckOutcome "const fn count() -> u32 { let a = [1u32]; let mut b = a; b[0] = 7; a[0] } fn f() { let a: [i32; count()] = [0; 1]; }"
      `shouldBe` accepted

  test "copying a tuple also copies its nested array storage" $
    typeCheckOutcome "const fn count() -> u32 { let a = ([1u32, 2], 3u32); let mut b = a; b.0[0] = 7; b.1 = 9; a.0[0] + a.1 } fn f() { let a: [i32; count()] = [0; 4]; }"
      `shouldBe` accepted

  test "a const function's by-value array parameter has independent storage" $
    typeCheckOutcome "const fn replace(mut a: [u32; 1]) -> u32 { a[0] = 7; a[0] } const fn count() -> u32 { let a = [1u32]; let changed = replace(a); changed + a[0] } fn f() { let a: [i32; count()] = [0; 8]; }"
      `shouldBe` accepted

  test "copying an exported array into a mutable local preserves the constant" $
    typeCheckOutcome "const A: [u32; 1] = [2]; const fn count() -> u32 { let mut a = A; a[0] = 9; A[0] } fn f() { let a: [i32; count()] = [0; 2]; }"
      `shouldBe` accepted

-- Sequencing is observable through mutations (plan §3.2, §5.6 Assignment).
-- The Rust convention evaluates ordinary operands left-to-right, but an
-- assignment's value before its target; primitive compound assignments do too.
constantEvaluationOrderTests : List ETest
constantEvaluationOrderTests = Test.do
  test "const call arguments are evaluated left-to-right" $
    typeCheckOutcome "const fn bump(c: &mut [u32; 1]) -> u32 { c[0] += 1; c[0] } const fn pair(a: u32, b: u32) -> u32 { a * 10 + b } const fn count() -> u32 { let mut c = [0]; pair(bump(&mut c), bump(&mut c)) } fn f() { let a: [i32; count()] = [0; 12]; }"
      `shouldBe` accepted

  test "const binary operands are evaluated left-to-right" $
    typeCheckOutcome "const fn bump(c: &mut [u32; 1]) -> u32 { c[0] += 1; c[0] } const fn count() -> u32 { let mut c = [0]; bump(&mut c) * 10 + bump(&mut c) } fn f() { let a: [i32; count()] = [0; 12]; }"
      `shouldBe` accepted

  test "assignment evaluates its value before its indexed target" $
    typeCheckOutcome "const fn count() -> u32 { let mut a = [0u32, 0]; let mut i = 0; a[i] = { i = 1; 7 }; a[0] * 10 + a[1] } fn f() { let a: [i32; count()] = [0; 7]; }"
      `shouldBe` accepted

  test "primitive compound assignment evaluates its value before its target" $
    typeCheckOutcome "const fn count() -> u32 { let mut a = [0u32, 0]; let mut i = 0; a[i] += { i = 1; 7 }; a[0] * 10 + a[1] } fn f() { let a: [i32; count()] = [0; 7]; }"
      `shouldBe` accepted

-- Integer arithmetic follows each operation's checked type (plan §3.2)
constantArithmeticTests : List ETest
constantArithmeticTests = Test.do
  test "integer division truncates toward zero" $
    typeCheckOutcome "const N: u32 = (-7 / 2 + 5) as u32; fn f() { let a: [i32; N] = [0; 2]; }"
      `shouldBe` accepted

  test "a remainder takes the dividend's sign" $
    typeCheckOutcome "const N: u32 = (-7 % 3 + 5) as u32; fn f() { let a: [i32; N] = [0; 4]; }"
      `shouldBe` accepted

  test "division follows its operands' checked type" $
    typeCheckOutcome "const N: u32 = (7.0 / 2.0) as u32 + (7 / 2) as u32; fn f() { let a: [i32; N] = [0; 6]; }"
      `shouldBe` accepted

  test "an unsigned overflow is rejected" $
    typeCheckOutcome "const X: u8 = 255 + 1;"
      `shouldBe` rejectedWith (ArithmeticOverflow u8 (spanAt 1 15))

  test "a signed overflow is rejected" $
    typeCheckOutcome "const X: i32 = 2147483647 + 1;"
      `shouldBe` rejectedWith (ArithmeticOverflow i32 (spanAt 1 16))

  test "an unsigned subtraction below zero is rejected" $
    typeCheckOutcome "const X: u32 = 1 - 2;"
      `shouldBe` rejectedWith (ArithmeticOverflow u32 (spanAt 1 16))

  test "a multiplication overflow is rejected" $
    typeCheckOutcome "const X: i16 = 300 * 300;"
      `shouldBe` rejectedWith (ArithmeticOverflow i16 (spanAt 1 16))

  test "the signed minimum divided by -1 overflows" $
    typeCheckOutcome "const X: i32 = -2147483648 / -1;"
      `shouldBe` rejectedWith (ArithmeticOverflow i32 (spanAt 1 16))

  test "the signed minimum remainder by -1 overflows" $
    typeCheckOutcome "const X: i32 = -2147483648 % -1;"
      `shouldBe` rejectedWith (ArithmeticOverflow i32 (spanAt 1 16))

  test "division by zero is rejected" $
    typeCheckOutcome "const X: i32 = 1 / 0;"
      `shouldBe` rejectedWith (DivisionByZeroInConstant (spanAt 1 16))

  test "a remainder by zero is rejected" $
    typeCheckOutcome "const X: i32 = 1 % 0;"
      `shouldBe` rejectedWith (DivisionByZeroInConstant (spanAt 1 16))

  test "a left shift drops bits beyond the operand's width" $
    typeCheckOutcome "const N: u32 = (255u8 << 1) as u32; fn f() { let a: [i32; N] = [0; 254]; }"
      `shouldBe` accepted

  test "a shift by the operand's width overflows" $
    typeCheckOutcome "const X: u8 = 1u8 << 8;"
      `shouldBe` rejectedWith (ArithmeticOverflow u8 (spanAt 1 15))

  test "a negative shift amount is rejected" $
    typeCheckOutcome "const X: u32 = 1u32 << -1;"
      `shouldBe` rejectedWith (ArithmeticOverflow u32 (spanAt 1 16))

  test "a signed right shift is arithmetic" $
    typeCheckOutcome "const N: u32 = ((-8 >> 1) + 10) as u32; fn f() { let a: [i32; N] = [0; 6]; }"
      `shouldBe` accepted

  test "bitwise operations use fixed-width bit patterns" $
    typeCheckOutcome "const N: u32 = (0b1100 & 0b1010) | (0b0001 ^ 0b0011); fn f() { let a: [i32; N] = [0; 10]; }"
      `shouldBe` accepted

  test "a negated literal is one signed number" $
    typeCheckOutcome "const X: i8 = -128;" `shouldBe` accepted

  test "&& does not evaluate its right side when the left is false" $
    typeCheckOutcome "const B: bool = false && 1 / 0 == 0;" `shouldBe` accepted

  test "|| does not evaluate its right side when the left is true" $
    typeCheckOutcome "const B: bool = true || 1 / 0 == 0;" `shouldBe` accepted

  test "an error on a branch that is not executed is not raised" $
    typeCheckOutcome "const X: i32 = if true { 1 } else { 1 / 0 };" `shouldBe` accepted

  test "f32 arithmetic rounds at each checked operation" $
    typeCheckOutcome "const X: f32 = 16777216.0 + 1.0; const N: u32 = (X - 16777216.0) as u32 + 1; fn f() { let a: [i32; N] = [0; 1]; }"
      `shouldBe` accepted

  test "constant conditions apply bit-to-bool coercion" $
    typeCheckOutcome "const B: bit = 1; const N: u32 = if (B) { 3 } else { 4 }; fn f() { let a: [i32; N] = [0; 3]; }"
      `shouldBe` accepted

  test "bit operators in a constant stay 0 or 1" $
    typeCheckOutcome "const B: bit = 1; const C: bit = B ^ 1; const D: bit = C | B; const N: u32 = C as u32 + D as u32 * 2; fn f() { let a: [i32; N] = [0; 2]; }"
      `shouldBe` accepted

-- Casts in constants (plan §3.2, §5.6 Casts)
constantCastTests : List ETest
constantCastTests = Test.do
  test "an integer narrowing cast truncates" $
    typeCheckOutcome "const N: u32 = 300 as u8 as u32; fn f() { let a: [i32; N] = [0; 44]; }"
      `shouldBe` accepted

  test "a negative integer cast to unsigned wraps" $
    typeCheckOutcome "const N: u32 = (-1 as u8) as u32; fn f() { let a: [i32; N] = [0; 255]; }"
      `shouldBe` accepted

  test "a float-to-integer cast truncates toward zero" $
    typeCheckOutcome "const N: u32 = 3.9 as u32 + (-3.9 as i32 + 5) as u32; fn f() { let a: [i32; N] = [0; 5]; }"
      `shouldBe` accepted

  test "a float-to-integer cast saturates" $
    typeCheckOutcome "const N: u32 = (1.0e10 as u8) as u32; fn f() { let a: [i32; N] = [0; 255]; }"
      `shouldBe` accepted

  test "NaN casts to zero" $
    typeCheckOutcome "const N: u32 = (0.0 / 0.0) as u32 + 1; fn f() { let a: [i32; N] = [0; 1]; }"
      `shouldBe` accepted

  test "bool casts to 0 or 1" $
    typeCheckOutcome "const N: u32 = true as u32 + true as u32 + false as u32; fn f() { let a: [i32; N] = [0; 2]; }"
      `shouldBe` accepted

  test "bit casts to an integer" $
    typeCheckOutcome "const B: bit = 1; const N: u32 = B as u32 + 1; fn f() { let a: [i32; N] = [0; 2]; }"
      `shouldBe` accepted

  test "an angle cast normalizes positive radians modulo two pi" $
    typeCheckOutcome "const A: angle64 = 7.0 as angle64; const N: u32 = if A < 1.0 { 1 } else { 2 }; fn f() { let a: [i32; N] = [0; 1]; }"
      `shouldBe` accepted

  test "an angle cast normalizes negative radians into the positive interval" $
    typeCheckOutcome "const A: angle64 = -1.0 as angle64; const N: u32 = if A > 5.0 { 1 } else { 2 }; fn f() { let a: [i32; N] = [0; 1]; }"
      `shouldBe` accepted

  test "an angle literal is normalized modulo two pi" $
    typeCheckOutcome "const A: angle64 = 7.0; const N: u32 = if A < 1.0 { 1 } else { 2 }; fn f() { let a: [i32; N] = [0; 1]; }"
      `shouldBe` accepted

-- Observe each prelude result, not only that the call is const-eligible
-- (plan §3.2, §4.2; spec §3, §14).
constantMathValueTests : List ETest
constantMathValueTests = Test.do
  test "integer abs computes negative, positive and zero magnitudes" $
    typeCheckOutcome "const N: u32 = if abs(-7i16) == 7i16 && abs(7i16) == 7i16 && abs(0i16) == 0i16 { 1 } else { 0 }; fn f() { let a: [i32; N] = [0; 1]; }"
      `shouldBe` accepted

  test "floating abs preserves the fractional magnitude" $
    typeCheckOutcome "const N: u32 = if abs(-1.75) == 1.75 && abs(0.25) == 0.25 && abs(0.0) == 0.0 { 1 } else { 0 }; fn f() { let a: [i32; N] = [0; 1]; }"
      `shouldBe` accepted

  test "floor rounds negative and positive fractions down and preserves integers" $
    typeCheckOutcome "const N: u32 = if floor(1.75) == 1.0 && floor(-1.25) == -2.0 && floor(2.0) == 2.0 { 1 } else { 0 }; fn f() { let a: [i32; N] = [0; 1]; }"
      `shouldBe` accepted

  test "ceil rounds negative and positive fractions up and preserves integers" $
    typeCheckOutcome "const N: u32 = if ceil(1.25) == 2.0 && ceil(-1.75) == -1.0 && ceil(2.0) == 2.0 { 1 } else { 0 }; fn f() { let a: [i32; N] = [0; 1]; }"
      `shouldBe` accepted

  test "round selects the nearest integer on both sides of a half" $
    typeCheckOutcome "const N: u32 = if round(1.25) == 1.0 && round(1.75) == 2.0 && round(-1.25) == -1.0 && round(-1.75) == -2.0 { 1 } else { 0 }; fn f() { let a: [i32; N] = [0; 1]; }"
      `shouldBe` accepted

  test "round resolves positive and negative halfway ties away from zero" $
    typeCheckOutcome "const N: u32 = if round(2.5) == 3.0 && round(-2.5) == -3.0 && round(0.5) == 1.0 && round(-0.5) == -1.0 { 1 } else { 0 }; fn f() { let a: [i32; N] = [0; 1]; }"
      `shouldBe` accepted

  test "turns converts a quarter turn to radians" $
    typeCheckOutcome "const A: angle64 = turns(0.25); const N: u32 = if A > 1.57 && A < 1.58 { 1 } else { 0 }; fn f() { let a: [i32; N] = [0; 1]; }"
      `shouldBe` accepted

  test "turns normalizes negative turns and turns larger than one" $
    typeCheckOutcome "const A: angle64 = turns(-0.25); const B: angle64 = turns(1.25); const N: u32 = if A > 4.71 && A < 4.72 && B > 1.57 && B < 1.58 { 1 } else { 0 }; fn f() { let a: [i32; N] = [0; 1]; }"
      `shouldBe` accepted

  test "min and max select the smaller and larger operand" $
    typeCheckOutcome "const N: u32 = if min(-2i32, 1i32) == -2i32 && max(-1.5, 2.0) == 2.0 { min(3u32, 5u32) + max(3u32, 5u32) } else { 0 }; fn f() { let a: [i32; N] = [0; 8]; }"
      `shouldBe` accepted

-- Static const eligibility (plan §3.2, §7.4)
constEligibilityTests : List ETest
constEligibilityTests = Test.do
  test "a non-const function cannot be called in a constant" $
    typeCheckOutcome "fn g() -> u32 { 3 } const N: u32 = g();"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 36))

  test "a non-const call in a branch that is not executed is still rejected" $
    typeCheckOutcome "fn g() -> i32 { 1 } const X: i32 = if false { g() } else { 1 };"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 47))

  test "a non-const call behind short-circuiting is still rejected" $
    typeCheckOutcome "fn g() -> bool { true } const B: bool = false && g();"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 50))

  test "a for loop is not allowed in a const fn that is never called" $
    typeCheckOutcome "const fn f() -> u32 { let mut s = 0; for i in 0..3 { s += i; } s }"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 38))

  test "a call through a function value is not const" $
    typeCheckOutcome "const fn run(g: classical fn(x: u32) -> u32) -> u32 { g(2) }"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 55))

  test "a quantum operation is not allowed in a constant" $
    typeCheckOutcome "const N: u32 = { let q = qalloc(); 1 };"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 26))

  test "a quantum operation is not allowed in a const fn" $
    typeCheckOutcome "const fn f() -> u32 { let q = qalloc(); discard(q); 1 }"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 31))

  test "abs, min, max, floor, ceil and round are const" $
    typeCheckOutcome "const A: f64 = abs(-2.0) + min(1.0, 2.0) + max(1.0, 2.0) + floor(1.5) + ceil(1.5) + round(1.5); const N: u32 = max(3, 4) + min(5, 6); fn f() { let a: [i32; N] = [0; 9]; }"
      `shouldBe` accepted

  test "sin is not const" $
    typeCheckOutcome "const S: f64 = sin(1.0);"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 16))

  test "sqrt is not const" $
    typeCheckOutcome "const S: f64 = sqrt(4.0);"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 16))

  test "turns is const" $
    typeCheckOutcome "const QUARTER: angle64 = turns(0.25);" `shouldBe` accepted

  test "len is const" $
    typeCheckOutcome "const N: u32 = len([1, 2, 3]); fn f() { let a: [i32; N] = [0; 3]; }" `shouldBe` accepted

  test "Param is not const" $
    typeCheckOutcome "const P: param = Param(\"p\");"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 18))

  test "rev is excluded from constant evaluation even when its result is unused" $
    typeCheckOutcome "const fn f() -> u32 { let r = rev(0..3); 1 }"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 31))

  test "a locally aliased const function is still an indirect const call" $
    typeCheckOutcome "const fn inc(x: u32) -> u32 { x + 1 } const N: u32 = { let f = inc; f(2) };"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 69))

  test "a non-const user function shadowing abs does not inherit prelude constness" $
    typeCheckOutcome "fn abs(x: u32) -> u32 { x } const N: u32 = abs(3);"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 44))

  test "a const user function shadowing sin uses its own const eligibility" $
    typeCheckOutcome "const fn sin(x: u32) -> u32 { x + 1 } const N: u32 = sin(2); fn f() { let a: [i32; N] = [0; 3]; }"
      `shouldBe` accepted

  test "a for loop is not allowed in a constant initializer" $
    typeCheckOutcome "const N: u32 = { let mut s = 0; for i in 0..3 { s += i; } s };"
      `shouldBe` rejectedWith (NotAConstantExpression (spanAt 1 33))

-- Evaluation limits and runtime errors (plan §3.2, §3.3)
constantLimitTests : List ETest
constantLimitTests = Test.do
  test "a nonterminating loop exhausts the evaluation budget" $
    typeCheckOutcome "const fn spin() -> u32 { loop { } } const N: u32 = spin();"
      `shouldBe` rejectedWith (ConstEvaluationLimitExceeded (spanAt 1 52))

  test "unbounded recursion exhausts the evaluation budget" $
    typeCheckOutcome "const fn down(n: u32) -> u32 { down(n) } const N: u32 = down(1);"
      `shouldBe` rejectedWith (ConstEvaluationLimitExceeded (spanAt 1 57))

  test "an index past an array's end is rejected during evaluation" $
    typeCheckOutcome "const fn get(i: u32) -> u32 { let a = [1, 2, 3]; a[i] } const N: u32 = get(5);"
      `shouldBe` rejectedWith (IndexOutOfBounds 5 3 (spanAt 1 52))

  test "a const fn cannot return a reference to its local" $
    typeCheckOutcome "const fn r() -> &u32 { let x = 5; &x }"
      `shouldBe` rejectedWith (EscapingReference (spanAt 1 35))

  test "a local array length that does not fit u32 is rejected" $
    typeCheckOutcome "const N: u64 = 4294967296; fn f() { let a: [i32; N]; }"
      `shouldBe` rejectedWith (ArrayLengthTooLarge 4294967296 (spanAt 1 50))

  test "a slice index past its end is rejected during evaluation" $
    typeCheckOutcome "const fn get(xs: &[u32]) -> u32 { xs[3] } const N: u32 = get(&[1, 2]);"
      `shouldBe` rejectedWith (IndexOutOfBounds 3 2 (spanAt 1 35))

  test "the evaluation budget is shared across nested const fn calls" $
    typeCheckOutcome "const fn spin(n: u32) -> u32 { let mut i = 0; while i < n { i += 1; } i } const fn many() -> u32 { let mut k = 0; while k < 2000 { spin(1000); k += 1; } k } const N: u32 = many();"
      `shouldBe` rejectedWith (ConstEvaluationLimitExceeded (spanAt 1 173))

export
runConstEvalTests : IO ()
runConstEvalTests =
  runTests $ concat
    [ constantValueTests
    , constantControlFlowTests
    , constantStorageTests
    , constantEvaluationOrderTests
    , constantArithmeticTests
    , constantCastTests
    , constantMathValueTests
    , constEligibilityTests
    , constantLimitTests
    ]

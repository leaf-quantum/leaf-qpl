module TypeChecker.Phases.BodyCheckTest

import Test.Simple

import Compiler.TypeChecker.Data
import Compiler.TypeChecker.Type
import Frontend.Syntax.Common
import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Pass B: bodies and inference
--------------------------------------------------------------------------------
-- Pass B gives every expression, pattern and local a type (plan §5). Every
-- test runs the whole checker, so an accepted program must also satisfy the
-- effect and ownership rules; a rejected one reports its first error,
-- compared through `show`. A type error points at the expression with the
-- wrong type; an operator, cast or call error at the start of that
-- expression; a pattern error at the pattern; a qualifier error at the
-- qualifier. An unsuffixed literal whose type is still open when an error is
-- reported is shown with its default type (i32 or f64).
--------------------------------------------------------------------------------

-- Literals (plan §5.4, §5.6)
literalTests : List ETest
literalTests = Test.do
  test "an unsuffixed integer literal takes the annotated type" $
    typeCheckOutcome "fn f() { let x: u8 = 34; }" `shouldBe` accepted

  test "an unconstrained integer literal defaults to i32" $
    typeCheckOutcome "fn f() -> i32 { let i = -7; i }" `shouldBe` accepted

  test "a later use fixes an unsuffixed literal's type" $
    typeCheckOutcome "fn f() { let x = 5; let y: u8 = x; }" `shouldBe` accepted

  test "a suffixed integer literal has its suffix type" $
    typeCheckOutcome "fn f() { let x: i32 = 5u8; }"
      `shouldBe` rejectedWith (TypeMismatch i32 u8 (spanAt 1 23))

  test "an integer literal must fit its type" $
    typeCheckOutcome "fn f() { let x: u8 = 256; }"
      `shouldBe` rejectedWith (IntegerLiteralOutOfRange 256 u8 (spanAt 1 22))

  test "a negated literal is checked as one signed number" $
    typeCheckOutcome "fn f() { let x: i8 = -128; }" `shouldBe` accepted

  test "a negated literal below the signed minimum is rejected" $
    typeCheckOutcome "fn f() { let x: i8 = -129; }"
      `shouldBe` rejectedWith (IntegerLiteralOutOfRange (-129) i8 (spanAt 1 22))

  test "a defaulted integer literal must fit i32" $
    typeCheckOutcome "fn f() { let x = 3000000000; }"
      `shouldBe` rejectedWith (IntegerLiteralOutOfRange 3000000000 i32 (spanAt 1 18))

  test "a bit literal is 0 or 1" $
    typeCheckOutcome "fn f() { let b: bit = 1; let c: bit = 0; }" `shouldBe` accepted

  test "a bit literal other than 0 or 1 is rejected" $
    typeCheckOutcome "fn f() { let b: bit = 2; }"
      `shouldBe` rejectedWith (IntegerLiteralOutOfRange 2 bit (spanAt 1 23))

  test "hexadecimal, octal and binary literals take their suffix types" $
    typeCheckOutcome "fn f() { let h: u8 = 0xff_u8; let o: i16 = 0o70_i16; let b: i64 = 0b1111_1111_1001_0000i64; }"
      `shouldBe` accepted

  test "an unconstrained float literal defaults to f64" $
    typeCheckOutcome "fn f() -> f64 { let d = -1000.0; d }" `shouldBe` accepted

  test "an unsuffixed float literal takes the annotated float type" $
    typeCheckOutcome "fn f() { let x: f32 = 1.234567; let y: f64 = 1.0e-3; let z = 12E+99_f64; }"
      `shouldBe` accepted

  test "a suffixed float literal has its suffix type" $
    typeCheckOutcome "fn f() { let x: f64 = 5f32; }"
      `shouldBe` rejectedWith (TypeMismatch f64 f32 (spanAt 1 23))

  test "a float literal is not an integer" $
    typeCheckOutcome "fn f() { let x: i32 = 1.5; }"
      `shouldBe` rejectedWith (TypeMismatch i32 f64 (spanAt 1 23))

  test "boolean and unit literals have bool and unit types" $
    typeCheckOutcome "fn f() { let b: bool = true; let u: () = (); }" `shouldBe` accepted

  test "an unsuffixed float literal can be an angle" $
    typeCheckOutcome "fn f() { let a: angle64 = 3.141592653589793; let b: angle32 = 34.0; }"
      `shouldBe` accepted

  test "an f64 value is not converted to an angle implicitly" $
    typeCheckOutcome "fn f() { let x: f64 = 1.0; let a: angle64 = x; }"
      `shouldBe` rejectedWith (TypeMismatch angle64 f64 (spanAt 1 45))

  test "an integer-looking literal with a float suffix is a float" $
    typeCheckOutcome "fn f() -> f32 { 5f32 }" `shouldBe` accepted

  test "a suffixed literal must fit its suffix type" $
    typeCheckOutcome "fn f() { let h = 0x1ff_u8; }"
      `shouldBe` rejectedWith (IntegerLiteralOutOfRange 511 u8 (spanAt 1 18))

  test "exponent float literals default to f64" $
    typeCheckOutcome "fn f() -> f64 { let x = 1.0e-3; let y = 12E+99; let z = 12E+99_f64; x + y + z }"
      `shouldBe` accepted

  test "an integer literal is not a float" $
    typeCheckOutcome "fn f() { let x: f64 = 1; }"
      `shouldBe` rejectedWith (TypeMismatch f64 i32 (spanAt 1 23))

-- Param and string literals (plan §5.6, §11.1)
paramAndStringTests : List ETest
paramAndStringTests = Test.do
  test "Param takes a string literal and returns a param" $
    typeCheckOutcome "fn f() { let theta: param = Param(\"theta\"); }" `shouldBe` accepted

  test "a string literal outside Param is unsupported" $
    typeCheckOutcome "fn f() { let name = \"theta\"; }"
      `shouldBe` rejectedWith (UnsupportedFeature "string literal" (spanAt 1 21))

  test "Param takes exactly one argument" $
    typeCheckOutcome "fn f() { let t = Param(\"a\", \"b\"); }"
      `shouldBe` rejectedWith (WrongArgumentCount 1 2 (spanAt 1 18))

  test "a param has no arithmetic" $
    typeCheckOutcome "fn f() { let t = Param(\"t\"); let u = -t; }"
      `shouldBe` rejectedWith (InvalidUnaryOperand "-" param (spanAt 1 38))

  test "a string literal inside a tuple is unsupported" $
    typeCheckOutcome "fn f() { let t = (\"theta\", 1); }"
      `shouldBe` rejectedWith (UnsupportedFeature "string literal" (spanAt 1 19))

  test "Param's argument must be the string literal itself" $
    typeCheckOutcome "fn f(c: bool) { let t = Param(if c { \"a\" } else { \"b\" }); }"
      `shouldBe` rejectedWith (UnsupportedFeature "string literal" (spanAt 1 38))

  test "a user function named Param shadows the prelude Param" $
    typeCheckOutcome "fn Param(x: i32) -> i32 { x } fn f() -> i32 { Param(1) }" `shouldBe` accepted

  test "a string literal passed to a user function named Param is unsupported" $
    typeCheckOutcome "fn Param(x: i32) -> i32 { x } fn f() -> i32 { Param(\"theta\") }"
      `shouldBe` rejectedWith (UnsupportedFeature "string literal" (spanAt 1 53))

-- Excluded qstate constructs and misplaced builtins (plan §1.4, §1.5 item 8)
excludedConstructTests : List ETest
excludedConstructTests = Test.do
  test "a qstate local type is unsupported" $
    typeCheckOutcome "fn f() { let s: qstate; }"
      `shouldBe` rejectedWith (UnsupportedFeature "qstate" (spanAt 1 17))

  test "a basis-string value is unsupported" $
    typeCheckOutcome "fn f() { let state = bs\"1011\"; }"
      `shouldBe` rejectedWith (UnsupportedFeature "basis-string value" (spanAt 1 22))

  test "tensor is unsupported" $
    typeCheckOutcome "fn f() { let q = qalloc(); let t = tensor(q); }"
      `shouldBe` rejectedWith (UnsupportedFeature "tensor" (spanAt 1 36))

  test "the prelude phase function is unsupported" $
    typeCheckOutcome "fn f() { let p = phase(1.5); }"
      `shouldBe` rejectedWith (UnsupportedFeature "phase" (spanAt 1 18))

  test "a builtin used as a value is an invalid builtin context" $
    typeCheckOutcome "fn f() { let m = measr; }"
      `shouldBe` rejectedWith (InvalidBuiltinContext "measr" (spanAt 1 18))

  test "a contract predicate in an expression is an invalid builtin context" $
    typeCheckOutcome "fn f(q: &qbit) { let c = clean(q); }"
      `shouldBe` rejectedWith (InvalidBuiltinContext "clean" (spanAt 1 26))

  test "a stray apply is an invalid builtin context" $
    typeCheckOutcome "fn f() { let a = apply; }"
      `shouldBe` rejectedWith (InvalidBuiltinContext "apply" (spanAt 1 18))

  test "a stray on is an invalid builtin context" $
    typeCheckOutcome "fn f() { let o = on; }"
      `shouldBe` rejectedWith (InvalidBuiltinContext "on" (spanAt 1 18))

  test "basis in an expression is an invalid builtin context" $
    typeCheckOutcome "fn f(q: &qbit) { let c = basis(q, X); }"
      `shouldBe` rejectedWith (InvalidBuiltinContext "basis" (spanAt 1 26))

  test "isolated in an expression is an invalid builtin context" $
    typeCheckOutcome "fn f(q: &qbit) { let c = isolated(q); }"
      `shouldBe` rejectedWith (InvalidBuiltinContext "isolated" (spanAt 1 26))

  test "product in an expression is an invalid builtin context" $
    typeCheckOutcome "fn f(q: &qbit, r: &qbit) { let c = product(q, r); }"
      `shouldBe` rejectedWith (InvalidBuiltinContext "product" (spanAt 1 36))

  test "separable in an expression is an invalid builtin context" $
    typeCheckOutcome "fn f(q: &qbit) { let c = separable(q); }"
      `shouldBe` rejectedWith (InvalidBuiltinContext "separable" (spanAt 1 26))

  test "stabilized in an expression is an invalid builtin context" $
    typeCheckOutcome "fn f(q: &qbit) { let c = stabilized(q); }"
      `shouldBe` rejectedWith (InvalidBuiltinContext "stabilized" (spanAt 1 26))

  test "the prelude phase function is unsupported as a value" $
    typeCheckOutcome "fn f() { let p = phase; }"
      `shouldBe` rejectedWith (UnsupportedFeature "phase" (spanAt 1 18))

  test "a user function named phase shadows the excluded prelude helper" $
    typeCheckOutcome "fn phase(x: f64) -> f64 { x } fn f() -> f64 { phase(1.5) }" `shouldBe` accepted

-- Names (plan §5.6)
nameTests : List ETest
nameTests = Test.do
  test "a local has the type of its initializer" $
    typeCheckOutcome "fn f() -> bool { let b = true; b }" `shouldBe` accepted

  test "a shadowing local has its own type" $
    typeCheckOutcome "fn f() -> bool { let x = 1; let x = true; x }" `shouldBe` accepted

  test "a local may shadow a prelude function" $
    typeCheckOutcome "fn f() -> i32 { let sin = 3; sin + 1 }" `shouldBe` accepted

  test "a function name used as a value has the function's type" $
    typeCheckOutcome "classical fn inc(x: i32) -> i32 { x + 1 } fn f() -> i32 { let g = inc; g(1) }"
      `shouldBe` accepted

  test "a local may shadow a user function" $
    typeCheckOutcome "fn g() -> bool { true } fn f() -> i32 { let g = 1; g + 1 }" `shouldBe` accepted

-- Operators (plan §5.6)
operatorTests : List ETest
operatorTests = Test.do
  test "arithmetic operators on integers" $
    typeCheckOutcome "fn f() { let add = 5 + 3; let sub = 10 - 4; let mul = 6 * 2; let div = 12 / 3; let rem = 10 % 3; }"
      `shouldBe` accepted

  test "arithmetic on floats" $
    typeCheckOutcome "fn f(x: f32) -> f32 { let y = 2.0; x + y }" `shouldBe` accepted

  test "arithmetic operands must have the same numeric type" $
    typeCheckOutcome "fn f(a: i32, b: i64) -> i64 { a + b }"
      `shouldBe` rejectedWith (InvalidBinaryOperands "+" i32 i64 (spanAt 1 31))

  test "arithmetic is not defined on booleans" $
    typeCheckOutcome "fn f(a: bool, b: bool) { let c = a + b; }"
      `shouldBe` rejectedWith (InvalidBinaryOperands "+" bool bool (spanAt 1 34))

  test "negation applies to signed integers and floats" $
    typeCheckOutcome "fn f(a: i32, b: f64) { let x = -a; let y = -b; }" `shouldBe` accepted

  test "negation does not apply to unsigned integers" $
    typeCheckOutcome "fn f(a: u32) { let x = -a; }"
      `shouldBe` rejectedWith (InvalidUnaryOperand "-" u32 (spanAt 1 24))

  test "! negates booleans and complements integers" $
    typeCheckOutcome "fn f(a: bool, b: u8) { let c = !a; let d: u8 = !b; }" `shouldBe` accepted

  test "! does not apply to floats" $
    typeCheckOutcome "fn f(a: f64) { let c = !a; }"
      `shouldBe` rejectedWith (InvalidUnaryOperand "!" f64 (spanAt 1 24))

  test "logical operators take booleans" $
    typeCheckOutcome "fn f(a: bool, b: bool) -> bool { a && b || !a }" `shouldBe` accepted

  test "logical operators require booleans" $
    typeCheckOutcome "fn f(a: i32, b: bool) -> bool { a && b }"
      `shouldBe` rejectedWith (InvalidBinaryOperands "&&" i32 bool (spanAt 1 33))

  test "bitwise operators accept bits, booleans and integers" $
    typeCheckOutcome "fn f(a: bit, b: bit, c: bool, d: u8) { let and_bit: bit = a & b; let or_bit: bit = a | b; let xor_bit: bit = a ^ b; let e = c & c; let g = d ^ d; }"
      `shouldBe` accepted

  test "bitwise operators do not accept floats" $
    typeCheckOutcome "fn f(a: f64) { let b = a & a; }"
      `shouldBe` rejectedWith (InvalidBinaryOperands "&" f64 f64 (spanAt 1 24))

  test "a comparison produces bool" $
    typeCheckOutcome "fn f(a: i32) -> bool { a < 5 }" `shouldBe` accepted

  test "a comparison is not an integer" $
    typeCheckOutcome "fn f(a: i32) -> i32 { a < 5 }"
      `shouldBe` rejectedWith (TypeMismatch i32 bool (spanAt 1 23))

  test "owned qubits cannot be compared" $
    typeCheckOutcome "fn f(q: qbit, r: qbit) -> bool { q == r }"
      `shouldBe` rejectedWith (InvalidBinaryOperands "==" linearQbit linearQbit (spanAt 1 34))

  test "shift operands may have different integer types" $
    typeCheckOutcome "fn f(a: u8, s: i32) -> u8 { a << s }" `shouldBe` accepted

  test "a shift has its left operand's type" $
    typeCheckOutcome "fn f(a: u8, s: i32) -> i32 { a << s }"
      `shouldBe` rejectedWith (TypeMismatch i32 u8 (spanAt 1 30))

  test "a shift requires integer operands" $
    typeCheckOutcome "fn f(a: f64, s: u32) -> f64 { a << s }"
      `shouldBe` rejectedWith (InvalidBinaryOperands "<<" f64 u32 (spanAt 1 31))

  test "operators accept a shared reference to a primitive" $
    typeCheckOutcome "fn f() -> i32 { let x = 10; let r = &x; r + 1 }" `shouldBe` accepted

  test "a comparison accepts two references of the same type" $
    typeCheckOutcome "fn f(a: &i32, b: &i32) -> bool { a == b }" `shouldBe` accepted

  test "negation applies to angles" $
    typeCheckOutcome "fn f(a: angle64) { let x = -a; }" `shouldBe` accepted

  test "arithmetic does not read through a mutable reference" $
    typeCheckOutcome "fn f(r: &mut i32) { let x = r + 1; }"
      `shouldBe` rejectedWith (InvalidBinaryOperands "+" (refMut i32) i32 (spanAt 1 29))

  test "logical operators do not accept bits" $
    typeCheckOutcome "fn f(a: bit, b: bit) { let c = a && b; }"
      `shouldBe` rejectedWith (InvalidBinaryOperands "&&" bit bit (spanAt 1 32))

  test "comparison operands must have one type" $
    typeCheckOutcome "fn f(a: i32, b: i64) -> bool { a < b }"
      `shouldBe` rejectedWith (InvalidBinaryOperands "<" i32 i64 (spanAt 1 32))

-- Compound assignment (plan §5.6 Assignment)
compoundAssignmentTests : List ETest
compoundAssignmentTests = Test.do
  test "every compound assignment operator applies its operator's rule" $
    typeCheckOutcome "fn f() { let mut x = 0; x += 5; x -= 2; x *= 2; x /= 3; x %= 4; x &= 1; x |= 1; x ^= 1; x <<= 1; x >>= 1; }"
      `shouldBe` accepted

  test "compound addition fixes an unsuffixed target's type" $
    typeCheckOutcome "fn f(xs: [i32; 3]) -> i32 { let mut total = 0; for i in 0..3 { total += xs[i]; } total }"
      `shouldBe` accepted

  test "compound assignment operands must be compatible" $
    typeCheckOutcome "fn f(b: bool) { let mut x: i32 = 0; x += b; }"
      `shouldBe` rejectedWith (InvalidBinaryOperands "+=" i32 bool (spanAt 1 37))

  test "compound shifts take any integer amount but compound addition needs one type" $
    typeCheckOutcome "fn f(a: i32) { let mut x: u8 = 0; x <<= a; let mut y: i64 = 1; y += a; }"
      `shouldBe` rejectedWith (InvalidBinaryOperands "+=" i64 i32 (spanAt 1 64))

  test "a compound assignment updates an element through a mutable slice" $
    typeCheckOutcome "fn f(xs: &mut [i32]) { xs[0] += 1; }" `shouldBe` accepted

  test "a compound assignment through a shared slice is rejected" $
    typeCheckOutcome "fn f(xs: &[i32]) { xs[0] += 1; }"
      `shouldBe` rejectedWith (AssignmentThroughSharedReference (spanAt 1 20))

-- Casts (plan §5.6)
castTests : List ETest
castTests = Test.do
  test "integers cast to integers, floats and angles" $
    typeCheckOutcome "fn f() { let a = 34 as i8; let b = 34 as u128; let c = 34 as f32; let d = 34 as angle32; }"
      `shouldBe` accepted

  test "floats cast to integers and angles" $
    typeCheckOutcome "fn f() { let a = 34.5 as i32; let b = 1.5 as angle64; let c = 2.5 as f32; }"
      `shouldBe` accepted

  test "bool and bit cast to integers" $
    typeCheckOutcome "fn f(b: bit, c: bool) { let x = b as i32; let y = c as u8; }" `shouldBe` accepted

  test "an integer does not cast to bool" $
    typeCheckOutcome "fn f(x: i32) { let b = x as bool; }"
      `shouldBe` rejectedWith (InvalidCast i32 bool (spanAt 1 24))

  test "an integer does not cast to bit" $
    typeCheckOutcome "fn f(x: i32) { let b = x as bit; }"
      `shouldBe` rejectedWith (InvalidCast i32 bit (spanAt 1 24))

  test "an angle does not cast to a float" $
    typeCheckOutcome "fn f(a: angle64) { let x = a as f64; }"
      `shouldBe` rejectedWith (InvalidCast angle64 f64 (spanAt 1 28))

  test "a qubit reference does not cast to an integer" $
    typeCheckOutcome "fn f(q: &qbit) { let x = q as i32; }"
      `shouldBe` rejectedWith (InvalidCast qbitRef i32 (spanAt 1 26))

  test "unit does not cast to an integer" $
    typeCheckOutcome "fn f() { let x = () as i32; }"
      `shouldBe` rejectedWith (InvalidCast unit i32 (spanAt 1 18))

  test "bool does not cast to a float" $
    typeCheckOutcome "fn f(b: bool) { let x = b as f64; }"
      `shouldBe` rejectedWith (InvalidCast bool f64 (spanAt 1 25))

-- Tuples (plan §5.6)
tupleTests : List ETest
tupleTests = Test.do
  test "tuple types and positional indexing" $
    typeCheckOutcome "fn f() -> bool { let t: (i32, f64, bool) = (1, 3.14, true); let x = t.0; let y: f64 = t.1; t.2 }"
      `shouldBe` accepted

  test "a tuple must have its annotation's arity" $
    typeCheckOutcome "fn f(a: i32) { let t: (i32, i32) = (a, a, a); }"
      `shouldBe` rejectedWith (TypeMismatch (tuple [i32, i32]) (tuple [i32, i32, i32]) (spanAt 1 36))

  test "a tuple index must be within the tuple's arity" $
    typeCheckOutcome "fn f() { let t = (1, 2); let x = t.2; }"
      `shouldBe` rejectedWith (IndexOutOfBounds 2 2 (spanAt 1 34))

  test "a tuple index on a non-tuple is rejected" $
    typeCheckOutcome "fn f(x: i32) { let y = x.0; }"
      `shouldBe` rejectedWith (NotIndexable i32 (spanAt 1 24))

  test "a tuple pattern splits a tuple" $
    typeCheckOutcome "fn f() { let (a, b, c) = (1, 2, 3); let (x, _, z) = (1, 2, 3); }" `shouldBe` accepted

  test "a tuple pattern must have the tuple's arity" $
    typeCheckOutcome "fn f() { let (a, b) = (1, 2, 3); }"
      `shouldBe` rejectedWith (WrongPatternArity 3 2 (spanAt 1 14))

-- Arrays, repetition and indexing (plan §5.6)
arrayTests : List ETest
arrayTests = Test.do
  test "array literals with annotated and inferred types" $
    typeCheckOutcome "fn f() { let bs: [bool; 4] = [true, false, true, false]; let is = [1, 2, 3]; let fs = [1.0, 2.0, 3.0]; let units = [(), ()]; }"
      `shouldBe` accepted

  test "array elements must share one type" $
    typeCheckOutcome "fn f(x: i32) { let a = [x, true]; }"
      `shouldBe` rejectedWith (TypeMismatch i32 bool (spanAt 1 28))

  test "an array literal must have its annotation's length" $
    typeCheckOutcome "fn f() { let a: [i32; 2] = [1, 2, 3]; }"
      `shouldBe` rejectedWith (TypeMismatch (array i32 2) (array i32 3) (spanAt 1 28))

  test "a repeat expression has the element type and the count" $
    typeCheckOutcome "fn f() { let zeros = [0; 3]; let a: [i32; 3] = zeros; }" `shouldBe` accepted

  test "a repeat count must equal the annotated length" $
    typeCheckOutcome "fn f() { let a: [i32; 4] = [0; 3]; }"
      `shouldBe` rejectedWith (TypeMismatch (array i32 4) (array i32 3) (spanAt 1 28))

  test "a constant may be a repeat count" $
    typeCheckOutcome "const N: u32 = 3; fn f() { let a: [i32; 3] = [0; N]; }" `shouldBe` accepted

  test "a repeat count must be unsigned" $
    typeCheckOutcome "const N: i32 = 3; fn f() { let a = [0; N]; }"
      `shouldBe` rejectedWith (InvalidArrayLength i32 (spanAt 1 40))

  test "a constant may size a local array annotation" $
    typeCheckOutcome "const N: u64 = 4; fn f() { let c: [i32; N] = [0; 4]; }" `shouldBe` accepted

  test "an empty array takes its element type from the annotation" $
    typeCheckOutcome "fn f() { let a: [i32; 0] = []; }" `shouldBe` accepted

  test "a later use can fix an empty array's element type" $
    typeCheckOutcome "fn f() { let a = []; let b: [i32; 0] = a; }" `shouldBe` accepted

  test "an empty array nothing constrains cannot be inferred" $
    typeCheckOutcome "fn f() { let a = []; }"
      `shouldBe` rejectedWith (CannotInferType (spanAt 1 14))

  test "an array index has type u32" $
    typeCheckOutcome "fn f(a: [i32; 3], i: u32) -> i32 { a[i] }" `shouldBe` accepted

  test "an index position fixes a loop variable to u32" $
    typeCheckOutcome "fn f(a: [i32; 4]) -> i32 { let mut s = 0; for i in 0..4 { s += a[i]; } s }"
      `shouldBe` accepted

  test "an index must be u32" $
    typeCheckOutcome "fn f(a: [i32; 3], i: i32) -> i32 { a[i] }"
      `shouldBe` rejectedWith (TypeMismatch u32 i32 (spanAt 1 38))

  test "a constant index past the end is rejected" $
    typeCheckOutcome "fn f(a: [i32; 3]) -> i32 { a[3] }"
      `shouldBe` rejectedWith (IndexOutOfBounds 3 3 (spanAt 1 30))

  test "only arrays and slices can be indexed" $
    typeCheckOutcome "fn f(x: i32) -> i32 { x[0] }"
      `shouldBe` rejectedWith (NotIndexable i32 (spanAt 1 23))

  test "an array reference can be indexed" $
    typeCheckOutcome "fn f(a: &[i32; 3]) -> i32 { a[0] }" `shouldBe` accepted

  test "an element can be written through a mutable array reference" $
    typeCheckOutcome "fn f(a: &mut [i32; 3]) { a[0] = 1; }" `shouldBe` accepted

  test "an unsuffixed length literal defaults to u32, not i32" $
    typeCheckOutcome "fn f() { let a: [bool; 3000000000]; }" `shouldBe` accepted

  test "an unsuffixed length literal must fit u32" $
    typeCheckOutcome "fn f() { let a: [bool; 4294967296]; }"
      `shouldBe` rejectedWith (IntegerLiteralOutOfRange 4294967296 u32 (spanAt 1 24))

-- Slices (plan §5.6, spec §9)
sliceTests : List ETest
sliceTests = Test.do
  test "an array can be sliced with every range form" $
    typeCheckOutcome "fn f() { let a: [i32; 5] = [10, 20, 30, 40, 50]; let s1: &[i32] = &a[..]; let s2: &[i32] = &a[1..4]; let s3: &[i32] = &a[1..=3]; let s4: &[i32] = &a[2..]; let s5: &[i32] = &a[..3]; let s6: &[i32] = &a[..=3]; let s7 = &a[1..4]; }"
      `shouldBe` accepted

  test "a slice can be indexed and sliced again" $
    typeCheckOutcome "fn f(s: &[i32]) -> i32 { let x = s[0]; let mid: &[i32] = &s[1..3]; x + mid[0] }"
      `shouldBe` accepted

  test "a mutable slice of a mutable array can be written" $
    typeCheckOutcome "fn f() { let mut m: [i32; 5] = [10, 20, 30, 40, 50]; let w: &mut [i32] = &mut m[1..4]; w[0] = 99; }"
      `shouldBe` accepted

  test "a write through a shared slice is rejected" $
    typeCheckOutcome "fn f() { let mut m: [i32; 5] = [10, 20, 30, 40, 50]; let r: &[i32] = &m[..]; r[0] = 0; }"
      `shouldBe` rejectedWith (AssignmentThroughSharedReference (spanAt 1 78))

  test "a range index must be used through a reference" $
    typeCheckOutcome "fn f(a: [i32; 5]) { let s = a[1..3]; }"
      `shouldBe` rejectedWith (UnsizedValue (slice i32) (spanAt 1 29))

  test "a slice range past the array's end is rejected" $
    typeCheckOutcome "fn f(a: [i32; 5]) { let s = &a[2..6]; }"
      `shouldBe` rejectedWith (IndexOutOfBounds 6 5 (spanAt 1 35))

  test "an inclusive slice end at the length is out of bounds" $
    typeCheckOutcome "fn f(a: [i32; 5]) { let s = &a[..=5]; }"
      `shouldBe` rejectedWith (IndexOutOfBounds 5 5 (spanAt 1 35))

  test "a slice range must not run backwards" $
    typeCheckOutcome "fn f(a: [i32; 5]) { let s = &a[3..1]; }"
      `shouldBe` rejectedWith (ReversedRange 3 1 (spanAt 1 32))

  test "a qubit slice lends its qubits in place" $
    typeCheckOutcome "fn f() { let qs: [qbit; 4] = qalloc(4); let qv: &[qbit] = &qs[..]; H(&qv[0]); CX(&qv[1], &qv[2]); discard(qs); }"
      `shouldBe` accepted

  test "an array reference coerces to a slice at a call" $
    typeCheckOutcome "classical fn first(xs: &[i32]) -> i32 { xs[0] } fn f() -> i32 { let a = [1, 2, 3]; first(&a) }"
      `shouldBe` accepted

  test "an owned array does not coerce to a slice reference" $
    typeCheckOutcome "classical fn first(xs: &[i32]) -> i32 { xs[0] } fn f() -> i32 { let a = [1, 2, 3]; first(a) }"
      `shouldBe` rejectedWith (TypeMismatch (ref (slice i32)) (array i32 3) (spanAt 1 90))

-- References (plan §1.5 item 4, §5.6 Borrows)
referenceTests : List ETest
referenceTests = Test.do
  test "shared and mutable references to classical values" $
    typeCheckOutcome "fn f() { let x = 10; let r: &i32 = &x; let mut y = 10; let s: &mut i32 = &mut y; }"
      `shouldBe` accepted

  test "a mutable reference to a qubit is rejected" $
    typeCheckOutcome "fn f(q: qbit) -> qbit { let r = &mut q; q }"
      `shouldBe` rejectedWith (InvalidQbitReference (spanAt 1 33))

  test "a mutable reference to an aggregate holding a qubit is rejected" $
    typeCheckOutcome "fn f(p: (i32, qbit)) -> (i32, qbit) { let r = &mut p; p }"
      `shouldBe` rejectedWith (InvalidQbitReference (spanAt 1 47))

  test "a mutable reference is accepted where a shared one is expected" $
    typeCheckOutcome "classical fn read(x: &i32) -> i32 { x + 0 } fn f() -> i32 { let mut v = 5; let r = &mut v; read(r) }"
      `shouldBe` accepted

  test "a shared reference is not accepted where a mutable one is expected" $
    typeCheckOutcome "classical fn bump(x: &mut [i32]) { x[0] = 1; } fn f() { let a = [1, 2]; bump(&a); }"
      `shouldBe` rejectedWith (TypeMismatch (refMut (slice i32)) (ref (array i32 2)) (spanAt 1 78))

-- Named members (plan §1.4, §5.6 Members)
memberTests : List ETest
memberTests = Test.do
  test "a named field read is an unknown member" $
    typeCheckOutcome "fn f() { let t = (1, 2); let x = t.first; }"
      `shouldBe` rejectedWith (UnknownMember "first" (spanAt 1 36))

  test "a method call is an unknown member" $
    typeCheckOutcome "fn f() { let a = [1, 2]; let n = a.size(); }"
      `shouldBe` rejectedWith (UnknownMember "size" (spanAt 1 36))

  test "a chain of member reads reports its first member" $
    typeCheckOutcome "fn f() { let t = (1, 2); let x = t.first.second; }"
      `shouldBe` rejectedWith (UnknownMember "first" (spanAt 1 36))

  test "a field assignment is an unknown member" $
    typeCheckOutcome "fn f() { let mut t = (1, 2); t.first = 3; }"
      `shouldBe` rejectedWith (UnknownMember "first" (spanAt 1 32))

  test "a method call's arguments are checked before its member" $
    typeCheckOutcome "fn f(b: bool) { let a = [1, 2]; let n = a.size(b + b); }"
      `shouldBe` rejectedWith (InvalidBinaryOperands "+" bool bool (spanAt 1 48))

-- Calls (plan §5.6 Calls)
callTests : List ETest
callTests = Test.do
  test "a call must supply every parameter and no more" $
    typeCheckOutcome "fn g(x: i32) -> i32 { x } fn f() -> i32 { g(1, 2) }"
      `shouldBe` rejectedWith (WrongArgumentCount 1 2 (spanAt 1 43))

  test "only functions can be called" $
    typeCheckOutcome "fn f(x: i32) -> i32 { x(1) }"
      `shouldBe` rejectedWith (NotCallable i32 (spanAt 1 23))

  test "a function-typed parameter is called with its declared signature" $
    typeCheckOutcome "fn f(g: classical fn(x: i32) -> bool) -> bool { g(1) }" `shouldBe` accepted

  test "a call through a function-typed parameter checks its arguments" $
    typeCheckOutcome "fn f(g: classical fn(x: i32) -> bool) -> bool { g(true) }"
      `shouldBe` rejectedWith (TypeMismatch i32 bool (spanAt 1 51))

  test "a user function has no automatic borrowed form" $
    typeCheckOutcome "fn g(q: qbit) -> qbit { q } fn f() { let q = qalloc(); g(&q); discard(q); }"
      `shouldBe` rejectedWith (TypeMismatch linearQbit qbitRef (spanAt 1 58))

  test "a call must supply every parameter" $
    typeCheckOutcome "fn g(x: i32, y: i32) -> i32 { x } fn f() -> i32 { g(1) }"
      `shouldBe` rejectedWith (WrongArgumentCount 2 1 (spanAt 1 51))

-- Function values: directional assignability (plan §5.3)
functionValueTests : List ETest
functionValueTests = Test.do
  test "an uncompsafe function satisfies a unitary function type" $
    typeCheckOutcome "uncompsafe fn flip(q: qbit) -> qbit { X(q) } fn run(g: unitary fn(q: qbit) -> qbit, q: qbit) -> qbit { g(q) } fn f() -> qbit { run(flip, qalloc()) }"
      `shouldBe` accepted

  test "a unitary function does not satisfy an uncompsafe function type" $
    typeCheckOutcome "unitary fn had(q: qbit) -> qbit { H(q) } fn run(g: uncompsafe fn(q: qbit) -> qbit, q: qbit) -> qbit { g(q) } fn f() -> qbit { run(had, qalloc()) }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectUncompsafe [linearQbit] linearQbit) (fnType EffectUnitary [linearQbit] linearQbit) (spanAt 1 131))

  test "a classical function satisfies a general function type" $
    typeCheckOutcome "classical fn inc(x: i32) -> i32 { x + 1 } fn run(g: fn(x: i32) -> i32) -> i32 { g(1) } fn f() -> i32 { run(inc) }"
      `shouldBe` accepted

  test "an isometry does not satisfy a coisometry function type" $
    typeCheckOutcome "isometry fn grow(q: qbit) -> (qbit, qbit) { (q, qalloc()) } fn run(g: coisometry fn(q: qbit) -> (qbit, qbit), q: qbit) -> (qbit, qbit) { g(q) } fn f() -> (qbit, qbit) { run(grow, qalloc()) }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectCoisometry [linearQbit] (tuple [linearQbit, linearQbit])) (fnType EffectIsometry [linearQbit] (tuple [linearQbit, linearQbit])) (spanAt 1 174))

  test "function parameter multiplicities must match exactly" $
    typeCheckOutcome "fn keep(q: affine qbit) -> affine qbit { q } fn run(g: fn(q: qbit) -> qbit, q: qbit) -> qbit { g(q) } fn f() -> qbit { run(keep, qalloc()) }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectGeneral [linearQbit] linearQbit) (fnType EffectGeneral [affineQbit] affineQbit) (spanAt 1 124))

  test "a function value's result type must match" $
    typeCheckOutcome "classical fn inc(x: i32) -> i32 { x + 1 } fn run(g: classical fn(x: i32) -> bool) -> bool { g(1) } fn f() -> bool { run(inc) }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectClassical [i32] bool) (fnType EffectClassical [i32] i32) (spanAt 1 121))

-- Conditionals (plan §5.6)
conditionalTests : List ETest
conditionalTests = Test.do
  test "an if condition may be a bool" $
    typeCheckOutcome "fn f() -> i32 { if 7 > 5 { 1 } else { 2 } }" `shouldBe` accepted

  test "an if condition may be a bit" $
    typeCheckOutcome "fn f(b: bit) -> i32 { if b { 1 } else { 0 } }" `shouldBe` accepted

  test "an if condition must be a bool or a bit" $
    typeCheckOutcome "fn f(n: i32) -> i32 { if n { 1 } else { 0 } }"
      `shouldBe` rejectedWith (InvalidConditionType "if" i32 (spanAt 1 26))

  test "if branches join to one type" $
    typeCheckOutcome "fn f(flag: bool) { let x: i32 = if flag { 1 } else { 2 }; }" `shouldBe` accepted

  test "if branches of different types are rejected" $
    typeCheckOutcome "fn f(flag: bool, a: i32) -> i32 { if flag { a } else { true } }"
      `shouldBe` rejectedWith (TypeMismatch i32 bool (spanAt 1 56))

  test "an else-if chain joins every branch" $
    typeCheckOutcome "fn f(x: i32) -> i32 { if x < 0 { -1 } else if x == 0 { 0 } else { 1 } }"
      `shouldBe` accepted

  test "an if without else must have a unit block" $
    typeCheckOutcome "fn f(flag: bool, a: i32) { if flag { a }; }"
      `shouldBe` rejectedWith (TypeMismatch unit i32 (spanAt 1 38))

  test "a diverging branch does not constrain the if's type" $
    typeCheckOutcome "fn f(flag: bool) -> i32 { let x = if flag { return 0; } else { 5 }; x }"
      `shouldBe` accepted

  test "a branch join keeps qubit multiplicities invariant" $
    typeCheckOutcome "fn f(c: bool, a: qbit, b: affine qbit) { let q = if c { a } else { b }; discard(q); }"
      `shouldBe` rejectedWith (TypeMismatch linearQbit affineQbit (spanAt 1 68))

  test "a branch join does not coerce an array reference to a slice" $
    typeCheckOutcome "fn f(c: bool, a: &[i32; 2], s: &[i32]) { let r = if c { a } else { s }; }"
      `shouldBe` rejectedWith (TypeMismatch (ref (array i32 2)) (ref (slice i32)) (spanAt 1 68))

  test "an expected slice type reaches both branches" $
    typeCheckOutcome "fn f(c: bool, a: &[i32; 2], s: &[i32]) { let r: &[i32] = if c { a } else { s }; }"
      `shouldBe` accepted

-- Loops (plan §5.6)
loopTests : List ETest
loopTests = Test.do
  test "a while condition may be a bool or a bit" $
    typeCheckOutcome "fn f(b: bit) { let mut count = 0; while count <= 5 { count += 1; } while b { } }"
      `shouldBe` accepted

  test "a while condition must be a bool or a bit" $
    typeCheckOutcome "fn f(n: i32) { while n { } }"
      `shouldBe` rejectedWith (InvalidConditionType "while" i32 (spanAt 1 22))

  test "a loop has the type of its break values" $
    typeCheckOutcome "fn f() -> i32 { let mut count = 0; let result = loop { if count == 3 { break count; } count += 1; }; result }"
      `shouldBe` accepted

  test "a bare break contributes unit to its loop's type" $
    typeCheckOutcome "fn f() -> i32 { loop { break; } }"
      `shouldBe` rejectedWith (TypeMismatch i32 unit (spanAt 1 24))

  test "a loop without a break never produces a value" $
    typeCheckOutcome "fn f() -> i32 { loop { } }" `shouldBe` accepted

  test "a loop's break values join" $
    typeCheckOutcome "fn f(c: bool) -> i32 { loop { if c { break 1; } else { break 2; } } }"
      `shouldBe` accepted

  test "a loop's break values must share a type" $
    typeCheckOutcome "fn f(c: bool, a: i32) -> i32 { loop { if c { break a; } else { break true; } } }"
      `shouldBe` rejectedWith (TypeMismatch i32 bool (spanAt 1 70))

  test "a while loop cannot break with a value" $
    typeCheckOutcome "fn f() { while true { break 5; } }"
      `shouldBe` rejectedWith (BreakValueInUnitLoop (spanAt 1 23))

  test "a for loop cannot break with a value" $
    typeCheckOutcome "fn f() { for i in 0..3 { break 1; } }"
      `shouldBe` rejectedWith (BreakValueInUnitLoop (spanAt 1 26))

-- for loops (plan §5.6, spec §32)
forLoopTests : List ETest
forLoopTests = Test.do
  test "a for loop over a range binds integers" $
    typeCheckOutcome "fn f() -> u32 { let mut s: u32 = 0; for i in 1..6 { s += i; } s }" `shouldBe` accepted

  test "a for loop over a reversed range binds integers" $
    typeCheckOutcome "fn f() -> u32 { let mut s: u32 = 0; for i in rev(1..6) { s += i; } s }"
      `shouldBe` accepted

  test "a for loop over an owned array binds its elements" $
    typeCheckOutcome "fn f() -> i32 { let a = [1, 2, 3]; let mut s = 0; for x in a { s += x; } s }"
      `shouldBe` accepted

  test "a for loop over a borrowed array binds element references" $
    typeCheckOutcome "fn f() -> i32 { let a = [1, 2, 3]; let mut s = 0; for x in &a { s += x; } s }"
      `shouldBe` accepted

  test "a for loop over borrowed qubits binds qubit references" $
    typeCheckOutcome "fn f() { let qs = qalloc(4); for q in &qs { H(q); } discard(qs); }" `shouldBe` accepted

  test "a constant loop bound written in parentheses before a block" $
    typeCheckOutcome "const N: u32 = 3; fn f() -> u32 { let mut s: u32 = 0; for i in 0..(N) { s += i; } s }"
      `shouldBe` accepted

  test "a range stored in a local can be iterated" $
    typeCheckOutcome "fn f() { let r = 0..3; for i in r { } }" `shouldBe` accepted

  test "a range without a start cannot be iterated" $
    typeCheckOutcome "fn f() { for i in ..5 { } }"
      `shouldBe` rejectedWith (MissingRangeEndpoint "for" (spanAt 1 19))

  test "a constant-named for variable is a refutable pattern" $
    typeCheckOutcome "const ZERO: u32 = 0; fn f() { for ZERO in 0..3 { } }"
      `shouldBe` rejectedWith (RefutableBindingPattern (spanAt 1 35))

  test "an open-ended range can drive a for loop" $
    typeCheckOutcome "fn f() { let r = 0..; for i in r { if i == 3 { break; } } }" `shouldBe` accepted

  test "a for loop over a slice reference binds element references" $
    typeCheckOutcome "fn f(xs: &[i32]) -> i32 { let mut s = 0; for x in xs { s += x; } s }"
      `shouldBe` accepted

  test "a for loop over a mutable array reference binds mutable element references" $
    typeCheckOutcome "fn f() { let mut a = [1, 2]; for x in &mut a { let r: &mut i32 = x; } }"
      `shouldBe` accepted

  test "a for loop over a shared array reference does not bind mutable references" $
    typeCheckOutcome "fn f() { let a = [1, 2]; for x in &a { let r: &mut i32 = x; } }"
      `shouldBe` rejectedWith (TypeMismatch (refMut i32) (ref i32) (spanAt 1 58))

  test "a unit constant-named for variable is an irrefutable pattern" $
    typeCheckOutcome "const UNIT: () = (); fn f() { for UNIT in [(), ()] { } }" `shouldBe` accepted

-- Ranges (plan §5.6, spec §31)
rangeTests : List ETest
rangeTests = Test.do
  test "ranges are values" $
    typeCheckOutcome "fn f(a: i32, b: i32) { let r1 = a..b; let r2 = a..=b; let r3 = 1..; let r4 = ..5; let r5 = ..=5; }"
      `shouldBe` accepted

  test "range endpoints must have one type" $
    typeCheckOutcome "fn f(a: i32, b: i64) { let r = a..b; }"
      `shouldBe` rejectedWith (TypeMismatch i32 i64 (spanAt 1 35))

  test "rev reverses a range with both endpoints" $
    typeCheckOutcome "fn f(n: u32) { let r = rev(0..n); }" `shouldBe` accepted

  test "rev requires a range with both endpoints" $
    typeCheckOutcome "fn f() { let r = rev(1..); }"
      `shouldBe` rejectedWith (MissingRangeEndpoint "rev" (spanAt 1 22))

-- Blocks, returns and divergence (plan §1.2, §5.6)
blockTests : List ETest
blockTests = Test.do
  test "a block has the value of its tail expression" $
    typeCheckOutcome "fn f() -> i32 { let x = { let a = 1; let b = 2; a + b }; x }" `shouldBe` accepted

  test "a block without a tail has unit type" $
    typeCheckOutcome "fn f() { let unit: () = { let a = 1; }; }" `shouldBe` accepted

  test "a block's type must fit its use" $
    typeCheckOutcome "fn f() { let x: i32 = { let a = 1; }; }"
      `shouldBe` rejectedWith (TypeMismatch i32 unit (spanAt 1 23))

  test "an explicit return is checked against the declared result" $
    typeCheckOutcome "fn f() -> i32 { return true; }"
      `shouldBe` rejectedWith (TypeMismatch i32 bool (spanAt 1 24))

  test "a body without a result value returns unit" $
    typeCheckOutcome "fn f() -> i32 { }"
      `shouldBe` rejectedWith (TypeMismatch i32 unit (spanAt 1 15))

  test "returns in both branches make the generated unit return unreachable" $
    typeCheckOutcome "fn f(c: bool) -> i32 { if c { return 1; } else { return 2; }; }" `shouldBe` accepted

  test "an early return and a final return type-check" $
    typeCheckOutcome "fn f(c: bool) -> i32 { if c { return 1; } return 2; }" `shouldBe` accepted

  test "unreachable code is still type-checked" $
    typeCheckOutcome "fn f(y: i32) -> i32 { return 1; let x: bool = y; }"
      `shouldBe` rejectedWith (TypeMismatch bool i32 (spanAt 1 47))

  test "a block-like statement without a semicolon must be unit" $
    typeCheckOutcome "fn f(c: bool) -> i32 { if c { 1 } else { 2 } 3 }"
      `shouldBe` rejectedWith (TypeMismatch unit i32 (spanAt 1 24))

  test "a while loop does not diverge even when its body returns" $
    typeCheckOutcome "fn f() -> i32 { while true { return 1; } }"
      `shouldBe` rejectedWith (TypeMismatch i32 unit (spanAt 1 17))

-- Bindings and patterns (plan §5.6)
patternTests : List ETest
patternTests = Test.do
  test "unit and wildcard patterns" $
    typeCheckOutcome "fn f() { let () = (); let _ = 5; }" `shouldBe` accepted

  test "an array pattern splits an array" $
    typeCheckOutcome "fn f() -> bit { let [b0, b1, b2]: [bit; 3] = [0, 1, 0]; b1 }" `shouldBe` accepted

  test "an array pattern must have the array's length" $
    typeCheckOutcome "fn f() { let [x, y] = [1, 2, 3]; }"
      `shouldBe` rejectedWith (WrongPatternArity 3 2 (spanAt 1 14))

  test "an annotated binding checks its initializer" $
    typeCheckOutcome "fn f() { let x: bool = 5; }"
      `shouldBe` rejectedWith (TypeMismatch bool i32 (spanAt 1 24))

  test "a let naming a unit constant is an irrefutable pattern" $
    typeCheckOutcome "const UNIT: () = (); fn f() { let UNIT = (); }" `shouldBe` accepted

  test "a constant-name pattern does not introduce a local" $
    typeCheckOutcome "const UNIT: () = (); fn f() -> () { let UNIT = (); UNIT }" `shouldBe` accepted

  test "a let naming a non-unit constant is a refutable pattern" $
    typeCheckOutcome "const ZERO: i32 = 0; fn f() { let ZERO = 0; }"
      `shouldBe` rejectedWith (RefutableBindingPattern (spanAt 1 35))

  test "a constant name inside a tuple pattern is refutable" $
    typeCheckOutcome "const ONE: i32 = 1; fn f() { let (a, ONE) = (2, 1); }"
      `shouldBe` rejectedWith (RefutableBindingPattern (spanAt 1 38))

  test "a unit pattern must match a unit value" $
    typeCheckOutcome "fn f() { let () = 5; }"
      `shouldBe` rejectedWith (TypeMismatch i32 unit (spanAt 1 14))

  test "nested tuple and array patterns split their components" $
    typeCheckOutcome "fn f() -> i32 { let (a, [b, c]) = (1, [2, 3]); a + b + c }" `shouldBe` accepted

-- Constant initializers (plan §3.5)
constantInitializerTests : List ETest
constantInitializerTests = Test.do
  test "a constant initializer is checked against its type" $
    typeCheckOutcome "const FIVE: i32 = true;"
      `shouldBe` rejectedWith (TypeMismatch i32 bool (spanAt 1 19))

  test "a constant initializer's literal must fit its type" $
    typeCheckOutcome "const SMALL: u8 = 300;"
      `shouldBe` rejectedWith (IntegerLiteralOutOfRange 300 u8 (spanAt 1 19))

  test "a constant array initializer must have the declared length" $
    typeCheckOutcome "const A: [i32; 3] = [1, 2];"
      `shouldBe` rejectedWith (TypeMismatch (array i32 3) (array i32 2) (spanAt 1 21))

-- Allocation and measurement (plan §4.2, spec §10, §43)
qubitAllocationTests : List ETest
qubitAllocationTests = Test.do
  test "qalloc returns a qubit and qalloc(n) an array of qubits" $
    typeCheckOutcome "fn f() { let q: qbit = qalloc(); let qs: [qbit; 3] = qalloc(3); let r = qalloc(); let rs = qalloc(2); discard(q); discard(qs); discard(r); discard(rs); }"
      `shouldBe` accepted

  test "a qalloc count must equal the annotated length" $
    typeCheckOutcome "fn f() { let qs: [qbit; 2] = qalloc(3); discard(qs); }"
      `shouldBe` rejectedWith (TypeMismatch (array linearQbit 2) (array linearQbit 3) (spanAt 1 30))

  test "a constant may be a qalloc count" $
    typeCheckOutcome "const N: u32 = 2; fn f() { let qs: [qbit; 2] = qalloc(N); discard(qs); }"
      `shouldBe` accepted

  test "a qalloc count must be unsigned" $
    typeCheckOutcome "const N: i64 = 2; fn f() { let qs = qalloc(N); discard(qs); }"
      `shouldBe` rejectedWith (InvalidArrayLength i64 (spanAt 1 44))

  test "measr consumes or borrows a qubit and returns a bit" $
    typeCheckOutcome "fn f() -> (bit, bit) { let q = qalloc(); let r = qalloc(); let b: bit = measr(&q); let c: bit = measr(q); let d = measr(r); (b, c) }"
      `shouldBe` accepted

  test "measr of several qubits returns a tuple of bits" $
    typeCheckOutcome "fn f() -> (bit, bit, bit) { let q1 = qalloc(); let q2 = qalloc(); let q3 = qalloc(); measr(q1, q2, q3) }"
      `shouldBe` accepted

  test "measr of a qubit array returns an array of bits" $
    typeCheckOutcome "fn f() -> [bit; 3] { let qs: [qbit; 3] = qalloc(3); let bs: [bit; 3] = measr(&qs); measr(qs) }"
      `shouldBe` accepted

  test "an array pattern can split measured bits" $
    typeCheckOutcome "fn f() -> bit { let qs = qalloc(3); let [b0, b1, b2]: [bit; 3] = measr(qs); b0 }"
      `shouldBe` accepted

  test "a measurement is a bit, not a bool" $
    typeCheckOutcome "fn f() -> bool { let q = qalloc(); measr(q) }"
      `shouldBe` rejectedWith (TypeMismatch bool bit (spanAt 1 36))

  test "measr's qubit arguments are all owned or all borrowed" $
    typeCheckOutcome "fn f(a: qbit, b: &qbit) { let (x, y) = measr(a, b); }"
      `shouldBe` rejectedWith (TypeMismatch linearQbit qbitRef (spanAt 1 49))

-- Qubit multiplicities and qualifiers (plan §5.5, spec §12, §41, §42)
multiplicityTests : List ETest
multiplicityTests = Test.do
  test "let and type qualifiers give qubits their multiplicity" $
    typeCheckOutcome "fn f() { let linear a: qbit = qalloc(); let b: linear qbit = qalloc(); let affine c: qbit = qalloc(); let d: affine qbit = qalloc(); let e: [affine qbit; 2] = qalloc(2); let p: (affine qbit, affine qbit) = (qalloc(), qalloc()); discard(a); discard(b); }"
      `shouldBe` accepted

  test "an affine let fixes an inferred qubit's multiplicity" $
    typeCheckOutcome "fn f() { let affine q = qalloc(); }" `shouldBe` accepted

  test "a gate preserves its argument's multiplicity" $
    typeCheckOutcome "fn f() { let affine q: qbit = qalloc(); let affine r = H(q); }" `shouldBe` accepted

  test "an affine let cannot hold a linear qubit" $
    typeCheckOutcome "fn f() { let q: qbit = qalloc(); let affine r = H(q); discard(r); }"
      `shouldBe` rejectedWith (MultiplicityMismatch QuantumMultiplicityAffine QuantumMultiplicityLinear (spanAt 1 38))

  test "weaken makes qubits affine" $
    typeCheckOutcome "fn f() { let linear q: qbit = qalloc(); let affine q = weaken(q); let linear qs: [qbit; 3] = qalloc(3); let affine qs = weaken(qs); }"
      `shouldBe` accepted

  test "weaken's result is affine without a qualifier" $
    typeCheckOutcome "fn f() { let q = qalloc(); let r = weaken(q); }" `shouldBe` accepted

  test "weaken's result is not linear" $
    typeCheckOutcome "fn f() { let q = qalloc(); let r: qbit = weaken(q); discard(r); }"
      `shouldBe` rejectedWith (TypeMismatch linearQbit affineQbit (spanAt 1 42))

  test "weaken of several qubits returns affine qubits" $
    typeCheckOutcome "fn f() { let q1 = qalloc(); let q2 = qalloc(); let q3 = qalloc(); let affine (a, b, c): (qbit, qbit, qbit) = weaken(q1, q2, q3); }"
      `shouldBe` accepted

  test "scratch qualifiers apply to qubit bindings" $
    typeCheckOutcome "fn f() { let scratch q: qbit = qalloc(); let scratch qs: [qbit; 2] = qalloc(2); let scratch affine r: qbit = qalloc(); }"
      `shouldBe` accepted

  test "a scratch qualifier needs a qubit" $
    typeCheckOutcome "fn f() { let scratch n: i32 = 5; }"
      `shouldBe` rejectedWith (InvalidQuantumQualifier "scratch" i32 (spanAt 1 14))

  test "an affine qualifier needs a qubit" $
    typeCheckOutcome "fn f() { let affine n = 5; }"
      `shouldBe` rejectedWith (InvalidQuantumQualifier "affine" i32 (spanAt 1 14))

  test "a linear qualifier needs a qubit" $
    typeCheckOutcome "fn f() { let linear x: i32 = 1; }"
      `shouldBe` rejectedWith (InvalidQuantumQualifier "linear" i32 (spanAt 1 14))

  test ":= needs a qubit-valued initializer" $
    typeCheckOutcome "fn f() { let x: i32 := 5; }"
      `shouldBe` rejectedWith (InvalidQuantumQualifier ":=" i32 (spanAt 1 21))

  test ":= accepts an uncompsafe qubit initializer" $
    typeCheckOutcome "uncompsafe fn flip(q: qbit) -> qbit { X(q) } fn f() { let q: qbit := flip(qalloc()); }"
      `shouldBe` accepted

  test "an affine let over a tuple qualifies only its qubit positions" $
    typeCheckOutcome "fn f() -> i32 { let affine (q, n) = (qalloc(), 1); n }" `shouldBe` accepted

  test "weaken takes owned qubits only" $
    typeCheckOutcome "fn f(q: &qbit) { let r = weaken(q); }"
      `shouldBe` rejectedWith (TypeMismatch linearQbit qbitRef (spanAt 1 33))

  test "discard takes owned qubits only" $
    typeCheckOutcome "fn f(q: &qbit) { discard(q); }"
      `shouldBe` rejectedWith (TypeMismatch linearQbit qbitRef (spanAt 1 26))

-- Gates (plan §4.2, §4.3, spec §13, §14)
gateTests : List ETest
gateTests = Test.do
  test "an owned gate call returns its qubit" $
    typeCheckOutcome "fn f(q: qbit) -> qbit { let q: qbit = H(q); let linear q: qbit = H(q); let q = H(q); q }"
      `shouldBe` accepted

  test "a borrowed gate call returns unit" $
    typeCheckOutcome "fn f(q: &qbit) { let u: () = H(q); }" `shouldBe` accepted

  test "every single-qubit gate has owned and borrowed forms" $
    typeCheckOutcome "fn f(q: qbit) -> qbit { let q = I(q); let q = X(q); let q = Y(q); let q = Z(q); let q = H(q); let q = S(q); let q = SDG(q); let q = T(q); let q = TDG(q); let q = SX(q); let q = SXDG(q); I(&q); X(&q); Y(&q); Z(&q); H(&q); S(&q); SDG(&q); T(&q); TDG(&q); SX(&q); SXDG(&q); q }"
      `shouldBe` accepted

  test "parametric single-qubit gates take their angles before the qubit" $
    typeCheckOutcome "fn f(q: qbit) -> qbit { let q = RX(1.0, q); let q = RY(1.0, q); let q = RZ(1.0, q); let q = U1(1.0, q); let q = U2(1.0, 2.0, q); let q = U3(1.0, 2.0, 3.0, q); let q = GPI(1.0, q); let q = GPI2(1.0, q); U3(1.0, 2.0, 3.0, &q); q }"
      `shouldBe` accepted

  test "two-qubit gates return both qubits" $
    typeCheckOutcome "fn f(q0: qbit, q1: qbit) -> (qbit, qbit) { let (q0, q1) = CNOT(q0, q1); let (q0, q1) = CX(q0, q1); let (q0, q1) = CY(q0, q1); let (q0, q1) = CZ(q0, q1); let (q0, q1) = CS(q0, q1); let (q0, q1) = CSDG(q0, q1); let (q0, q1) = CT(q0, q1); let (q0, q1) = CTDG(q0, q1); let (q0, q1) = CSX(q0, q1); let (q0, q1) = CSXDG(q0, q1); let (q0, q1) = SWAP(q0, q1); CX(&q0, &q1); (q0, q1) }"
      `shouldBe` accepted

  test "parametric two-qubit gates take their angles first" $
    typeCheckOutcome "fn f(q0: qbit, q1: qbit) -> (qbit, qbit) { let (q0, q1) = CRX(1.0, q0, q1); let (q0, q1) = CRY(1.0, q0, q1); let (q0, q1) = CRZ(1.0, q0, q1); let (q0, q1) = CU1(1.0, q0, q1); let (q0, q1) = CU2(1.0, 2.0, q0, q1); let (q0, q1) = CU3(1.0, 2.0, 3.0, q0, q1); let (q0, q1) = RXX(1.0, q0, q1); let (q0, q1) = RYY(1.0, q0, q1); let (q0, q1) = RZZ(1.0, q0, q1); let (q0, q1) = MS(1.0, 2.0, q0, q1); let (q0, q1) = ZZ(1.0, q0, q1); (q0, q1) }"
      `shouldBe` accepted

  test "three-qubit gates return all three qubits" $
    typeCheckOutcome "fn f(q0: qbit, q1: qbit, q2: qbit) -> (qbit, qbit, qbit) { let (q0, q1, q2) = CCX(q0, q1, q2); let (q0, q1, q2) = CSWAP(q0, q1, q2); CCX(&q0, &q1, &q2); (q0, q1, q2) }"
      `shouldBe` accepted

  test "a gate takes its declared number of qubits" $
    typeCheckOutcome "fn f(q0: qbit, q1: qbit) -> qbit { H(q0, q1) }"
      `shouldBe` rejectedWith (WrongArgumentCount 1 2 (spanAt 1 36))

  test "a gate's qubit arguments are all owned or all borrowed" $
    typeCheckOutcome "fn f(q0: &qbit, q1: qbit) -> qbit { CX(q0, q1); q1 }"
      `shouldBe` rejectedWith (TypeMismatch qbitRef linearQbit (spanAt 1 44))

  test "a qubit reference selects the borrowed form" $
    typeCheckOutcome "fn apply_gate(q: &qbit) { H(q); }" `shouldBe` accepted

  test "a gate does not accept a classical argument" $
    typeCheckOutcome "fn f(x: &i32) { H(x); }"
      `shouldBe` rejectedWith (TypeMismatch qbitRef (ref i32) (spanAt 1 19))

  test "a gate angle may be a float, an angle or a param" $
    typeCheckOutcome "fn f(q: &qbit, a32: angle32, a64: angle64, x: f32, y: f64) { RX(a32, q); RX(a64, q); RX(x, q); RX(y, q); RX(turns(0.25), q); let theta = Param(\"theta\"); U1(theta, q); }"
      `shouldBe` accepted

  test "a gate angle cannot be a boolean" $
    typeCheckOutcome "fn f(q: &qbit) { RX(true, q); }"
      `shouldBe` rejectedWith (TypeMismatch angle64 bool (spanAt 1 21))

  test "an owned gate on an affine qubit returns an affine qubit" $
    typeCheckOutcome "fn f(q: affine qbit) -> affine qbit { H(q) }" `shouldBe` accepted

  test "an owned gate on an affine qubit does not return a linear qubit" $
    typeCheckOutcome "fn f(q: affine qbit) -> qbit { H(q) }"
      `shouldBe` rejectedWith (TypeMismatch linearQbit affineQbit (spanAt 1 32))

  test "a two-qubit gate returns each argument's multiplicity" $
    typeCheckOutcome "fn f(a: affine qbit, b: qbit) -> (affine qbit, qbit) { CX(a, b) }" `shouldBe` accepted

  test "a gate angle cannot be an integer literal" $
    typeCheckOutcome "fn f(q: &qbit) { RX(1, q); }"
      `shouldBe` rejectedWith (TypeMismatch angle64 i32 (spanAt 1 21))

  test "parametric single-qubit gates have borrowed forms" $
    typeCheckOutcome "fn f(q: &qbit) { RX(1.0, q); RY(1.0, q); RZ(1.0, q); U1(1.0, q); U2(1.0, 2.0, q); U3(1.0, 2.0, 3.0, q); GPI(1.0, q); GPI2(1.0, q); }"
      `shouldBe` accepted

  test "two-qubit gates have borrowed forms" $
    typeCheckOutcome "fn f(a: &qbit, b: &qbit) { CNOT(a, b); CX(a, b); CY(a, b); CZ(a, b); CS(a, b); CSDG(a, b); CT(a, b); CTDG(a, b); CSX(a, b); CSXDG(a, b); SWAP(a, b); }"
      `shouldBe` accepted

  test "parametric two-qubit gates have borrowed forms" $
    typeCheckOutcome "fn f(a: &qbit, b: &qbit) { CRX(1.0, a, b); CRY(1.0, a, b); CRZ(1.0, a, b); CU1(1.0, a, b); CU2(1.0, 2.0, a, b); CU3(1.0, 2.0, 3.0, a, b); RXX(1.0, a, b); RYY(1.0, a, b); RZZ(1.0, a, b); MS(1.0, 2.0, a, b); ZZ(1.0, a, b); }"
      `shouldBe` accepted

-- Builtins (plan §4.2, spec §38 to §44)
builtinTests : List ETest
builtinTests = Test.do
  test "reset consumes and returns or borrows its qubits" $
    typeCheckOutcome "fn f() { let q: qbit = qalloc(); let q = reset(q); reset(&q); let qs: [qbit; 3] = qalloc(3); let qs = reset(qs); reset(&qs); let q1 = qalloc(); let q2 = qalloc(); let (q1, q2) = reset(q1, q2); discard(q); discard(qs); discard(q1, q2); }"
      `shouldBe` accepted

  test "discard accepts one qubit, several qubits or an array" $
    typeCheckOutcome "fn f() { let q = qalloc(); discard(q); let q1 = qalloc(); let q2 = qalloc(); discard(q1, q2); let qs = qalloc(3); discard(qs); }"
      `shouldBe` accepted

  test "discard returns unit" $
    typeCheckOutcome "fn f() -> i32 { let q = qalloc(); discard(q) }"
      `shouldBe` rejectedWith (TypeMismatch i32 unit (spanAt 1 35))

  test "uncompute consumes and returns or borrows its qubits" $
    typeCheckOutcome "fn f() { let a = X(qalloc()); uncompute(&a); discard(a); let b = X(qalloc()); let b = uncompute(b); discard(b); }"
      `shouldBe` accepted

  test "barrier accepts no qubits, owned qubits or borrowed qubits" $
    typeCheckOutcome "fn f() { barrier(); let q0 = qalloc(); let q1 = qalloc(); let (q0, q1) = barrier(q0, q1); barrier(&q0, &q1); let qs = qalloc(2); let qs = barrier(qs); barrier(&qs); discard(q0, q1); discard(qs); }"
      `shouldBe` accepted

  test "borrowed builtins accept a qubit slice" $
    typeCheckOutcome "fn f(qs: &[qbit]) { reset(qs); barrier(qs); }" `shouldBe` accepted

  test "measuring a qubit slice has no fixed-size result" $
    typeCheckOutcome "fn f(qs: &[qbit]) { let bs = measr(qs); }"
      `shouldBe` rejectedWith (UnsizedValue (slice bit) (spanAt 1 30))

  test "len returns u32 for arrays and slices" $
    typeCheckOutcome "fn f(xs: &[i32]) -> u32 { let a = [1, 2, 3]; let n: u32 = len(a); len(xs) + n }"
      `shouldBe` accepted

  test "len does not return i32" $
    typeCheckOutcome "fn f() -> i32 { let a = [1, 2]; len(a) }"
      `shouldBe` rejectedWith (TypeMismatch i32 u32 (spanAt 1 33))

  test "len accepts mutable slices and array references" $
    typeCheckOutcome "fn f(xs: &mut [i32], a: &[i32; 3]) -> u32 { len(xs) + len(a) }" `shouldBe` accepted

  test "len takes exactly one argument" $
    typeCheckOutcome "fn f() -> u32 { let a = [1, 2]; len(a, a) }"
      `shouldBe` rejectedWith (WrongArgumentCount 1 2 (spanAt 1 33))

  test "reset preserves an affine argument's multiplicity" $
    typeCheckOutcome "fn f(q: affine qbit) -> affine qbit { reset(q) }" `shouldBe` accepted

-- ctrl (plan §5.6 Control forms, spec §15)
controlTests : List ETest
controlTests = Test.do
  test "owned controls are returned before the target's results" $
    typeCheckOutcome "fn f(q0: qbit, q1: qbit, q2: qbit) -> (qbit, qbit, qbit) { let (q0, q1, q2): (qbit, qbit, qbit) = ctrl(q0, q1).apply(H)(q2); (q0, q1, q2) }"
      `shouldBe` accepted

  test "borrowed controls and targets give a unit result" $
    typeCheckOutcome "fn f(q0: &qbit, q1: &qbit, q2: &qbit) { let u: () = ctrl(q0, q1).apply(H)(q2); }"
      `shouldBe` accepted

  test "a control selector keeps the result shape" $
    typeCheckOutcome "fn f(q0: qbit, q1: qbit, q2: qbit) -> (qbit, qbit, qbit) { let (q0, q1, q2) = ctrl(q0, q1).on(bs\"10\").apply(H)(q2); (q0, q1, q2) }"
      `shouldBe` accepted

  test "a control block over borrowed controls has unit type" $
    typeCheckOutcome "fn f(q0: &qbit, q1: &qbit, q2: &qbit) { ctrl(q0, q1) { H(q2); } let u: () = ctrl(q0, q1).on(bs\"10\") { H(q2); }; }"
      `shouldBe` accepted

  test "a control block requires borrowed controls" $
    typeCheckOutcome "fn f(q0: qbit, q2: &qbit) -> qbit { ctrl(q0) { H(q2); } q0 }"
      `shouldBe` rejectedWith (TypeMismatch qbitRef linearQbit (spanAt 1 42))

  test "controls and targets use one form" $
    typeCheckOutcome "fn f(q0: &qbit, q1: qbit) -> qbit { ctrl(q0).apply(X)(q1) }"
      `shouldBe` rejectedWith (TypeMismatch qbitRef linearQbit (spanAt 1 55))

  test "an owned controlled gate returns the controls and the target" $
    typeCheckOutcome "fn f(c: qbit, t: qbit) { let (c, t, x) = ctrl(c).apply(X)(t); }"
      `shouldBe` rejectedWith (WrongPatternArity 2 3 (spanAt 1 30))

  test "a stored controlled callable with owned controls is an implementation limit" $
    typeCheckOutcome "fn f(q0: qbit, q1: qbit) -> (qbit, qbit) { let g = ctrl(q0).apply(X); g(q1) }"
      `shouldBe` rejectedWith (UnsupportedFeature "stored controlled callable" (spanAt 1 52))

  test "owned controls are prepended to a multi-qubit target's results" $
    typeCheckOutcome "fn f(c: qbit, a: qbit, b: qbit) -> (qbit, qbit, qbit) { let (c, a, b) = ctrl(c).apply(CX)(a, b); (c, a, b) }"
      `shouldBe` accepted

  test "a controlled rotation keeps its angle parameter" $
    typeCheckOutcome "fn f(c: qbit, q: qbit) -> (qbit, qbit) { ctrl(c).apply(RX)(0.5, q) }"
      `shouldBe` accepted

  test "a controlled adjoint gate type-checks" $
    typeCheckOutcome "fn f(c: &qbit, q: &qbit) { ctrl(c).apply(adjoint(S))(q); }" `shouldBe` accepted

  test "a gate alias keeps its control capability" $
    typeCheckOutcome "fn f(c: &qbit, q: &qbit) { let h = H; ctrl(c).apply(h)(q); }" `shouldBe` accepted

-- adjoint and gate aliases (plan §4.2, §5.6 Adjoint, spec §16)
adjointTests : List ETest
adjointTests = Test.do
  test "the adjoint of a gate keeps the gate's owned and borrowed forms" $
    typeCheckOutcome "fn f(q1: qbit, q2: qbit) -> (qbit, qbit) { let q1 = adjoint(H)(q1); adjoint(H)(&q1); adjoint(CT)(&q1, &q2); (q1, q2) }"
      `shouldBe` accepted

  test "the adjoint of a rotation still takes its angle" $
    typeCheckOutcome "fn f(q: &qbit) { adjoint(RX)(1.0, q); }" `shouldBe` accepted

  test "the adjoint of a rotation needs its angle" $
    typeCheckOutcome "fn f(q: &qbit) { adjoint(RX)(q); }"
      `shouldBe` rejectedWith (WrongArgumentCount 2 1 (spanAt 1 18))

  test "an adjoint alias keeps the gate's borrowed form" $
    typeCheckOutcome "fn f(q: &qbit) { let h = adjoint(H); h(q); }" `shouldBe` accepted

  test "an adjoint block has unit type" $
    typeCheckOutcome "fn f(q1: &qbit, q2: &qbit) { let u: () = adjoint { H(q1); CT(q1, q2) }; }"
      `shouldBe` accepted

  test "a gate alias keeps both forms" $
    typeCheckOutcome "fn f(q: qbit) -> qbit { let g = H; g(&q); g(q) }" `shouldBe` accepted

  test "a mutable gate alias can be reassigned" $
    typeCheckOutcome "fn f(q: &qbit) { let mut h = H; h = X; h(q); }" `shouldBe` accepted

  test "the adjoint of an owned two-qubit gate returns both qubits" $
    typeCheckOutcome "fn f(a: qbit, b: qbit) -> (qbit, qbit) { adjoint(CX)(a, b) }" `shouldBe` accepted

  test "the adjoint of a gate alias is permitted" $
    typeCheckOutcome "fn f(q: &qbit) { let s = S; adjoint(s)(q); }" `shouldBe` accepted

  test "the adjoint of a gate's adjoint is permitted" $
    typeCheckOutcome "fn f(q: &qbit) { adjoint(adjoint(T))(q); }" `shouldBe` accepted

-- Context propagation and delayed writeback (plan §4.3, §5.2–§5.4; spec §6, §7, §48)
contextualInferenceTests : List ETest
contextualInferenceTests = Test.do
  test "a return context fixes an unsuffixed integer before range checking" $
    typeCheckOutcome "fn f() -> u8 { 255 }"
      `shouldBe` accepted

  test "a call argument is checked before its integer type is defaulted" $
    typeCheckOutcome "fn keep(x: u8) -> u8 { x } fn f() -> u8 { keep(255) }"
      `shouldBe` accepted

  test "an assignment propagates the target type to its literal" $
    typeCheckOutcome "fn f() -> u8 { let mut x: u8 = 0; x = 255; x }"
      `shouldBe` accepted

  test "nested tuple and array expectations reach each literal" $
    typeCheckOutcome "fn f() -> ([u8; 2], (bool, i16)) { ([1, 255], (true, -32768)) }"
      `shouldBe` accepted

  test "a later array annotation range-checks every previously inferred element" $
    typeCheckOutcome "fn f() { let xs = [1, 256]; let ys: [u8; 2] = xs; }"
      `shouldBe` rejectedWith (IntegerLiteralOutOfRange 256 u8 (spanAt 1 23))

  test "a gate angle remains open until a later f32 constraint" $
    typeCheckOutcome "fn f(q: &qbit) { let theta = 0.5; RX(theta, q); let x: f32 = theta; }"
      `shouldBe` accepted

  test "ordinary angle parameters do not inherit a gate float coercion" $
    typeCheckOutcome "fn rotate(theta: angle64) {} fn f(x: f64) { rotate(x); }"
      `shouldBe` rejectedWith (TypeMismatch angle64 f64 (spanAt 1 52))

  test "ordinary float parameters do not implicitly convert integers" $
    typeCheckOutcome "fn take(x: f64) {} fn f(x: i32) { take(x); }"
      `shouldBe` rejectedWith (TypeMismatch f64 i32 (spanAt 1 40))

  test "an unreachable tail does not change a diverging block type" $
    typeCheckOutcome "fn f() -> i32 { { return 1; true } }"
      `shouldBe` accepted

  test "nested loops keep their break-value types separate" $
    typeCheckOutcome "fn f() -> i32 { loop { let done: bool = loop { break true; }; if done { break 7; } } }"
      `shouldBe` accepted


-- Joined callable types and schemes (plan §4.2, §5.3; spec §53, §61)
functionJoinTests : List ETest
functionJoinTests = Test.do
  test "a branch join retains the weaker function effect" $
    typeCheckOutcome "classical fn pure_value(x: i32) -> i32 { x } fn general_value(x: i32) -> i32 { x } fn f(flag: bool) -> i32 { let g = if flag { pure_value } else { general_value }; g(1) }"
      `shouldBe` accepted

  test "a joined function cannot regain the stronger effect of one branch" $
    typeCheckOutcome "classical fn pure_value(x: i32) -> i32 { x } fn general_value(x: i32) -> i32 { x } fn f(flag: bool) { let g = if flag { pure_value } else { general_value }; let h: classical fn(x: i32) -> i32 = g; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectClassical [i32] i32) (fnType EffectGeneral [i32] i32) (spanAt 1 195))

  test "an inferred array joins function effects across its elements" $
    typeCheckOutcome "classical fn pure_value(x: i32) -> i32 { x } fn general_value(x: i32) -> i32 { x } fn f() -> i32 { let fs = [pure_value, general_value]; fs[0](1) }"
      `shouldBe` accepted

  test "a tuple branch join recursively joins its callable component" $
    typeCheckOutcome "classical fn pure_value(x: i32) -> i32 { x } fn general_value(x: i32) -> i32 { x } fn f(flag: bool) -> i32 { let pair = if flag { (pure_value, 1) } else { (general_value, 2) }; pair.0(pair.1) }"
      `shouldBe` accepted

  test "loop breaks join function effects before the callable is used" $
    typeCheckOutcome "classical fn pure_value(x: i32) -> i32 { x } fn general_value(x: i32) -> i32 { x } fn f(flag: bool) -> i32 { let g = loop { if flag { break pure_value; } break general_value; }; g(1) }"
      `shouldBe` accepted

  test "a callable join intersects capabilities instead of retaining adjoint" $
    typeCheckOutcome "unitary fn plain(q: qbit) -> qbit { H(q) } fn f(flag: bool, q: qbit) -> qbit { let g = if flag { H } else { plain }; adjoint(g)(q) }"
      `shouldBe` rejectedWith (MissingCapability "adjoint" (spanAt 1 126))

  test "joining two gates preserves a compatible borrowed signature" $
    typeCheckOutcome "fn f(flag: bool, q: &qbit) { let gate = if flag { H } else { X }; gate(q); }"
      `shouldBe` accepted

  test "a gate array preserves a compatible borrowed signature" $
    typeCheckOutcome "fn f(q: &qbit) { let gates = [H, X]; gates[0](q); gates[1](q); }"
      `shouldBe` accepted


-- Directional coercions at checked boundaries (plan §5.3, §5.6; spec §9, §51, §61)
coercionBoundaryTests : List ETest
coercionBoundaryTests = Test.do
  test "a returned array reference coerces to a slice reference" $
    typeCheckOutcome "fn f(xs: &[i32; 3]) -> &[i32] { xs }"
      `shouldBe` accepted

  test "a mutable array reference can reborrow as a shared slice argument" $
    typeCheckOutcome "fn first(xs: &[i32]) -> i32 { xs[0] } fn f() -> i32 { let mut xs = [1, 2]; first(&mut xs) }"
      `shouldBe` accepted

  test "a mutable array reference coerces to a mutable slice argument" $
    typeCheckOutcome "fn replace(xs: &mut [i32]) { xs[0] = 7; } fn f() -> i32 { let mut xs = [1, 2]; replace(&mut xs); xs[0] }"
      `shouldBe` accepted

  test "a gate specializes to a borrowed function-typed parameter" $
    typeCheckOutcome "fn apply_gate(g: unitary fn(q: &qbit), q: &qbit) { g(q); } fn f(q: &qbit) { apply_gate(H, q); }"
      `shouldBe` accepted

  test "an ordinary call cannot widen a concrete f32 to f64" $
    typeCheckOutcome "fn take(x: f64) {} fn f(x: f32) { take(x); }"
      `shouldBe` rejectedWith (TypeMismatch f64 f32 (spanAt 1 40))

  test "an expected tuple type coerces an array reference component to a slice" $
    typeCheckOutcome "fn f(a: &[i32; 2]) -> i32 { let t: (&[i32], i32) = (a, 1); t.1 }" `shouldBe` accepted


-- Runtime prelude overloads (plan §4.2; spec §6, §14, §65)
mathPreludeTests : List ETest
mathPreludeTests = Test.do
  test "abs, min and max preserve the selected integer type" $
    typeCheckOutcome "fn f(x: i16, y: i16, a: u8, b: u8) { let magnitude: i16 = abs(x); let lower: i16 = min(x, y); let upper: u8 = max(a, b); }"
      `shouldBe` accepted

  test "numeric math overloads preserve f32 instead of defaulting to f64" $
    typeCheckOutcome "fn f(x: f32, y: f32) -> f32 { max(abs(x), min(x, y)) }"
      `shouldBe` accepted

  test "transcendental math functions use f64 signatures" $
    typeCheckOutcome "fn f(x: f64) { let a: f64 = sin(x); let b: f64 = cos(x); let c: f64 = tan(x); let d: f64 = asin(x); let e: f64 = acos(x); let f: f64 = atan(x); let g: f64 = exp(x); let h: f64 = ln(x); let i: f64 = log2(x); let j: f64 = log10(x); let k: f64 = sqrt(x); }"
      `shouldBe` accepted

  test "a transcendental call does not widen an f32 argument" $
    typeCheckOutcome "fn f(x: f32) { let y = sin(x); }"
      `shouldBe` rejectedWith (TypeMismatch f64 f32 (spanAt 1 28))

  test "min checks both arguments against the same overload" $
    typeCheckOutcome "fn f(x: i32, y: i64) { let z = min(x, y); }"
      `shouldBe` rejectedWith (TypeMismatch i32 i64 (spanAt 1 39))

  test "a math call rejects missing arguments before selecting an overload" $
    typeCheckOutcome "fn f() { let x = max(1); }"
      `shouldBe` rejectedWith (WrongArgumentCount 2 1 (spanAt 1 18))

  test "turns produces an angle64 value" $
    typeCheckOutcome "fn f() -> angle64 { turns(0.25) }"
      `shouldBe` accepted

  test "turns does not return an ordinary float" $
    typeCheckOutcome "fn f() -> f64 { turns(0.25) }"
      `shouldBe` rejectedWith (TypeMismatch f64 angle64 (spanAt 1 17))

-- Function values and the effect order (plan §5.3, §7.3): a provided effect
-- satisfies a required one when classical ≤ uncompsafe ≤ unitary ≤
-- {isometry, coisometry} ≤ general, and a join takes the least common effect.
-- Only declared functions make width claims (§7.1), so written i32 -> i32
-- function types can carry every effect.
effectOrderTests : List ETest
effectOrderTests = Test.do
  test "a classical function value satisfies classical, uncompsafe, unitary, isometry, coisometry and general function types" $
    typeCheckOutcome "fn f(h: classical fn(x: i32) -> i32) { let v0: classical fn(x: i32) -> i32 = h; let v1: uncompsafe fn(x: i32) -> i32 = h; let v2: unitary fn(x: i32) -> i32 = h; let v3: isometry fn(x: i32) -> i32 = h; let v4: coisometry fn(x: i32) -> i32 = h; let v5: general fn(x: i32) -> i32 = h; }"
      `shouldBe` accepted

  test "an uncompsafe function value satisfies uncompsafe, unitary, isometry, coisometry and general function types" $
    typeCheckOutcome "fn f(h: uncompsafe fn(x: i32) -> i32) { let v0: uncompsafe fn(x: i32) -> i32 = h; let v1: unitary fn(x: i32) -> i32 = h; let v2: isometry fn(x: i32) -> i32 = h; let v3: coisometry fn(x: i32) -> i32 = h; let v4: general fn(x: i32) -> i32 = h; }"
      `shouldBe` accepted

  test "a unitary function value satisfies unitary, isometry, coisometry and general function types" $
    typeCheckOutcome "fn f(h: unitary fn(x: i32) -> i32) { let v0: unitary fn(x: i32) -> i32 = h; let v1: isometry fn(x: i32) -> i32 = h; let v2: coisometry fn(x: i32) -> i32 = h; let v3: general fn(x: i32) -> i32 = h; }"
      `shouldBe` accepted

  test "an isometry function value satisfies isometry and general function types" $
    typeCheckOutcome "fn f(h: isometry fn(x: i32) -> i32) { let v0: isometry fn(x: i32) -> i32 = h; let v1: general fn(x: i32) -> i32 = h; }"
      `shouldBe` accepted

  test "a coisometry function value satisfies coisometry and general function types" $
    typeCheckOutcome "fn f(h: coisometry fn(x: i32) -> i32) { let v0: coisometry fn(x: i32) -> i32 = h; let v1: general fn(x: i32) -> i32 = h; }"
      `shouldBe` accepted

  test "a general function value satisfies general function types" $
    typeCheckOutcome "fn f(h: general fn(x: i32) -> i32) { let v0: general fn(x: i32) -> i32 = h; }"
      `shouldBe` accepted

  test "an uncompsafe function value does not satisfy a classical function type" $
    typeCheckOutcome "fn f(h: uncompsafe fn(x: i32) -> i32) { let g: classical fn(x: i32) -> i32 = h; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectClassical [i32] i32) (fnType EffectUncompsafe [i32] i32) (spanAt 1 78))

  test "a unitary function value does not satisfy a classical function type" $
    typeCheckOutcome "fn f(h: unitary fn(x: i32) -> i32) { let g: classical fn(x: i32) -> i32 = h; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectClassical [i32] i32) (fnType EffectUnitary [i32] i32) (spanAt 1 75))

  test "a unitary function value does not satisfy an uncompsafe function type" $
    typeCheckOutcome "fn f(h: unitary fn(x: i32) -> i32) { let g: uncompsafe fn(x: i32) -> i32 = h; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectUncompsafe [i32] i32) (fnType EffectUnitary [i32] i32) (spanAt 1 76))

  test "an isometry function value does not satisfy a classical function type" $
    typeCheckOutcome "fn f(h: isometry fn(x: i32) -> i32) { let g: classical fn(x: i32) -> i32 = h; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectClassical [i32] i32) (fnType EffectIsometry [i32] i32) (spanAt 1 76))

  test "an isometry function value does not satisfy an uncompsafe function type" $
    typeCheckOutcome "fn f(h: isometry fn(x: i32) -> i32) { let g: uncompsafe fn(x: i32) -> i32 = h; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectUncompsafe [i32] i32) (fnType EffectIsometry [i32] i32) (spanAt 1 77))

  test "an isometry function value does not satisfy a unitary function type" $
    typeCheckOutcome "fn f(h: isometry fn(x: i32) -> i32) { let g: unitary fn(x: i32) -> i32 = h; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectUnitary [i32] i32) (fnType EffectIsometry [i32] i32) (spanAt 1 74))

  test "an isometry function value does not satisfy a coisometry function type" $
    typeCheckOutcome "fn f(h: isometry fn(x: i32) -> i32) { let g: coisometry fn(x: i32) -> i32 = h; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectCoisometry [i32] i32) (fnType EffectIsometry [i32] i32) (spanAt 1 77))

  test "a coisometry function value does not satisfy a classical function type" $
    typeCheckOutcome "fn f(h: coisometry fn(x: i32) -> i32) { let g: classical fn(x: i32) -> i32 = h; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectClassical [i32] i32) (fnType EffectCoisometry [i32] i32) (spanAt 1 78))

  test "a coisometry function value does not satisfy an uncompsafe function type" $
    typeCheckOutcome "fn f(h: coisometry fn(x: i32) -> i32) { let g: uncompsafe fn(x: i32) -> i32 = h; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectUncompsafe [i32] i32) (fnType EffectCoisometry [i32] i32) (spanAt 1 79))

  test "a coisometry function value does not satisfy a unitary function type" $
    typeCheckOutcome "fn f(h: coisometry fn(x: i32) -> i32) { let g: unitary fn(x: i32) -> i32 = h; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectUnitary [i32] i32) (fnType EffectCoisometry [i32] i32) (spanAt 1 76))

  test "a coisometry function value does not satisfy an isometry function type" $
    typeCheckOutcome "fn f(h: coisometry fn(x: i32) -> i32) { let g: isometry fn(x: i32) -> i32 = h; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectIsometry [i32] i32) (fnType EffectCoisometry [i32] i32) (spanAt 1 77))

  test "a general function value does not satisfy a classical function type" $
    typeCheckOutcome "fn f(h: general fn(x: i32) -> i32) { let g: classical fn(x: i32) -> i32 = h; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectClassical [i32] i32) (fnType EffectGeneral [i32] i32) (spanAt 1 75))

  test "a general function value does not satisfy an uncompsafe function type" $
    typeCheckOutcome "fn f(h: general fn(x: i32) -> i32) { let g: uncompsafe fn(x: i32) -> i32 = h; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectUncompsafe [i32] i32) (fnType EffectGeneral [i32] i32) (spanAt 1 76))

  test "a general function value does not satisfy a unitary function type" $
    typeCheckOutcome "fn f(h: general fn(x: i32) -> i32) { let g: unitary fn(x: i32) -> i32 = h; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectUnitary [i32] i32) (fnType EffectGeneral [i32] i32) (spanAt 1 73))

  test "a general function value does not satisfy an isometry function type" $
    typeCheckOutcome "fn f(h: general fn(x: i32) -> i32) { let g: isometry fn(x: i32) -> i32 = h; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectIsometry [i32] i32) (fnType EffectGeneral [i32] i32) (spanAt 1 74))

  test "a general function value does not satisfy a coisometry function type" $
    typeCheckOutcome "fn f(h: general fn(x: i32) -> i32) { let g: coisometry fn(x: i32) -> i32 = h; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectCoisometry [i32] i32) (fnType EffectGeneral [i32] i32) (spanAt 1 76))

  test "joining isometry and coisometry function values gives general" $
    typeCheckOutcome "fn f(c: bool, a: isometry fn(x: i32) -> i32, b: coisometry fn(x: i32) -> i32) { let g = if c { a } else { b }; let h: isometry fn(x: i32) -> i32 = g; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectIsometry [i32] i32) (fnType EffectGeneral [i32] i32) (spanAt 1 148))

  test "joining classical and unitary function values gives unitary" $
    typeCheckOutcome "fn f(c: bool, a: classical fn(x: i32) -> i32, b: unitary fn(x: i32) -> i32) { let g = if c { a } else { b }; let h: unitary fn(x: i32) -> i32 = g; }"
      `shouldBe` accepted

  test "joining classical and unitary function values does not give uncompsafe" $
    typeCheckOutcome "fn f(c: bool, a: classical fn(x: i32) -> i32, b: unitary fn(x: i32) -> i32) { let g = if c { a } else { b }; let h: uncompsafe fn(x: i32) -> i32 = g; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectUncompsafe [i32] i32) (fnType EffectUnitary [i32] i32) (spanAt 1 148))

-- These two invalid forms have no specified diagnostic constructor yet:
-- recursive inference constraints (§5.3) and a reversed range used as an index
-- (§5.6). Require a returned TypeError rather than acceptance or a crash;
-- frontend fixture failures still propagate from typeCheckOutcome.
inferenceOccursCheckTests : List ETest
inferenceOccursCheckTests = Test.do
  test "an inferred array element type cannot contain itself" $
    rejected (typeCheckOutcome "fn f() { let mut x = []; x = [x; 0]; }")
      `shouldBe` True

-- Function components are invariant even where an ordinary call or return
-- permits a coercion (plan §5.3; spec §9, §51, §53).
callableComponentTests : List ETest
callableComponentTests = Test.do
  test "array-to-slice argument coercion does not change a function parameter type" $
    typeCheckOutcome "fn f(g: fn(xs: &[i32])) { let h: fn(xs: &[i32; 2]) = g; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectGeneral [ref (array i32 2)] unit) (fnType EffectGeneral [ref (slice i32)] unit) (spanAt 1 54))

  test "mutable-to-shared reborrowing does not change a function parameter type" $
    typeCheckOutcome "fn f(g: fn(x: &i32)) { let h: fn(x: &mut i32) = g; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectGeneral [refMut i32] unit) (fnType EffectGeneral [ref i32] unit) (spanAt 1 49))

  test "array-to-slice return coercion does not change a function result type" $
    typeCheckOutcome "fn f(g: fn(xs: &[i32; 2]) -> &[i32; 2]) { let h: fn(xs: &[i32; 2]) -> &[i32] = g; }"
      `shouldBe` rejectedWith (TypeMismatch (fnType EffectGeneral [ref (array i32 2)] (ref (slice i32))) (fnType EffectGeneral [ref (array i32 2)] (ref (array i32 2))) (spanAt 1 80))

  test "a branch join cannot weaken a function effect behind a reference" $
    typeCheckOutcome "fn f(c: bool, a: classical fn(x: i32) -> i32, b: fn(x: i32) -> i32) { let r = if c { &a } else { &b }; }"
      `shouldBe` rejectedWith (TypeMismatch (ref (fnType EffectClassical [i32] i32)) (ref (fnType EffectGeneral [i32] i32)) (spanAt 1 98))

-- Gate aliases preserve schemes; angle arguments specialize independently at
-- each call and at each parameter position (plan §4.2–§4.3; spec §14, §16).
aliasedAngleTests : List ETest
aliasedAngleTests = Test.do
  test "a rotation alias independently accepts f32 and f64 calls" $
    typeCheckOutcome "fn f(q: &qbit) { let rotate = RX; rotate(0.5f32, q); rotate(0.5f64, q); }"
      `shouldBe` accepted

  test "an adjoint rotation alias independently accepts f32 and f64 calls" $
    typeCheckOutcome "fn f(q: &qbit) { let rotate = adjoint(RX); rotate(0.5f32, q); rotate(0.5f64, q); }"
      `shouldBe` accepted

  test "each angle of U3 can have a different representation" $
    typeCheckOutcome "fn f(q: &qbit, a: angle32, p: param) { U3(a, 0.5f64, p, q); }"
      `shouldBe` accepted

  test "a U3 alias can change each angle representation at its next call" $
    typeCheckOutcome "fn f(q: &qbit, a: angle32, p: param) { let rotate = U3; rotate(a, 0.5f64, p, q); rotate(p, a, 0.5f32, q); }"
      `shouldBe` accepted

-- Only reachable breaks contribute to a loop's result, but all source
-- expressions must still be checked (plan §5.6).
unreachableBreakTests : List ETest
unreachableBreakTests = Test.do
  test "a break after return does not determine the loop result" $
    typeCheckOutcome "fn f() -> i32 { loop { return 1; break true; } }"
      `shouldBe` accepted

  test "a break after continue does not make a diverging loop produce a value" $
    typeCheckOutcome "fn f() -> i32 { loop { continue; break true; } }"
      `shouldBe` accepted

  test "a second unreachable break does not join with a reachable break value" $
    typeCheckOutcome "fn f() -> i32 { loop { break 1; break true; } }"
      `shouldBe` accepted

  test "an unreachable break still checks its operand's operators" $
    typeCheckOutcome "fn f() -> i32 { loop { return 1; break true + false; } }"
      `shouldBe` rejectedWith (InvalidBinaryOperands "+" bool bool (spanAt 1 40))

-- Indexing uses a range value, not only the range expression's syntax, and
-- an exclusive slice endpoint may equal the array length (plan §5.6; spec §9).
storedRangeIndexTests : List ETest
storedRangeIndexTests = Test.do
  test "indexing constrains a stored range's open integer endpoints to u32" $
    typeCheckOutcome "fn f(a: [i32; 3]) { let r = 0..2; let s: &[i32] = &a[r]; }"
      `shouldBe` accepted

  test "an open range stored in a local can slice an array" $
    typeCheckOutcome "fn f(a: [i32; 3]) { let r = 1..; let s: &[i32] = &a[r]; }"
      `shouldBe` accepted

  test "a reversed range stored in a local cannot index an array" $
    rejected (typeCheckOutcome "fn f(a: [i32; 3]) { let r = rev(0u32..2u32); let s = &a[r]; }")
      `shouldBe` True

  test "empty slices may start at the array's end" $
    typeCheckOutcome "fn f(a: [i32; 3]) { let s: &[i32] = &a[3..3]; let t: &[i32] = &a[3..]; }"
      `shouldBe` accepted

  test "an empty array can be borrowed as an empty slice" $
    typeCheckOutcome "fn f(a: [i32; 0]) { let s: &[i32] = &a[0..0]; let t: &[i32] = &a[..]; }"
      `shouldBe` accepted

-- Invalid forms the plan rejects without naming a diagnostic: a prelude name
-- with no value type used as a value (§2.4, §5.6), a for loop over a value
-- that is not iterable and rev of something that is not a range (§5.6).
unspecifiedDiagnosticTests : List ETest
unspecifiedDiagnosticTests = Test.do
  test "Param is not a value" $
    rejected (typeCheckOutcome "fn f() { let p = Param; }")
      `shouldBe` True

  test "a for loop over a value that is not iterable is rejected" $
    rejected (typeCheckOutcome "fn f() { for i in 5 { } }")
      `shouldBe` True

  test "rev requires a range operand" $
    rejected (typeCheckOutcome "fn f() { let r = rev(5); }")
      `shouldBe` True

export
runBodyCheckTests : IO ()
runBodyCheckTests =
  runTests $ concat
    [ literalTests
    , paramAndStringTests
    , excludedConstructTests
    , nameTests
    , operatorTests
    , compoundAssignmentTests
    , castTests
    , tupleTests
    , arrayTests
    , sliceTests
    , referenceTests
    , memberTests
    , callTests
    , functionValueTests
    , conditionalTests
    , loopTests
    , forLoopTests
    , rangeTests
    , blockTests
    , patternTests
    , constantInitializerTests
    , qubitAllocationTests
    , multiplicityTests
    , gateTests
    , builtinTests
    , controlTests
    , adjointTests
    , contextualInferenceTests
    , functionJoinTests
    , coercionBoundaryTests
    , mathPreludeTests
    , effectOrderTests
    , inferenceOccursCheckTests
    , callableComponentTests
    , aliasedAngleTests
    , unreachableBreakTests
    , storedRangeIndexTests
    , unspecifiedDiagnosticTests
    ]

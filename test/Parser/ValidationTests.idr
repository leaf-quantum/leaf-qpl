module Parser.ValidationTests

import Test.Simple

import Frontend.ASTPhases
import Compiler.Validation.PostParseValidation
import Frontend.Syntax.AST
import Parser.Helper

%default total

validationMessages : String -> Maybe (List String)
validationMessages source =
  case lexThenParse "test-fixture.rs" source of
    Nothing => Nothing
    Just sourceFile => Just (map interpolate (validateSourceFile sourceFile))

export
runPostParseValidationTests : IO ()
runPostParseValidationTests = runTests $ Test.do

  test "unknown attributes are rejected after parsing" $
    validationMessages "#[unknown]\nfn f() {}" `shouldBe`
      Just
        [ "test-fixture.rs:1:1: unknown attribute `unknown` " ++
          "(supported: qasm_gate, qasm_def)"
        ]

  test "mutable qbit references are rejected after parsing" $
    validationMessages "fn f(q: &mut qbit) {}" `shouldBe`
      Just
        [ "test-fixture.rs:1:9: `mut` should never be written on a qbit reference; " ++
          "qbit references are mutable by default"
        ]

  test "a multiplicity qualifier repeated in a let type annotation is rejected" $
    validationMessages "fn f() {let linear q: linear qbit = qalloc();}" `shouldBe`
      Just
        [ "test-fixture.rs:1:23: `linear` cannot be written in the type " ++
          "annotation because the `let` already has the `linear` qualifier; " ++
          "write the multiplicity qualifier in one place only"
        ]

  test "a conflicting multiplicity qualifier nested in a let type annotation is rejected" $
    validationMessages "fn f() {let linear (a, b): (affine qbit, qbit) = (qalloc(), qalloc());}" `shouldBe`
      Just
        [ "test-fixture.rs:1:29: `affine` cannot be written in the type " ++
          "annotation because the `let` already has the `linear` qualifier; " ++
          "write the multiplicity qualifier in one place only"
        ]

  test "a multiplicity qualifier written in one place only is accepted" $
    validationMessages
      "fn f() {let linear a: qbit = qalloc(); let b: affine qbit = qalloc(); let scratch c: affine qbit = qalloc();}"
      `shouldBe` Just []

  test "multiplicity qualifiers inside a function type in a let annotation are not repeats" $
    validationMessages "fn f(g: fn(q: affine qbit) -> qbit) {let linear h: fn(q: affine qbit) -> linear qbit = g;}"
      `shouldBe` Just []

  test "a multiplicity qualifier behind a reference in a let annotation is not reported as a repeat" $
    validationMessages
      "fn f(q: qbit) {let affine x: (qbit, &[linear qbit; 1]) = (qalloc(), &q);}"
      `shouldBe`
      Just
        [ "test-fixture.rs:1:39: `linear` cannot be written behind a reference; " ++
          "a reference borrows its referent without owning it"
        ]

  test "a multiplicity qualifier in a referenced slice is rejected" $
    validationMessages "fn f(qs: &[linear qbit]) {}" `shouldBe`
      Just
        [ "test-fixture.rs:1:12: `linear` cannot be written behind a reference; " ++
          "a reference borrows its referent without owning it"
        ]

  test "a multiplicity qualifier deep in a referenced tuple is rejected" $
    validationMessages "fn f(p: &(i32, [affine qbit; 2])) {}" `shouldBe`
      Just
        [ "test-fixture.rs:1:17: `affine` cannot be written behind a reference; " ++
          "a reference borrows its referent without owning it"
        ]

  test "a multiplicity qualifier behind nested references is rejected once" $
    validationMessages "fn f(v: &[&[affine qbit]]) {}" `shouldBe`
      Just
        [ "test-fixture.rs:1:13: `affine` cannot be written behind a reference; " ++
          "a reference borrows its referent without owning it"
        ]

  test "a multiplicity qualifier behind a mutable qbit reference is rejected with the mut" $
    validationMessages "fn f(qs: &mut [affine qbit]) {}" `shouldBe`
      Just
        [ "test-fixture.rs:1:10: `mut` should never be written on a qbit reference; " ++
          "qbit references are mutable by default"
        , "test-fixture.rs:1:16: `affine` cannot be written behind a reference; " ++
          "a reference borrows its referent without owning it"
        ]

  test "multiplicity qualifiers in a referenced function type are allowed" $
    validationMessages "fn f(g: &fn(q: affine qbit) -> linear qbit) {}"
      `shouldBe` Just []

  test "a multiplicity qualifier on a qbit array element repeated in a let is rejected" $
    validationMessages "fn f() {let affine qs: [linear qbit; 2] = qalloc(2);}" `shouldBe`
      Just
        [ "test-fixture.rs:1:25: `linear` cannot be written in the type " ++
          "annotation because the `let` already has the `affine` qualifier; " ++
          "write the multiplicity qualifier in one place only"
        ]

  test "a signed suffix on an array type length is rejected" $
    validationMessages "fn f(qs: [qbit; 3i8]) {}" `shouldBe`
      Just
        [ "test-fixture.rs:1:17: an array length cannot have the signed type " ++
          "suffix `i8`; write an unsigned suffix such as `u32`, or none"
        ]

  test "a signed suffix on a repeated array length is rejected" $
    validationMessages "fn f() {let xs = [0; 0x2_i128];}" `shouldBe`
      Just
        [ "test-fixture.rs:1:22: an array length cannot have the signed type " ++
          "suffix `i128`; write an unsigned suffix such as `u32`, or none"
        ]

  test "a signed suffix on a parenthesized array type length is rejected" $
    validationMessages "fn f(qs: [qbit; (3i8)]) {}" `shouldBe`
      Just
        [ "test-fixture.rs:1:18: an array length cannot have the signed type " ++
          "suffix `i8`; write an unsigned suffix such as `u32`, or none"
        ]

  test "a signed suffix on a doubly parenthesized repeated array length is rejected" $
    validationMessages "fn f() {let xs = [0; ((3i8))];}" `shouldBe`
      Just
        [ "test-fixture.rs:1:24: an array length cannot have the signed type " ++
          "suffix `i8`; write an unsigned suffix such as `u32`, or none"
        ]

  test "an array type length too large for its suffix type is rejected" $
    validationMessages "fn f(qs: [qbit; 256u8]) {}" `shouldBe`
      Just
        [ "test-fixture.rs:1:17: the array length `256u8` does not fit in " ++
          "`u8`, whose largest value is 255"
        ]

  test "a repeated array length too large for its suffix type is rejected" $
    validationMessages "fn f() {let xs = [0; 0x1_0000_u16];}" `shouldBe`
      Just
        [ "test-fixture.rs:1:22: the array length `0x1_0000_u16` does not fit " ++
          "in `u16`, whose largest value is 65535"
        ]

  test "unsigned and missing array length suffixes are accepted" $
    validationMessages
      "fn f(qs: [qbit; 3u8], rs: [qbit; 0x2_u64], ss: [qbit; 4]) {let xs = [0; 4u32];}"
      `shouldBe` Just []

  test "array lengths at the largest value of their suffix type are accepted" $
    validationMessages
      "fn f(qs: [qbit; 255u8], rs: [qbit; (0xff_u8)]) {let xs = [0; 65535u16];}"
      `shouldBe` Just []

  test "break outside a loop is rejected after parsing" $
    validationMessages "fn f() {break;}" `shouldBe`
      Just ["test-fixture.rs:1:9: `break` found outside of a loop"]

  test "continue outside a loop is rejected after parsing" $
    validationMessages "fn f() {continue;}" `shouldBe`
      Just ["test-fixture.rs:1:9: `continue` found outside of a loop"]

  test "return in a constant initializer is rejected after parsing" $
    validationMessages "const N: i64 = return 4;" `shouldBe`
      Just ["test-fixture.rs:1:16: `return` found outside of a function body"]

  test "a repeated attribute name is rejected after parsing" $
    validationMessages "#[qasm_gate]\n#[qasm_gate]\nfn f() {}" `shouldBe`
      Just
        [ "test-fixture.rs:2:1: attribute `qasm_gate` is already applied " ++
          "to this item"
        ]

  test "two distinct known attributes together are rejected after parsing" $
    validationMessages "#[qasm_gate]\n#[qasm_def]\nfn f() {}" `shouldBe`
      Just
        [ "test-fixture.rs:2:1: attribute `qasm_def` conflicts with " ++
          "another attribute already applied to this item (qasm_gate and " ++
          "qasm_def are mutually exclusive)"
        ]

  test "repeated parameter names are deferred to name resolution" $
    validationMessages "fn f(x: i32, x: i32) {}" `shouldBe`
      Just []

  test "repeated let-pattern names are deferred to name resolution" $
    validationMessages "fn f() {let (x, x) = pair;}" `shouldBe`
      Just []

  test "repeated names across nested tuple patterns require name resolution" $
    validationMessages "fn f() {let ((x, y), (z, x)) = value;}" `shouldBe`
      Just []

  test "repeated names in nested array patterns require name resolution" $
    validationMessages "fn f() {let (x, [y, x]) = value;}" `shouldBe`
      Just []

  test "repeated constant patterns in parameters and lets pass syntax validation" $
    validationMessages
      "const U: () = (); fn f(U: (), U: ()) {let (U, U) = ((), ());}" `shouldBe`
      Just []

  test "constant names in consecutive for loops pass syntax validation" $
    validationMessages
      "const U: () = (); fn f() {for U in [()] {} for U in [()] {}}" `shouldBe`
      Just []

  test "repeated parameter names do not skip type validation" $
    map length (validationMessages "fn f(x: &mut qbit, x: &mut qbit) {}") `shouldBe`
      Just 2

  test "a control basis matching the number of controls is accepted" $
    validationMessages
      "fn f() {ctrl(q0, q1).on(bs\"10\").apply(H)(q2);}" `shouldBe`
      Just []

  test "a missing control basis is accepted" $
    validationMessages
      "fn f() {ctrl(q0, q1).apply(H)(q2); ctrl(q0) {H(q1);}}" `shouldBe`
      Just []

  test "a control basis shorter than the callable controls is rejected" $
    validationMessages
      "fn f() {ctrl(q0, q1).on(bs\"1\").apply(H)(q2);}" `shouldBe`
      Just
        [ "test-fixture.rs:1:25: control basis contains 1 states, but " ++
          "the control expression has 2 control qbits"
        ]

  test "a control basis longer than the block controls is rejected" $
    validationMessages "fn f() {ctrl(q0).on(bs\"10\") {H(q1);}}" `shouldBe`
      Just
        [ "test-fixture.rs:1:21: control basis contains 2 states, but " ++
          "the control expression has 1 control qbits"
        ]

  test "valid contextual forms pass post-parse validation" $
    validationMessages
      "#[qasm_gate]\nfn f(x: &mut i32) {loop {break;} while ready {continue;} return}" `shouldBe`
      Just []

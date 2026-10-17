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

  test "mutable qubit references are rejected after parsing" $
    validationMessages "fn f(q: &mut qubit) {}" `shouldBe`
      Just
        [ "test-fixture.rs:1:9: `mut` should never be written on a qubit reference; " ++
          "qubit references are mutable by default"
        ]

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
    map length (validationMessages "fn f(x: &mut qubit, x: &mut qubit) {}") `shouldBe`
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
          "the control expression has 2 control qubits"
        ]

  test "a control basis longer than the block controls is rejected" $
    validationMessages "fn f() {ctrl(q0).on(bs\"10\") {H(q1);}}" `shouldBe`
      Just
        [ "test-fixture.rs:1:21: control basis contains 2 states, but " ++
          "the control expression has 1 control qubits"
        ]

  test "valid contextual forms pass post-parse validation" $
    validationMessages
      "#[qasm_gate]\nfn f(x: &mut i32) {loop {break;} while ready {continue;} return}" `shouldBe`
      Just []

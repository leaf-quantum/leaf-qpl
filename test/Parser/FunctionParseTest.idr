module Parser.FunctionParseTest

import Test.Simple

import Parser.Helper

%default total

export
runFunctionParseTests : IO ()
runFunctionParseTests = runTests $ Test.do

  test "empty function" $
    parseAndPrettyPrint "fn empty() {}" `shouldBe` Just "fn empty() { }"

  test "a raw integer literal in place of a function name is described by kind" $
    parseErrorDetails "fn 5() {}" `shouldBe`
      Just
        ( "Parse error: expected ['function name'], but got raw integer literal `5`"
        , "test-fixture.rs"
        , (1, 4)
        , (1, 5)
        )

  test "pub empty function" $
    parseAndPrettyPrint "pub fn empty() {}" `shouldBe` Just "pub fn empty() { }"

  test "empty function with unit output" $
    parseAndPrettyPrint "fn empty() -> () {}" `shouldBe` Just "fn empty() -> () { }"

  test "unitary empty function with unit output" $
    parseAndPrettyPrint "unitary fn empty() -> () {}" `shouldBe` Just "unitary fn empty() -> () { }"

  test "uncompsafe function effect" $
    parseAndPrettyPrint "uncompsafe fn empty() {}" `shouldBe`
      Just "uncompsafe fn empty() { }"

  test "const classical function" $
    parseAndPrettyPrint
      "const classical fn multBy2(i: i32) -> i32 { 2 * i }" `shouldBe`
      Just "const classical fn multBy2(i: i32) -> i32 { (2 * i) }"

  test "public const classical function" $
    parseAndPrettyPrint
      "pub const classical fn multBy2(i: i32) -> i32 { 2 * i }" `shouldBe`
      Just "pub const classical fn multBy2(i: i32) -> i32 { (2 * i) }"

  test "public const function without an effect" $
    parseAndPrettyPrint "pub const fn square(x: i64) -> i64 { x * x }" `shouldBe`
      Just "pub const fn square(x: i64) -> i64 { (x * x) }"

  test "pub unitary empty function with unit output" $
    parseAndPrettyPrint "pub unitary fn empty() -> () {}" `shouldBe` Just "pub unitary fn empty() -> () { }"

  test "empty function with unit output and simple annotation" $
    parseAndPrettyPrint "#[qasm_gate]\nfn empty() -> () {}" `shouldBe` Just "#[qasm_gate]\nfn empty() -> () { }"

  test "empty general pub function with unit output and annotation with text" $
    parseAndPrettyPrint  "#[qasm_def(\"qasm_subroutine_name\")]\npub general fn empty() -> () {}" 
      `shouldBe` Just "#[qasm_def(\"qasm_subroutine_name\")]\npub general fn empty() -> () { }"

  test "function with two annotations" $
    parseAndPrettyPrint  "#[qasm_gate]\n#[qasm_def(\"qasm_subroutine_name\")]\npub general fn empty() -> () {}" 
      `shouldBe` Just "#[qasm_gate]\n#[qasm_def(\"qasm_subroutine_name\")]\npub general fn empty() -> () { }"

  test "empty function with parameters" $
    parseAndPrettyPrint "fn add(i : i32, point : (i32, i32)) {}" `shouldBe` Just "fn add(i: i32, point: (i32, i32)) { }"

  test "function parameters accept a trailing comma" $
    parseAndPrettyPrint "fn add(i: i32, point: (i32, i32),) {}" `shouldBe`
      Just "fn add(i: i32, point: (i32, i32)) { }"

  test "function parameters reject a missing middle parameter" $
    parseAndPrettyPrint "fn add(i: i32,, point: i32) {}" `shouldBe` Nothing

  test "mutable function parameter" $
    parseAndPrettyPrint "fn increment(mut x: i32) -> i32 { x += 1; x }"
      `shouldBe` Just "fn increment(mut x: i32) -> i32 { x += 1; x }"

  test "named and path types" $
    parseAndPrettyPrint "fn use_types(person: Person, config: my_module::Config) {}"
      `shouldBe` Just "fn use_types(person: Person, config: my_module::Config) { }"

  test "path types with more than two segments" $
    parseAndPrettyPrint "fn use_types(value: root::inner::Leaf) {}"
      `shouldBe` Just "fn use_types(value: root::inner::Leaf) { }"

  test "reference and slice types" $
    parseAndPrettyPrint
      "fn borrow(q: &qubit, person: &Person, mutable: &mut Person, values: &[i32], output: &mut [i32]) {}"
      `shouldBe`
      Just
        "fn borrow(q: &qubit, person: &Person, mutable: &mut Person, values: &[i32], output: &mut [i32]) { }"

  test "reference types require an inner type" $
    parseErrorDetails "fn f(x: &) {}" `shouldBe`
      Just
        ( "Parse error: expected ['a type declaration'], but got symbol )"
        , "test-fixture.rs"
        , (1, 10)
        , (1, 11)
        )

  test "a builtin in place of a type is described by kind" $
    parseErrorDetails "fn f(x: measr) {}" `shouldBe`
      Just
        ( "Parse error: expected ['a type declaration'], but got builtin measr"
        , "test-fixture.rs"
        , (1, 9)
        , (1, 14)
        )

  test "array parameter types accept expression lengths" $
    parseAndPrettyPrint "fn f(a: [i32; 2 + 2]) {}" `shouldBe`
      Just "fn f(a: [i32; (2 + 2)]) { }"

  test "node identifiers follow source order through parameter types" $
    parseAndListNodeIds "fn f(c: a::b::c, r: &mut P) {}" `shouldBe`
      Just [0, 1, 3, 5, 10, 12, 14, 17]

  test "qualified types" $
    parseAndPrettyPrint
      "fn qualified(q: affine qubit, pair: (linear qubit, affine qubit)) {}"
      `shouldBe`
      Just
        "fn qualified(q: affine qubit, pair: (linear qubit, affine qubit)) { }"

  test "conflicting ownership qualifiers in a type are rejected" $
    parseErrorDetails "fn bad(q: linear affine qubit) {}" `shouldBe`
      Just
        ( "Cannot combine `linear` and `affine` storage qualifiers."
        , "test-fixture.rs"
        , (1, 18)
        , (1, 24)
        )

  test "duplicate ownership qualifiers in a type are rejected" $
    parseErrorDetails "fn bad(q: affine affine qubit) {}" `shouldBe`
      Just
        ( "Duplicate `affine` storage qualifier."
        , "test-fixture.rs"
        , (1, 18)
        , (1, 24)
        )

  test "scratch qualifier in a type is rejected" $
    parseErrorDetails "fn bad(q: scratch qubit) {}" `shouldBe`
      Just
        ( "The `scratch` qualifier is only allowed on `let` bindings, not in types: write `let scratch q: qubit = ...`."
        , "test-fixture.rs"
        , (1, 11)
        , (1, 18)
        )

  test "scratch qualifier after an ownership qualifier in a type is rejected" $
    parseAndPrettyPrint "fn bad(q: linear scratch qubit) {}" `shouldBe` Nothing

  test "scratch qualifier in a nested type is rejected" $
    parseAndPrettyPrint "fn bad(f: fn(value: qubit) -> (scratch qubit, qubit)) {}" `shouldBe` Nothing

  test "a qualifier followed by a non-type keyword is rejected" $
    parseErrorDetails "fn bad(q: linear if) {}" `shouldBe`
      Just
        ( "The `linear` qualifier can only qualify `qubit`, not keyword if."
        , "test-fixture.rs"
        , (1, 18)
        , (1, 20)
        )

  test "qualified qubits inside nested type forms" $
    parseAndPrettyPrint
      "fn nested(q: fn(value: affine qubit) -> (linear qubit, [affine qubit])) {}"
      `shouldBe`
      Just
        "fn nested(q: fn(value: affine qubit) -> (linear qubit, [affine qubit])) { }"

  test "qualified array elements" $
    parseAndPrettyPrint "fn f(qs: [affine qubit; 2], rs: [[linear qubit; 2]; 3]) {}"
      `shouldBe`
      Just "fn f(qs: [affine qubit; 2], rs: [[linear qubit; 2]; 3]) { }"

  test "a qualified array type is rejected" $
    parseErrorDetails "fn bad(qs: linear [qubit; 2]) {}" `shouldBe`
      Just
        ( "The `linear` qualifier cannot qualify an array or slice: qualify the qubits of an array instead, e.g. `[linear qubit; 2]`."
        , "test-fixture.rs"
        , (1, 19)
        , (1, 20)
        )

  test "a qualified array type in a let annotation is rejected" $
    parseErrorDetails "fn f() { let qs: affine [qubit; 2] = qalloc(2); }" `shouldBe`
      Just
        ( "The `affine` qualifier cannot qualify an array or slice: qualify the qubits of an array instead, e.g. `[affine qubit; 2]`."
        , "test-fixture.rs"
        , (1, 25)
        , (1, 26)
        )

  test "a qualifier directly behind a reference is rejected" $
    parseErrorDetails "fn bad(q: &affine qubit) {}" `shouldBe`
      Just
        ( "The `affine` qualifier cannot be written behind a reference: a reference borrows its referent without owning it, so remove the qualifier."
        , "test-fixture.rs"
        , (1, 12)
        , (1, 18)
        )

  test "a qualifier directly behind a mutable reference is rejected" $
    parseErrorDetails "fn bad(q: &mut linear qubit) {}" `shouldBe`
      Just
        ( "The `linear` qualifier cannot be written behind a reference: a reference borrows its referent without owning it, so remove the qualifier."
        , "test-fixture.rs"
        , (1, 16)
        , (1, 22)
        )

  test "a qualified slice behind a reference is rejected as behind a reference" $
    parseErrorDetails "fn bad(qs: &linear [qubit]) {}" `shouldBe`
      Just
        ( "The `linear` qualifier cannot be written behind a reference: a reference borrows its referent without owning it, so remove the qualifier."
        , "test-fixture.rs"
        , (1, 13)
        , (1, 19)
        )

  test "scratch directly behind a reference is rejected as scratch in a type" $
    parseErrorDetails "fn bad(q: &scratch qubit) {}" `shouldBe`
      Just
        ( "The `scratch` qualifier is only allowed on `let` bindings, not in types: write `let scratch q: qubit = ...`."
        , "test-fixture.rs"
        , (1, 12)
        , (1, 19)
        )

  test "a qualifier nested behind a reference is left to post-parse validation" $
    parseAndPrettyPrint "fn f(qs: &[linear qubit]) {}"
      `shouldBe` Just "fn f(qs: &[linear qubit]) { }"

  test "a qualified tuple type is rejected" $
    parseErrorDetails "fn bad(p: affine (qubit, qubit)) {}" `shouldBe`
      Just
        ( "The `affine` qualifier cannot qualify a parenthesized type or tuple: qualify each qubit inside it instead, e.g. `affine qubit` or `(affine qubit, affine qubit)`."
        , "test-fixture.rs"
        , (1, 18)
        , (1, 19)
        )

  test "a qualified parenthesized qubit is rejected" $
    parseErrorDetails "fn bad(q: linear (qubit)) {}" `shouldBe`
      Just
        ( "The `linear` qualifier cannot qualify a parenthesized type or tuple: qualify each qubit inside it instead, e.g. `linear qubit` or `(linear qubit, linear qubit)`."
        , "test-fixture.rs"
        , (1, 18)
        , (1, 19)
        )

  test "a qualified function type is rejected" $
    parseErrorDetails "fn bad(f: linear fn(q: qubit)) {}" `shouldBe`
      Just
        ( "The `linear` qualifier can only qualify `qubit`, not keyword fn."
        , "test-fixture.rs"
        , (1, 18)
        , (1, 20)
        )

  test "higher-order function types" $
    parseAndPrettyPrint
      "general fn phase_kickback(oracle: unitary fn(qs: [qubit; 4], target: qubit) -> ([qubit; 4], qubit)) {}"
      `shouldBe`
      Just
        "general fn phase_kickback(oracle: unitary fn(qs: [qubit; 4], target: qubit) -> ([qubit; 4], qubit)) { }"

  test "function type without an effect or return type" $
    parseAndPrettyPrint "fn callback(f: fn(value: i32)) {}"
      `shouldBe` Just "fn callback(f: fn(value: i32)) { }"

  test "function parameter outer doc comments are not yet supported" $
    parseErrorDetails "fn f(\n/// docs\nx: i32) {}" `shouldBe`
      Just
        ( "Documentation comments on function parameters are not yet supported."
        , "test-fixture.rs"
        , (2, 1)
        , (2, 9)
        )

  test "function supports clauses are not yet supported" $
    parseErrorDetails "fn f() supports adjoint {}" `shouldBe`
      Just
        ( "Function `supports` clauses are not yet supported."
        , "test-fixture.rs"
        , (1, 8)
        , (1, 16)
        )

  test "requires contract clauses are not yet supported" $
    parseErrorDetails "fn f() requires clean(q) {}" `shouldBe`
      Just
        ( "Quantum contracts `requires` and/or `ensures` are not yet supported."
        , "test-fixture.rs"
        , (1, 8)
        , (1, 16)
        )

  test "ensures contract clauses are not yet supported" $
    parseErrorDetails "fn f() ensures basis(q, X) {}" `shouldBe`
      Just
        ( "Quantum contracts `requires` and/or `ensures` are not yet supported."
        , "test-fixture.rs"
        , (1, 8)
        , (1, 15)
        )

  test "function with a simple statement" $
    parseAndPrettyPrint "fn simple() {let i: i32 = 1;}" `shouldBe` Just "fn simple() { let i: i32 = 1; }"

  test "function with a simple return expression" $
    parseAndPrettyPrint "fn simple_expression() -> i64 {1}" `shouldBe` Just "fn simple_expression() -> i64 { 1 }"

  test "annotation applied to a statement instead to a function declaration" $
    parseErrorDetails "#[qasm_gate]\nlet i = 1;" `shouldBe`
      Just ("Expected function declaration after attribute, found instead: `let`.", "test-fixture.rs", (2, 1), (2, 4))

  test "attributes on const declarations are not yet supported" $
    parseErrorDetails "#[qasm_gate]\nconst N: i64 = 4;" `shouldBe`
      Just
        ( "Attributes on const declarations are not yet supported."
        , "test-fixture.rs"
        , (2, 7)
        , (2, 8)
        )

  test "function or constant expected after pub visibility modifier" $
    parseErrorDetails "pub let i = 1;" `shouldBe`
      Just ("Expected function or constant declaration after `pub` visibility modifier, found instead: `let`.", "test-fixture.rs", (1, 5), (1, 8))

  test "function keyword expected after function effect" $
    parseErrorDetails "pub general let i = 1;" `shouldBe`
      Just ("Expected `fn` after `general` effect modifier, found instead: `let`.", "test-fixture.rs", (1, 13), (1, 16))

  test "function keyword expected before a non-keyword after function effect" $
    parseErrorDetails "general foo" `shouldBe`
      Just ("Expected `fn` after `general` effect modifier, found instead: `foo`.", "test-fixture.rs", (1, 9), (1, 12))

  test "function keyword expected after const and function effect" $
    parseErrorDetails "const general let i = 1;" `shouldBe`
      Just ("Expected `fn` after `general` effect modifier, found instead: `let`.", "test-fixture.rs", (1, 15), (1, 18))

  test "malformed attribute, missing closing bracket" $
    parseErrorDetails "#[qasm_gate \nfn empty() -> () {}" `shouldBe`
      Just ("Malformed attribute.", "test-fixture.rs", (1, 1), (1, 2))

  test "malformed attribute, extra content" $
    parseErrorDetails "#[qasm_gate bogus_name] \nfn empty() -> () {}" `shouldBe`
      Just ("Malformed attribute.", "test-fixture.rs", (1, 1), (1, 2))

  test "malformed attribute with argument, missing closing bracket" $
    parseErrorDetails "#[qasm_def(\"qasm_subroutine_name\") \nfn empty() -> () {}" `shouldBe`
      Just ("Malformed attribute.", "test-fixture.rs", (1, 1), (1, 2))

  test "malformed attribute with argument, extra content" $
    parseErrorDetails "#[qasm_def(\"qasm_subroutine_name\") bogus_name] \nfn empty() -> () {}" `shouldBe`
      Just ("Malformed attribute.", "test-fixture.rs", (1, 1), (1, 2))

  test "function without opening brace" $
    parseErrorDetails "fn empty(); }" `shouldBe`
      Just ("Expected a braced block starting with `{`, found instead: `;`.", "test-fixture.rs", (1, 11), (1, 12))

  test "function with statement missing semicolon" $
    parseErrorDetails "fn simple() { let i: i32 = 1; 2 let j = 3;" `shouldBe`
      Just ("Expected `;` or `}`, found instead: `let`.", "test-fixture.rs", (1, 33), (1, 36))

  -- debugTestParseError "fn simple() { let i: i32 = 1; 2 let j = 3;"

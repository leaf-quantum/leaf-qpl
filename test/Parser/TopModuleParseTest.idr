module Parser.TopModuleParseTest

import Test.Simple

import Parser.Helper

%default total

export
runTopModuleParseTests : IO ()
runTopModuleParseTests = runTests $ Test.do

  test "empty input parses as an empty output" $
    parseAndPrettyPrint "" `shouldBe` Just ""

  test "input containing only ordinary comments parses as an empty output" $
    parseAndPrettyPrint "// nothing here\n/* still nothing */" `shouldBe`
      Just ""

  test "module declarations are not yet supported" $
    parseErrorDetails "mod my_library;" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:1, with message: Modules are not yet supported."
        , (1, 4)
        )

  test "use statements are not yet supported" $
    parseErrorDetails "use my_library::helper;" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:1, with message: Use statements are not yet supported."
        , (1, 4)
        )

  test "constant expression declaration" $
    parseAndPrettyPrint "const N: i64 = 4;" `shouldBe`
      Just "const N: i64 = 4;"

  test "public constant expression declaration" $
    parseAndPrettyPrint "pub const MAX_USERS: i16 = 100;" `shouldBe`
      Just "pub const MAX_USERS: i16 = 100;"

  test "constant function declaration" $
    parseAndPrettyPrint
      "const fn square(x: i64) -> i64 {\n    x * x\n}" `shouldBe`
      Just "const fn square(x: i64) -> i64 { (x * x) }"

  test "constant declarations accept array types with expression lengths" $
    parseAndPrettyPrint "const A: [i32; 2 + 2] = [1, 2, 3, 4];" `shouldBe`
      Just "const A: [i32; (2 + 2)] = [1, 2, 3, 4];"

  test "constant declarations report a missing constant name" $
    parseErrorDetails "const struct Point {}" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:7, with message: expected 'constant name', but got keyword struct"
        , (1, 13)
        )

  test "constant declarations require a colon after the name" $
    parseErrorDetails "const N i64 = 4;" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:9, with message: Expected `:` after constant name, found instead: `i64`."
        , (1, 12)
        )

  test "constant declarations require an equals sign after the type" $
    parseErrorDetails "const N: i64 4;" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:14, with message: Expected `=` in const declaration, found instead: `4`."
        , (1, 15)
        )

  test "constant declarations require a semicolon after the value" $
    parseErrorDetails "const N: i64 = 4 }" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:18, with message: Expected `;` after const declaration, found instead: `}`."
        , (1, 19)
        )

  test "enum declarations are not yet supported" $
    parseErrorDetails "enum Result {}" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:1, with message: Enums are not yet supported."
        , (1, 5)
        )

  test "qenum declarations are not yet supported" $
    parseErrorDetails "qenum QResult {}" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:1, with message: Qenums are not yet supported."
        , (1, 6)
        )

  test "struct declarations are not yet supported" $
    parseErrorDetails "struct Point {}" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:1, with message: Structs are not yet supported."
        , (1, 7)
        )

  test "struct declarations after pub visibility are not yet supported" $
    parseErrorDetails "pub struct Point {}" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:5, with message: Structs are not yet supported."
        , (1, 11)
        )

  test "impl blocks are not yet supported" $
    parseErrorDetails "impl Point {}" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:1, with message: Impl blocks and structs are not yet supported."
        , (1, 5)
        )

  test "impl blocks after a function effect are not yet supported" $
    parseErrorDetails "general impl Point {}" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:9, with message: Impl blocks and structs are not yet supported."
        , (1, 13)
        )

  test "impl blocks after const and a function effect are not yet supported" $
    parseErrorDetails "const general impl Point {}" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:15, with message: Impl blocks and structs are not yet supported."
        , (1, 19)
        )

  test "unsupported top-level items after a function effect preserve their error" $
    parseErrorDetails "general mod my_library;" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:9, with message: Modules are not yet supported."
        , (1, 12)
        )

  test "unsupported top-level items after const and a function effect preserve their error" $
    parseErrorDetails "const general mod my_library;" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:15, with message: Modules are not yet supported."
        , (1, 18)
        )

  test "non-keyword items after const and a function effect report the effect" $
    parseErrorDetails "const general foo" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:15, with message: Expected `fn` after `general` effect modifier, found instead: `foo`."
        , (1, 18)
        )

  test "node identifiers account for each declaration prefix modifier" $
    map parseAndListNodeIds
      [ "fn f() {}"
      , "pub fn f() {}"
      , "const fn f() {}"
      , "pub const fn f() {}"
      , "pub const unitary fn f() {}"
      , "#[qasm_gate]\nfn f() {}"
      ] `shouldBe`
      [ Just [0, 1, 3]
      , Just [0, 1, 4]
      , Just [0, 1, 4]
      , Just [0, 1, 5]
      , Just [0, 1, 6]
      , Just [0, 1, 5]
      ]

  test "outer doc comments are not yet supported" $
    parseErrorDetails "/// docs\n" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:1, with message: Outer doc comments are not yet supported."
        , (1, 9)
        )

  test "inner doc comments are not yet supported" $
    parseErrorDetails "//! module docs" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:1, with message: Inner doc comments are not yet supported."
        , (1, 16)
        )

  test "unexpected top-level tokens report the token" $
    parseErrorDetails "let i = 1;" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:1, with message: Unexpected token: `let` at module level. Only function and constant declarations are currently supported."
        , (1, 4)
        )

  test "unexpected non-keyword top-level tokens report the token" $
    parseErrorDetails "foo" `shouldBe`
      Just
        ( "Parse error at: test-fixture.rs:1:1, with message: Unexpected token: `foo` at module level. Only function and constant declarations are currently supported."
        , (1, 4)
        )

module CompileCodeExamplesTest

import Test.Simple

import CompileCodeExamples

%default total

isFailure : Either String () -> Bool
isFailure (Left _)  = True
isFailure (Right _) = False

export
runCompileCodeExamplesTests : IO ()
runCompileCodeExamplesTests = runTests $ Test.do

  test "the source compilation pipeline accepts a valid program" $
    compileLeafSource "test-fixture.rs" "fn f() {}" `shouldBe` Right ()

  test "the source compilation pipeline desugars and resolves local and prelude names" $
    compileLeafSource "test-fixture.rs" "fn f() { let mut x = 1; x += 2; sin(x) }"
      `shouldBe` Right ()

  test "the source compilation pipeline reports unresolved names" $
    compileLeafSource "test-fixture.rs" "fn f() { missing; }" `shouldBe`
      Left "Resolution error in test-fixture.rs: Unresolved name 'missing' at 1:10"

  test "the source compilation pipeline resolves quantum gate calls" $
    compileLeafSource "test-fixture.rs"
      "fn f() { let q = qalloc(); H(&q); X(&q); U1(0.25, &q); measr(q) }"
      `shouldBe` Right ()

  test "the source compilation pipeline reports both duplicate declaration positions" $
    compileLeafSource "test-fixture.rs" "fn f() {}\nfn f() {}" `shouldBe`
      Left "Resolution error in test-fixture.rs: Duplicate declaration 'f' at 2:4; previous declaration at 1:4"

  test "the source compilation pipeline reports bindings that shadow constants" $
    compileLeafSource "test-fixture.rs" "const N: i32 = 1;\nfn f() { let N = 2; }" `shouldBe`
      Left "Resolution error in test-fixture.rs: Binding 'N' at 2:14 shadows the constant declared at 1:7"

  test "the source compilation pipeline reports lexer failures" $
    isFailure (compileLeafSource "test-fixture.rs" "@") `shouldBe` True

  test "the source compilation pipeline reports parser failures" $
    isFailure (compileLeafSource "test-fixture.rs" "fn f( {}") `shouldBe` True

  test "the source compilation pipeline reports every validation failure" $
    compileLeafSource "test-fixture.rs" "fn f() {break; continue;}" `shouldBe`
      Left
        ( "Validation errors in test-fixture.rs:\n" ++
          "test-fixture.rs:1:9: `break` found outside of a loop\n" ++
          "test-fixture.rs:1:16: `continue` found outside of a loop\n"
        )

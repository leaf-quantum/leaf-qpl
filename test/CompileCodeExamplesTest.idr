module CompileCodeExamplesTest

import Test.Simple

import Compiler.ScopeAndNameResolution.Data
import Main

%default total

-- Runs the same pipeline as the leaf executable, discarding the resolved module.
compile : String -> Either String ()
compile source = map (const ()) (compileSource "test-fixture.rs" source)

isFailure : Either String () -> Bool
isFailure (Left _)  = True
isFailure (Right _) = False

export
runCompileCodeExamplesTests : IO ()
runCompileCodeExamplesTests = runTests $ Test.do

  test "the source compilation pipeline accepts a valid program" $
    compile "fn f() {}" `shouldBe` Right ()

  test "the source compilation pipeline desugars and resolves local and prelude names" $
    compile "fn f() { let mut x = 1; x += 2; sin(x) }" `shouldBe` Right ()

  test "the source compilation pipeline reports unresolved names" $
    compile "fn f() { missing; }" `shouldBe`
      Left "Could not find a matching declaration for this name: 'missing' in 'file: '' at line: '1' and column: '10''."

  test "the source compilation pipeline resolves quantum gate calls" $
    compile "fn f() { let q = qalloc(); H(&q); X(&q); U1(0.25, &q); measr(q) }" `shouldBe` Right ()

  test "the source compilation pipeline reports both duplicate declaration positions" $
    compile "fn f() {}\nfn f() {}" `shouldBe`
      Left "A duplicate declaration for name: 'f' declared in 'file: '' at line: '2' and column: '4'' was found; the previous declaration is in 'file: '' at line: '1' and column: '4''."

  test "the source compilation pipeline reports mutable bindings that shadow constants" $
    compile "const N: i32 = 1;\nfn f() { let mut N = 2; }" `shouldBe`
      Left "The mutable binding for name: 'N' in 'file: '' at line: '2' and column: '18'' cannot shadow the constant declared in 'file: '' at line: '1' and column: '7''."

  test "the source compilation pipeline accepts repeated constant patterns" $
    compile "const U: () = (); fn f(U: (), U: ()) { let (U, U) = ((), ()); for U in [()] {} }"
      `shouldBe` Right ()

  test "the source compilation pipeline reports locals used in constant expressions" $
    compile "fn f(n: i32) {\n  [0; n];\n}" `shouldBe`
      Left "The local: 'n' used in 'file: '' at line: '2' and column: '7'' is not a constant and cannot be used in an array length or repeat count; it is declared in 'file: '' at line: '1' and column: '6''."

  test "the source compilation pipeline reports lexer failures" $
    isFailure (compile "@") `shouldBe` True

  test "the source compilation pipeline reports parser failures" $
    isFailure (compile "fn f( {}") `shouldBe` True

  test "the source compilation pipeline reports every validation failure" $
    compile "fn f() {break; continue;}" `shouldBe`
      Left
        ( "Validation errors:\n" ++
          "test-fixture.rs:1:9: `break` found outside of a loop\n" ++
          "test-fixture.rs:1:16: `continue` found outside of a loop"
        )

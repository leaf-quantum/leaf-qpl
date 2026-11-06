module TypeChecker.Phases.TypedAstTranslationTest

import Test.Simple

import Compiler.TypeChecker.Data
import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Phase T: the typed AST
--------------------------------------------------------------------------------
-- Translation rebuilds the checked resolved AST node for node in the typed
-- phase (plan §6). Each test pretty-prints the typed AST of a program that
-- type-checks and expects exactly the printed desugared and resolved AST,
-- including the nodes desugaring generated: default effects and result
-- types, returns, unit else blocks, ctrl selectors, moved and default
-- qualifiers and attribute arguments. Named members never reach translation:
-- pass B rejects them first.
--------------------------------------------------------------------------------

-- Items and generated nodes (plan §6.1, §6.2)
itemTranslationTests : List ETest
itemTranslationTests = Test.do
  test "an empty function keeps its generated effect, result type and return" $
    printedTypedAst "fn f() {}"
      `shouldBe` Right "general fn f() -> () { return (); }"

  test "a final expression keeps its generated return" $
    printedTypedAst "fn f() -> i32 { 1 }"
      `shouldBe` Right "general fn f() -> i32 { return 1; }"

  test "a constant item is translated" $
    printedTypedAst "const FIVE: i32 = 5;"
      `shouldBe` Right "const FIVE: i32 = 5;"

  test "several items are translated in order" $
    printedTypedAst "const N: u32 = 2; fn f(a: [i32; N]) -> i32 { a[0] } fn g() -> i32 { f([1, 2]) }"
      `shouldBe` Right "const N: u32 = 2;\ngeneral fn f(a: [i32; N]) -> i32 { return a[0]; }\ngeneral fn g() -> i32 { return f([1, 2]); }"

  test "the generated return after diverging branches is kept" $
    printedTypedAst "fn f(c: bool) -> i32 { if c { return 1; } else { return 2; }; }"
      `shouldBe` Right "general fn f(c: bool) -> i32 { if c { return 1; } else { return 2; }; return (); }"

  test "a final if without else keeps its generated else block" $
    printedTypedAst "fn f(c: bool) { if c { let x = 1; } }"
      `shouldBe` Right "general fn f(c: bool) -> () { return if c { let x = 1; } else { () }; }"

  test "attributes keep their generated name argument" $
    printedTypedAst "#[qasm_gate] unitary fn g(q: qbit) -> qbit { H(q) }"
      `shouldBe` Right "#[qasm_gate(\"g\")]\nunitary fn g(q: linear qbit) -> linear qbit { return H(q); }"

  test "a function-typed parameter keeps its generated qualifiers" $
    printedTypedAst "fn run(g: unitary fn(q: qbit) -> qbit, q: qbit) -> qbit { g(q) }"
      `shouldBe` Right "general fn run(g: unitary fn(q: linear qbit) -> linear qbit, q: linear qbit) -> linear qbit { return g(q); }"

  test "array length expressions in types are translated" $
    printedTypedAst "const N: u32 = 2; fn f(a: [i32; N + 1]) -> [i32; N + 1] { a }"
      `shouldBe` Right "const N: u32 = 2;\ngeneral fn f(a: [i32; (N + 1)]) -> [i32; (N + 1)] { return a; }"

-- Statements and patterns (plan §6.2)
statementTranslationTests : List ETest
statementTranslationTests = Test.do
  test "let bindings, assignments and compound assignments are translated" $
    printedTypedAst "fn f() -> i32 { let mut x: i32 = 0; x = 2; x += 1; x }"
      `shouldBe` Right "general fn f() -> i32 { let mut x: i32 = 0; x = 2; x += 1; return x; }"

  test "tuple, wildcard, unit and array patterns are translated" $
    printedTypedAst "fn f() -> i32 { let (a, _) = (1, 2); let () = (); let [b, c] = [3, 4]; a + b + c }"
      `shouldBe` Right "general fn f() -> i32 { let (a, _) = (1, 2); let () = (); let [b, c] = [3, 4]; return ((a + b) + c); }"

  test "a unit constant-name pattern is translated as a constant path" $
    printedTypedAst "const UNIT: () = (); fn f() { let UNIT = (); }"
      `shouldBe` Right "const UNIT: () = ();\ngeneral fn f() -> () { let UNIT = (); return (); }"

  test "a unit constant-name parameter is translated" $
    printedTypedAst "const UNIT: () = (); fn f(UNIT: ()) {}"
      `shouldBe` Right "const UNIT: () = ();\ngeneral fn f(UNIT: ()) -> () { return (); }"

  test "a let multiplicity keeps its place in the annotation" $
    printedTypedAst "fn f() -> bit { let affine q: qbit = qalloc(); H(&q); measr(q) }"
      `shouldBe` Right "general fn f() -> bit { let q: affine qbit = qalloc(); H((&q)); return measr(q); }"

  test "scratch and := markers are translated" $
    printedTypedAst "uncompsafe fn flip(q: qbit) -> qbit { X(q) } fn f(t: &qbit) { let b: qbit := flip(qalloc()); CX(&b, t); let scratch a = qalloc(); CX(t, &a); }"
      `shouldBe` Right "uncompsafe fn flip(q: linear qbit) -> linear qbit { return X(q); }\ngeneral fn f(t: &qbit) -> () { let b: linear qbit := flip(qalloc()); CX((&b), t); let scratch a = qalloc(); CX(t, (&a)); return (); }"

  test "a unit constant-named for variable is translated as a constant path" $
    printedTypedAst "const UNIT: () = (); fn f() { for UNIT in [(), ()] { } }"
      `shouldBe` Right "const UNIT: () = ();\ngeneral fn f() -> () { return for UNIT in [(), ()] { }; }"

-- Expressions (plan §6.2)
expressionTranslationTests : List ETest
expressionTranslationTests = Test.do
  test "blocks, if and else-if chains are translated" $
    printedTypedAst "fn f(c: bool, x: i32) -> i32 { let y = { let a = 1; a + x }; if c { y } else if x == 0 { 0 } else { -y } }"
      `shouldBe` Right "general fn f(c: bool, x: i32) -> i32 { let y = { let a = 1; (a + x) }; return if c { y } else if (x == 0) { 0 } else { (-y) }; }"

  test "loops, ranges and casts are translated" $
    printedTypedAst "fn f() -> u32 { let mut s: u32 = 0; for i in 0..4 { s += i; } while s > 10 { s -= 1; } let x = loop { break 3; }; s + x as u32 }"
      `shouldBe` Right "general fn f() -> u32 { let mut s: u32 = 0; for i in (0..4) { s += i; } while (s > 10) { s -= 1; } let x = loop { break 3; }; return (s + (x as u32)); }"

  test "arrays, repetition, indexing and slices are translated" $
    printedTypedAst "fn f() -> i32 { let a = [1, 2, 3]; let z = [0; 2]; let s = &a[1..]; a[0] + z[1] + s[0] }"
      `shouldBe` Right "general fn f() -> i32 { let a = [1, 2, 3]; let z = [0; 2]; let s = (&a[(1..)]); return ((a[0] + z[1]) + s[0]); }"

  test "tuples and tuple indexing are translated" $
    printedTypedAst "fn f() -> bool { let t = (1, true); t.1 }"
      `shouldBe` Right "general fn f() -> bool { let t = (1, true); return t.1; }"

  test "quantum calls and borrows are translated" $
    printedTypedAst "fn f() -> (bit, bit) { let q0 = qalloc(); let q1 = qalloc(); H(&q0); let (q0, q1) = CX(q0, q1); measr(q0, q1) }"
      `shouldBe` Right "general fn f() -> (bit, bit) { let q0 = qalloc(); let q1 = qalloc(); H((&q0)); let (q0, q1) = CX(q0, q1); return measr(q0, q1); }"

  test "ctrl and adjoint forms are translated" $
    printedTypedAst "fn f(c: &qbit, t: &qbit) { ctrl(c) { X(t); } adjoint { H(t); } ctrl(c).on(bs\"0\").apply(X)(t); adjoint(H)(t); }"
      `shouldBe` Right "general fn f(c: &qbit, t: &qbit) -> () { ctrl(c).on(bs\"1\") { X(t); } adjoint { H(t); } ctrl(c).on(bs\"0\").apply(X)(t); adjoint(H)(t); return (); }"

  test "Param and its string literal are translated" $
    printedTypedAst "fn f() -> param { Param(\"theta\") }"
      `shouldBe` Right "general fn f() -> param { return Param(\"theta\"); }"

-- Named members are rejected before translation (plan §6.1)
memberTranslationTests : List ETest
memberTranslationTests = Test.do
  test "a named field read is rejected before translation" $
    printedTypedAst "fn f() { let t = (1, 2); let x = t.first; }"
      `shouldBe` Left (show (UnknownMember "first" (spanAt 1 36)))

  test "a method call is rejected before translation" $
    printedTypedAst "fn f() { let a = [1, 2]; let n = a.size(); }"
      `shouldBe` Left (show (UnknownMember "size" (spanAt 1 36)))

  test "a field assignment is rejected before translation" $
    printedTypedAst "fn f() { let mut t = (1, 2); t.first = 3; }"
      `shouldBe` Left (show (UnknownMember "first" (spanAt 1 32)))

export
runTypedAstTranslationTests : IO ()
runTypedAstTranslationTests =
  runTests $ concat
    [ itemTranslationTests
    , statementTranslationTests
    , expressionTranslationTests
    , memberTranslationTests
    ]

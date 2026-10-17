module Desugarer.DesugaringTest

import Test.Simple

import Desugarer.Helper

%default total

export
runDesugaringTests : IO ()
runDesugaringTests = runTests $ Test.do

  test "missing return type is filled in with -> ()" $
    desugarAndPrettyPrint "general fn empty() {}"
      `shouldBe` Just "general fn empty() -> () { return (); }"

  test "missing effect is filled in with general" $
    desugarAndPrettyPrint "fn f() -> i32 { 1 }"
      `shouldBe` Just "general fn f() -> i32 { return 1; }"

  test "an explicit final return remains a single return statement" $
    desugarAndPrettyPrint "fn f() -> i32 { return 1 }"
      `shouldBe` Just "general fn f() -> i32 { return 1; }"

  test "a valueless explicit final return receives a unit value" $
    desugarAndPrettyPrint "fn f() { return }"
      `shouldBe` Just "general fn f() -> () { return (); }"

  test "a parenthesized explicit final return remains a single return statement" $
    desugarAndPrettyPrint "fn f() -> i32 { (return 2) }"
      `shouldBe` Just "general fn f() -> i32 { return 2; }"

  test "a nested parenthesized explicit final return remains a single return statement" $
    desugarAndPrettyPrint "fn f() -> i32 { ((return 2)) }"
      `shouldBe` Just "general fn f() -> i32 { return 2; }"

  test "explicitly typed qubit let binding is linear by default" $
    desugarAndPrettyPrint "fn allocate() { let q: qubit = qalloc(); }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let linear q: qubit = qalloc(); return (); }"

  test "explicitly typed qubit array let binding is linear by default" $
    desugarAndPrettyPrint "fn allocate() { let qs: [qubit; 3] = qalloc(3); }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let linear qs: [qubit; 3] = qalloc(3); return (); }"

  test "explicitly typed qubit tuple let binding is linear by default" $
    desugarAndPrettyPrint
      "fn allocate() { let qs: (qubit, qubit) = (qalloc(), qalloc()); }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let linear qs: (qubit, qubit) = (qalloc(), qalloc()); return (); }"

  test "mixed tuple containing a qubit is linear by default" $
    desugarAndPrettyPrint
      "fn allocate() { let pair: (i32, qubit) = (0, qalloc()); }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let linear pair: (i32, qubit) = (0, qalloc()); return (); }"

  test "parenthesized qubit type is linear by default" $
    desugarAndPrettyPrint "fn allocate() { let q: ((qubit)) = qalloc(); }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let linear q: qubit = qalloc(); return (); }"

  test "qubit reference let binding is not linear by default" $
    desugarAndPrettyPrint "fn borrow(q: &qubit) { let qref: &qubit = &q; }"
      `shouldBe`
      Just
        "general fn borrow(q: &qubit) -> () { let qref: &qubit = (&q); return (); }"

  test "classical array let binding is not linear by default" $
    desugarAndPrettyPrint
      "fn values() { let values: [i32; 3] = [0, 0, 0]; }"
      `shouldBe`
      Just
        "general fn values() -> () { let values: [i32; 3] = [0, 0, 0]; return (); }"

  test "explicit affine qualifier is preserved for a qubit let binding" $
    desugarAndPrettyPrint "fn allocate() { let affine q: qubit = qalloc(); }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let affine q: qubit = qalloc(); return (); }"

  test "scratch qubit let binding is linear by default" $
    desugarAndPrettyPrint "fn allocate() { let scratch q: qubit = qalloc(); }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let scratch linear q: qubit = qalloc(); return (); }"

  test "inferred qubit let binding receives no qualifier during desugaring" $
    desugarAndPrettyPrint "fn allocate() { let q = qalloc(); }"
      `shouldBe`
      Just "general fn allocate() -> () { let q = qalloc(); return (); }"

  test "default attribute argument is added if argument is missing" $
    desugarAndPrettyPrint "#[qasm_gate]\ngeneral fn myFun() -> () {}"
      `shouldBe`
      Just "#[qasm_gate(\"myFun\")]\ngeneral fn myFun() -> () { return (); }"

  test "nested expressions round-trip through the canonical printer" $
    desugarAndPrettyPrint "fn add(x: i32) -> i32 { x + 1 }"
      `shouldBe` Just "general fn add(x: i32) -> i32 { return (x + 1); }"

  test "one control receives the default basis bs\"1\"" $
    desugarAndPrettyPrint "fn f() { ctrl(q0).apply(H)(q1); }"
      `shouldBe`
      Just
        "general fn f() -> () { ctrl(q0).on(bs\"1\").apply(H)(q1); return (); }"

  test "multiple controls receive one default basis 1 each" $
    desugarAndPrettyPrint "fn f() { ctrl(q0, q1, q2).apply(H)(q3); }"
      `shouldBe`
      Just
        "general fn f() -> () { ctrl(q0, q1, q2).on(bs\"111\").apply(H)(q3); return (); }"

  test "an explicitly written control basis is preserved" $
    desugarAndPrettyPrint
      "fn f() { ctrl(q0, q1).on(bs\"10\").apply(H)(q2); }"
      `shouldBe`
      Just
        "general fn f() -> () { ctrl(q0, q1).on(bs\"10\").apply(H)(q2); return (); }"

  test "+= is preserved for later compound-assignment lowering" $
    desugarAndPrettyPrint "fn assign() { x += 1; }"
      `shouldBe` Just "general fn assign() -> () { x += 1; return (); }"

  test "-= is preserved for later compound-assignment lowering" $
    desugarAndPrettyPrint "fn assign() { x -= 1; }"
      `shouldBe` Just "general fn assign() -> () { x -= 1; return (); }"

  test "*= is preserved for later compound-assignment lowering" $
    desugarAndPrettyPrint "fn assign() { x *= 2; }"
      `shouldBe` Just "general fn assign() -> () { x *= 2; return (); }"

  test "/= is preserved for later compound-assignment lowering" $
    desugarAndPrettyPrint "fn assign() { x /= 2; }"
      `shouldBe` Just "general fn assign() -> () { x /= 2; return (); }"

  test "%= is preserved for later compound-assignment lowering" $
    desugarAndPrettyPrint "fn assign() { x %= 2; }"
      `shouldBe` Just "general fn assign() -> () { x %= 2; return (); }"

  test "&= is preserved for later compound-assignment lowering" $
    desugarAndPrettyPrint "fn assign() { x &= 3; }"
      `shouldBe` Just "general fn assign() -> () { x &= 3; return (); }"

  test "|= is preserved for later compound-assignment lowering" $
    desugarAndPrettyPrint "fn assign() { x |= 3; }"
      `shouldBe` Just "general fn assign() -> () { x |= 3; return (); }"

  test "^= is preserved for later compound-assignment lowering" $
    desugarAndPrettyPrint "fn assign() { x ^= 3; }"
      `shouldBe` Just "general fn assign() -> () { x ^= 3; return (); }"

  test "<<= is preserved for later compound-assignment lowering" $
    desugarAndPrettyPrint "fn assign() { x <<= 2; }"
      `shouldBe` Just "general fn assign() -> () { x <<= 2; return (); }"

  test ">>= is preserved for later compound-assignment lowering" $
    desugarAndPrettyPrint "fn assign() { x >>= 2; }"
      `shouldBe` Just "general fn assign() -> () { x >>= 2; return (); }"

  test "compound assignment keeps a single call in its index" $
    desugarAndPrettyPrint "fn assign() { a[next()] += 1; }"
      `shouldBe` Just "general fn assign() -> () { a[next()] += 1; return (); }"

  test "compound assignment keeps a single block and declaration in its index" $
    desugarAndPrettyPrint "fn assign() { a[{ let i = 0; i }] += 1; }"
      `shouldBe` Just "general fn assign() -> () { a[{ let i = 0; i }] += 1; return (); }"

  test "compound assignment keeps a single call in its field base" $
    desugarAndPrettyPrint "fn assign() { next().field += 1; }"
      `shouldBe` Just "general fn assign() -> () { next().field += 1; return (); }"

  test "compound assignment keeps a single call in its tuple-index base" $
    desugarAndPrettyPrint "fn assign() { next().0 += 1; }"
      `shouldBe` Just "general fn assign() -> () { next().0 += 1; return (); }"

  test "missing classical else is filled in with a unit block" $
    desugarAndPrettyPrint "fn f() { if ready {} }"
      `shouldBe`
      Just "general fn f() -> () { if ready { } else { () } return (); }"

  test "const declarations desugar unchanged" $
    desugarAndPrettyPrint "const N: i64 = 4;"
      `shouldBe` Just "const N: i64 = 4;"

  -- Parenthesization nodes carry no meaning past the surface AST
  -- so the canonical AST holds the bare inner node.

  test "ExprParenthesized is discarded during canonicalization (1)" $
    desugarAndPrettyPrint "fn wrap() -> i32 { ((1 + 2)) }"
      `shouldBe` Just "general fn wrap() -> i32 { return (1 + 2); }"

  test "ExprParenthesized is discarded during canonicalization (2)" $
    desugarAndPrettyPrint "fn wrap() -> i32 { (3) }"
      `shouldBe` Just "general fn wrap() -> i32 { return 3; }"

  test "TyParenthesized is discarded during canonicalization (3)" $
    desugarAndPrettyPrint "fn t(x: (i32)) -> (i32) { x }"
      `shouldBe` Just "general fn t(x: i32) -> i32 { return x; }"

  test "PatternParenthesized is discarded during canonicalization (4)" $
    desugarAndPrettyPrint "fn p() { let (a) = 1; }"
      `shouldBe` Just "general fn p() -> () { let a = 1; return (); }"

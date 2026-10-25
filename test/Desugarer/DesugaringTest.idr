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
        "general fn allocate() -> () { let q: linear qubit = qalloc(); return (); }"

  test "explicitly typed qubit array let binding has linear elements by default" $
    desugarAndPrettyPrint "fn allocate() { let qs: [qubit; 3] = qalloc(3); }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let qs: [linear qubit; 3] = qalloc(3); return (); }"

  test "nested qubit arrays have linear innermost elements by default" $
    desugarAndPrettyPrint "fn allocate() { let qs: [[qubit; 2]; 3] = qalloc(6); }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let qs: [[linear qubit; 2]; 3] = qalloc(6); return (); }"

  test "explicitly typed qubit tuple let binding is linear by default" $
    desugarAndPrettyPrint
      "fn allocate() { let qs: (qubit, qubit) = (qalloc(), qalloc()); }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let qs: (linear qubit, linear qubit) = (qalloc(), qalloc()); return (); }"

  test "only the qubit element of a mixed tuple is linear by default" $
    desugarAndPrettyPrint
      "fn allocate() { let pair: (i32, qubit) = (0, qalloc()); }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let pair: (i32, linear qubit) = (0, qalloc()); return (); }"

  test "parenthesized qubit type is linear by default" $
    desugarAndPrettyPrint "fn allocate() { let q: ((qubit)) = qalloc(); }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let q: linear qubit = qalloc(); return (); }"

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

  test "an explicit affine let qualifier moves into the qubit type" $
    desugarAndPrettyPrint "fn allocate() { let affine q: qubit = qalloc(); }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let q: affine qubit = qalloc(); return (); }"

  test "an explicit linear let qualifier moves into the qubit array elements" $
    desugarAndPrettyPrint "fn allocate() { let linear qs: [qubit; 2] = qalloc(2); }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let qs: [linear qubit; 2] = qalloc(2); return (); }"

  test "an explicit let qualifier moves into every owned qubit position" $
    desugarAndPrettyPrint
      "fn allocate() { let affine (a, n, qs): (qubit, i32, [qubit; 2]) = (qalloc(), 0, qalloc(2)); }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let (a, n, qs): (affine qubit, i32, [affine qubit; 2]) = (qalloc(), 0, qalloc(2)); return (); }"

  test "a moved let qualifier keeps the span of the written keyword at every position" $
    firstLetTypeQualifierSpans
      "fn allocate() { let affine (a, qs): (qubit, [qubit; 2]) = (qalloc(), qalloc(2)); }"
      `shouldBe` Just [((1, 21), (1, 27)), ((1, 21), (1, 27))]

  test "a default qualifier takes the span of the type it qualifies" $
    firstLetTypeQualifierSpans "fn allocate() { let q: qubit = qalloc(); }"
      `shouldBe` Just [((1, 24), (1, 29))]

  test "a default qualifier on an array element takes the span of the element" $
    firstLetTypeQualifierSpans "fn allocate() { let qs: [qubit; 2] = qalloc(2); }"
      `shouldBe` Just [((1, 26), (1, 31))]

  test "an explicit let qualifier stays on a let without owned qubit positions" $
    desugarAndPrettyPrint "fn allocate() { let linear r: &qubit = &q; }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let linear r: &qubit = (&q); return (); }"

  test "an explicit let qualifier stays on a let without a type annotation" $
    desugarAndPrettyPrint "fn allocate() { let affine q = qalloc(); }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let affine q = qalloc(); return (); }"

  test "scratch qubit let binding is linear by default" $
    desugarAndPrettyPrint "fn allocate() { let scratch q: qubit = qalloc(); }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let scratch q: linear qubit = qalloc(); return (); }"

  test "scratch with an explicit ownership qualifier keeps scratch on the let" $
    desugarAndPrettyPrint "fn allocate() { let affine scratch q: qubit = qalloc(); }"
      `shouldBe`
      Just
        "general fn allocate() -> () { let scratch q: affine qubit = qalloc(); return (); }"

  test "qubit parameters, qubit array parameters and qubit results are linear by default" $
    desugarAndPrettyPrint
      "unitary fn f(q: qubit, qs: [qubit; 2], n: i32, r: &qubit) -> (qubit, [qubit; 2]) { (q, qs) }"
      `shouldBe`
      Just
        "unitary fn f(q: linear qubit, qs: [linear qubit; 2], n: i32, r: &qubit) -> (linear qubit, [linear qubit; 2]) { return (q, qs); }"

  test "an explicitly qualified parameter keeps its qualifier" $
    desugarAndPrettyPrint "fn f(q: affine qubit) {}"
      `shouldBe`
      Just "general fn f(q: affine qubit) -> () { return (); }"

  test "qubits inside function types are linear by default" $
    desugarAndPrettyPrint
      "fn run(oracle: unitary fn(qs: [qubit; 4], target: qubit) -> ([qubit; 4], qubit)) {}"
      `shouldBe`
      Just
        "general fn run(oracle: unitary fn(qs: [linear qubit; 4], target: linear qubit) -> ([linear qubit; 4], linear qubit)) -> () { return (); }"

  test "an array of mixed tuples qualifies only the qubit elements" $
    desugarAndPrettyPrint "fn f(pairs: [(qubit, i32); 2]) {}"
      `shouldBe`
      Just "general fn f(pairs: [(linear qubit, i32); 2]) -> () { return (); }"

  test "qubits inside a referenced function type are linear by default" $
    desugarAndPrettyPrint "fn run(oracle: &fn(q: qubit) -> qubit) {}"
      `shouldBe`
      Just
        "general fn run(oracle: &fn(q: linear qubit) -> linear qubit) -> () { return (); }"

  test "qubits inside a function type in a let annotation are linear by default" $
    desugarAndPrettyPrint "fn run(g: fn(q: qubit)) { let affine h: fn(q: qubit) = g; }"
      `shouldBe`
      Just
        "general fn run(g: fn(q: linear qubit)) -> () { let affine h: fn(q: linear qubit) = g; return (); }"

  test "a qubit const type is linear by default" $
    desugarAndPrettyPrint "const C: qubit = 3;"
      `shouldBe` Just "const C: linear qubit = 3;"

  test "a qubit cast target is linear by default" $
    desugarAndPrettyPrint "fn f() { let q = 3 as qubit; }"
      `shouldBe`
      Just "general fn f() -> () { let q = (3 as linear qubit); return (); }"

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

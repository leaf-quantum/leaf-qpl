module Parser.ExpressionParseTest

import Test.Simple

import Parser.Helper

%default total

export
runExpressionParseTests : IO ()
runExpressionParseTests = runTests $ Test.do

  test "function with a simple assignment statement" $
    parseAndPrettyPrint "fn assign() {x = 1;}" `shouldBe` Just "fn assign() { x = 1; }"

  test "function with compound assignment statements" $
    parseAndPrettyPrint "fn assign() {x += 1; x <<= 2; x &= 3;}" `shouldBe`
      Just "fn assign() { x += 1; x <<= 2; x &= 3; }"

  test "boolean literal expressions" $
    parseAndPrettyPrint "fn booleans() {true; false}" `shouldBe`
      Just "fn booleans() { true; false }"

  test "float literal expressions" $
    parseAndPrettyPrint "fn floats() {1.0; 12E+99_f64}" `shouldBe`
      Just "fn floats() { 1.0; 12E+99_f64 }"

  test "basis string literal expressions" $
    parseAndPrettyPrint
      "fn states() {bs\"10110010\"; bs\"++----++\"; bs\"10+-+-001\"; bs\"iiiiIIIII\"}" `shouldBe`
      Just
        "fn states() { bs\"10110010\"; bs\"++----++\"; bs\"10+-+-001\"; bs\"iiiiIIIII\" }"

  test "basis string literals in inferred let bindings" $
    parseAndPrettyPrint
      "fn states() {let a = bs\"10110010\"; let b = bs\"++----++\"; let c = bs\"10+-+-001\"; let d = bs\"iiiiIIIII\";}" `shouldBe`
      Just
        "fn states() { let a = bs\"10110010\"; let b = bs\"++----++\"; let c = bs\"10+-+-001\"; let d = bs\"iiiiIIIII\"; }"

  test "tuple and wildcard let patterns" $
    parseAndPrettyPrint
      "fn destructure() {let (a, b, c) = (1, 2, 3); let (x, _, z) = (1, 2, 3);}" `shouldBe`
      Just
        "fn destructure() { let (a, b, c) = (1, 2, 3); let (x, _, z) = (1, 2, 3); }"

  test "array let pattern with type annotation" $
    parseAndPrettyPrint
      "fn measure() {let [b0, b1, b2]: [bit; 3] = measr(qs);}" `shouldBe`
      Just
        "fn measure() { let [b0, b1, b2]: [bit; 3] = measr(qs); }"

  test "mutable let bindings can be reassigned" $
    parseAndPrettyPrint
      "fn mutable() { let mut x: i32 = 0; x = 5; let mut values = [0, 0]; values[0] = 10; }"
      `shouldBe`
      Just
        "fn mutable() { let mut x: i32 = 0; x = 5; let mut values = [0, 0]; values[0] = 10; }"

  test "constant expression in array type declaration" $
    parseAndPrettyPrint
      "fn arrays() { let b: [i32; 2 + 2]; }" `shouldBe`
      Just "fn arrays() { let b: [i32; (2 + 2)]; }"

  test "parenthesized constant expression in initialized array type declaration" $
    parseAndPrettyPrint
      "fn arrays() { let b: [i32; (2 + 2)] = [1, 2, 3, 4]; }" `shouldBe`
      Just "fn arrays() { let b: [i32; ((2 + 2))] = [1, 2, 3, 4]; }"

  test "named constant in array type declaration" $
    parseAndPrettyPrint
      "const N: i64 = 4;\nfn arrays() { let c: [i32; N]; }" `shouldBe`
      Just "const N: i64 = 4;\nfn arrays() { let c: [i32; N]; }"

  test "array type reports valid continuations after its element type" $
    parseErrorDetails "fn arrays() { let b: [i32 value]; }" `shouldBe`
      Just
        ( "Parse error: expected [']', ';'], but got identifier \"value\""
        , "test-fixture.rs"
        , (1, 27)
        , (1, 32)
        )

  test "quantum storage qualifiers on let bindings" $
    parseAndPrettyPrint
      "fn allocate() {let linear q: qubit = qalloc(); let affine a: qubit = qalloc(); let scratch linear qs: [qubit; 2] = qalloc(2); let affine scratch t: qubit = qalloc();}" `shouldBe`
      Just
        "fn allocate() { let linear q: qubit = qalloc(); let affine a: qubit = qalloc(); let scratch linear qs: [qubit; 2] = qalloc(2); let affine scratch t: qubit = qalloc(); }"

  test "conflicting multiplicity qualifiers on let bindings are rejected" $
    parseAndPrettyPrint
      "fn bad() {let linear affine q: qubit = qalloc();}" `shouldBe` Nothing

  test "duplicate scratch qualifiers on let bindings are rejected" $
    parseAndPrettyPrint
      "fn bad() {let scratch scratch q: qubit = qalloc();}" `shouldBe` Nothing

  test "auto-uncompute let initializer" $
    parseAndPrettyPrint
      "fn compute() {let q: qubit := f(q); let result := compute_value();}" `shouldBe`
      Just
        "fn compute() { let q: qubit := f(q); let result := compute_value(); }"

  test "let bindings report the markers accepted after a pattern" $
    parseErrorDetails "fn f() {let x + 1;}" `shouldBe`
      Just
        ( "Parse error: expected [':', '=', ':='], but got symbol +"
        , "test-fixture.rs"
        , (1, 15)
        , (1, 16)
        )

  test "let bindings report the markers accepted after a type annotation" $
    parseErrorDetails "fn f() {let x: i32 + 1;}" `shouldBe`
      Just
        ( "Parse error: expected ['=', ':='], but got symbol +"
        , "test-fixture.rs"
        , (1, 20)
        , (1, 21)
        )

  test "a builtin in place of a let pattern is described by kind" $
    parseErrorDetails "fn f() {let measr = 1;}" `shouldBe`
      Just
        ( "Parse error: expected ['a pattern'], but got builtin measr"
        , "test-fixture.rs"
        , (1, 13)
        , (1, 18)
        )

  test "a raw integer literal in place of a let pattern is described by kind" $
    parseErrorDetails "fn f() {let 5 = 1;}" `shouldBe`
      Just
        ( "Parse error: expected ['a pattern'], but got raw integer literal `5`"
        , "test-fixture.rs"
        , (1, 13)
        , (1, 14)
        )

  test "a raw float literal in place of a let pattern is described by kind" $
    parseErrorDetails "fn f() {let 5.0 = 1;}" `shouldBe`
      Just
        ( "Parse error: expected ['a pattern'], but got raw float literal `5.0`"
        , "test-fixture.rs"
        , (1, 13)
        , (1, 16)
        )

  test "a raw byte literal in place of a let pattern is described by kind" $
    parseErrorDetails "fn f() {let b'a' = 1;}" `shouldBe`
      Just
        ( "Parse error: expected ['a pattern'], but got raw byte literal `b'a'`"
        , "test-fixture.rs"
        , (1, 13)
        , (1, 17)
        )

  test "a raw byte string literal in place of a let pattern is described by kind" $
    parseErrorDetails "fn f() {let b\"hi\" = 1;}" `shouldBe`
      Just
        ( "Parse error: expected ['a pattern'], but got raw byte string literal `b\"hi\"`"
        , "test-fixture.rs"
        , (1, 13)
        , (1, 18)
        )

  test "a raw basis string literal in place of a let pattern is described by kind" $
    parseErrorDetails "fn f() {let bs\"01\" = 1;}" `shouldBe`
      Just
        ( "Parse error: expected ['a pattern'], but got raw basis string literal `bs\"01\"`"
        , "test-fixture.rs"
        , (1, 13)
        , (1, 19)
        )

  test "a raw string literal in place of a let pattern is described by kind" $
    parseErrorDetails "fn f() {let \"hi\" = 1;}" `shouldBe`
      Just
        ( "Parse error: expected ['a pattern'], but got raw string literal `\"hi\"`"
        , "test-fixture.rs"
        , (1, 13)
        , (1, 17)
        )

  test "a boolean literal in place of a let pattern is described by kind" $
    parseErrorDetails "fn f() {let true = 1;}" `shouldBe`
      Just
        ( "Parse error: expected ['a pattern'], but got boolean literal true"
        , "test-fixture.rs"
        , (1, 13)
        , (1, 17)
        )

  test "a state literal in place of a let pattern is described by kind" $
    parseErrorDetails "fn f() {let zero = 1;}" `shouldBe`
      Just
        ( "Parse error: expected ['a pattern'], but got state literal zero"
        , "test-fixture.rs"
        , (1, 13)
        , (1, 17)
        )

  test "a primitive type in place of a let pattern is described by kind" $
    parseErrorDetails "fn f() {let i32 = 1;}" `shouldBe`
      Just
        ( "Parse error: expected ['a pattern'], but got primitive type i32"
        , "test-fixture.rs"
        , (1, 13)
        , (1, 16)
        )

  test "an outer doc comment in place of a let pattern is described by kind" $
    parseErrorDetails "fn f() { let /// doc\nx = 1; }" `shouldBe`
      Just
        ( "Parse error: expected ['a pattern'], but got outer doc comment \"/// doc\""
        , "test-fixture.rs"
        , (1, 14)
        , (1, 21)
        )

  test "an inner doc comment in place of a let pattern is described by kind" $
    parseErrorDetails "fn f() { let //! doc\nx = 1; }" `shouldBe`
      Just
        ( "Parse error: expected ['a pattern'], but got inner doc comment \"//! doc\""
        , "test-fixture.rs"
        , (1, 14)
        , (1, 21)
        )

  test "an underscore in place of an expression is described by kind" $
    parseErrorDetails "fn f() { let _ = 1; _(); }" `shouldBe`
      Just
        ( "Parse error: expected ['an expression'], but got underscore"
        , "test-fixture.rs"
        , (1, 21)
        , (1, 22)
        )

  test "end of input in place of a closing bracket is described by kind" $
    parseErrorDetails "fn f() { let b: [i32; 2 " `shouldBe`
      Just
        ( "Parse error: expected [']'], but got end of input"
        , "test-fixture.rs"
        , (1, 25)
        , (1, 26)
        )

  test "unit literal expression" $
    parseAndPrettyPrint "fn unit() {()}" `shouldBe` Just "fn unit() { () }"

  test "parenthesized expression" $
    parseAndPrettyPrint "fn parenthesized() {(value)}" `shouldBe`
      Just "fn parenthesized() { (value) }"

  test "tuple expressions" $
    parseAndPrettyPrint "fn tuples() {(value,); (1, true); (1, (2, 3),)}" `shouldBe`
      Just "fn tuples() { (value,); (1, true); (1, (2, 3)) }"

  test "array expressions" $
    parseAndPrettyPrint "fn arrays() {[]; [1, 2, 3]; [1, 2, 3,]}" `shouldBe`
      Just "fn arrays() { []; [1, 2, 3]; [1, 2, 3] }"

  test "repeated array expression" $
    parseAndPrettyPrint "fn repeated() {[0; 3]}" `shouldBe`
      Just "fn repeated() { [0; 3] }"

  test "unary operator expressions" $
    parseAndPrettyPrint "fn unary() {-x; !x; &x; &mut x}" `shouldBe`
      Just "fn unary() { (-x); (!x); (&x); (&mut x) }"

  test "nested unary and postfix expressions" $
    parseAndPrettyPrint "fn unary() {!!flag; -f(x); &values[i]}" `shouldBe`
      Just "fn unary() { (!(!flag)); (-f(x)); (&values[i]) }"

  test "arithmetic binary precedence" $
    parseAndPrettyPrint "fn arithmetic() {1 + 2 * 3; 8 / 2 % 3 - 1}" `shouldBe`
      Just "fn arithmetic() { (1 + (2 * 3)); (((8 / 2) % 3) - 1) }"

  test "shift comparison and equality precedence" $
    parseAndPrettyPrint "fn comparisons() {a + b << c < d && e == f}" `shouldBe`
      Just "fn comparisons() { ((((a + b) << c) < d) && (e == f)) }"

  test "bitwise and logical precedence" $
    parseAndPrettyPrint "fn logic() {a & b ^ c | d && e || f}" `shouldBe`
      Just "fn logic() { (((((a & b) ^ c) | d) && e) || f) }"

  test "all comparison operators" $
    parseAndPrettyPrint "fn comparisons() {a <= b; a > b; a >= b; a != b}" `shouldBe`
      Just "fn comparisons() { (a <= b); (a > b); (a >= b); (a != b) }"

  test "comparison operators cannot be chained" $
    parseErrorDetails "fn f() {a < b < c}" `shouldBe`
      Just
        ( "Comparison operators cannot be chained. Parenthesize one of the comparisons."
        , "test-fixture.rs"
        , (1, 15)
        , (1, 16)
        )

  test "mixed equality and ordering comparisons cannot be chained" $
    parseErrorDetails "fn f() {a < b == c}" `shouldBe`
      Just
        ( "Comparison operators cannot be chained. Parenthesize one of the comparisons."
        , "test-fixture.rs"
        , (1, 15)
        , (1, 17)
        )

  test "parenthesized comparisons may be compared explicitly" $
    parseAndPrettyPrint "fn comparisons() {(a < b) < c; a < (b < c)}"
      `shouldBe`
      Just "fn comparisons() { (((a < b)) < c); (a < ((b < c))) }"

  test "cast expressions" $
    parseAndPrettyPrint "fn casts() {x as i32; value as i32 as i64}" `shouldBe`
      Just "fn casts() { (x as i32); ((value as i32) as i64) }"

  test "cast to an array type with an expression length" $
    parseAndPrettyPrint "fn casts() {x as [i32; 2 + 2]}" `shouldBe`
      Just "fn casts() { (x as [i32; (2 + 2)]) }"

  test "cast precedence" $
    parseAndPrettyPrint "fn casts() {-x as i32 + y as i32}" `shouldBe`
      Just "fn casts() { (((-x) as i32) + (y as i32)) }"

  test "range expressions" $
    parseAndPrettyPrint "fn ranges() {1..5; 1..=5; 1..; ..5; ..=5; ..}" `shouldBe`
      Just "fn ranges() { (1..5); (1..=5); (1..); (..5); (..=5); (..) }"

  test "inclusive range requires an end expression" $
    parseAndPrettyPrint "fn ranges() {1..=}" `shouldBe` Nothing

  test "range endpoint precedence" $
    parseAndPrettyPrint "fn ranges() {1 + 2..3 * 4; ..x as i32}" `shouldBe`
      Just "fn ranges() { ((1 + 2)..(3 * 4)); (..(x as i32)) }"

  test "open-ended ranges terminate at commas and closing delimiters" $
    parseAndPrettyPrint "fn ranges() {g(1.., ..2, ..); [1.., ..]; (1.., ..)}" `shouldBe`
      Just "fn ranges() { g((1..), (..2), (..)); [(1..), (..)]; ((1..), (..)) }"

  test "block expression" $
    parseAndPrettyPrint "fn block() {{1}}" `shouldBe`
      Just "fn block() { { 1 } }"

  test "classical if expressions" $
    parseAndPrettyPrint "fn choose() {if ready {1} else if retry {2} else {3}}" `shouldBe`
      Just "fn choose() { if ready { 1 } else if retry { 2 } else { 3 } }"

  test "else-if chains nest to arbitrary depth" $
    parseAndPrettyPrint
      "fn choose() {if a {1} else if b {2} else if c {3} else {4}}" `shouldBe`
      Just "fn choose() { if a { 1 } else if b { 2 } else if c { 3 } else { 4 } }"

  test "if expressions require a braced body" $
    parseErrorDetails "fn f() {if ready}" `shouldBe`
      Just
        ( "Expected a braced block starting with `{`, found instead: `}`."
        , "test-fixture.rs"
        , (1, 17)
        , (1, 18)
        )

  test "else is left unconsumed when followed by neither a block nor an if" $
    parseErrorDetails "fn f() {if ready {1} else 2}" `shouldBe`
      Just
        ( "Parse error: expected ['an expression'], but got keyword else"
        , "test-fixture.rs"
        , (1, 22)
        , (1, 26)
        )

  test "quantum if expressions are not yet supported" $
    parseErrorDetails "fn f() {qif q {1} qelse {0}}" `shouldBe`
      Just ("Quantum if expressions are not yet supported.",
            "test-fixture.rs", (1, 9), (1, 12))

  test "match expressions are not yet supported" $
    parseErrorDetails "fn f() {match value {0 => false}}" `shouldBe`
      Just ("Match expressions are not yet supported.",
            "test-fixture.rs", (1, 9), (1, 14))

  test "quantum match expressions are not yet supported" $
    parseErrorDetails "fn f() {qmatch q {0 => false}}" `shouldBe`
      Just ("Quantum match expressions are not yet supported.",
            "test-fixture.rs", (1, 9), (1, 15))

  test "loop while and for expressions" $
    parseAndPrettyPrint "fn control() {loop {break}; while ready {continue}; for x in values {x}}" `shouldBe`
      Just "fn control() { loop { break }; while ready { continue }; for x in values { x } }"

  test "loop expressions require a braced body" $
    parseErrorDetails "fn f() {loop}" `shouldBe`
      Just
        ( "Expected a braced block starting with `{`, found instead: `}`."
        , "test-fixture.rs"
        , (1, 13)
        , (1, 14)
        )

  test "while expressions require a braced body after their condition" $
    parseErrorDetails "fn f() {while ready}" `shouldBe`
      Just
        ( "Expected a braced block starting with `{`, found instead: `}`."
        , "test-fixture.rs"
        , (1, 20)
        , (1, 21)
        )

  test "for expressions require in after their binder" $
    parseErrorDetails "fn f() {for x y {}}" `shouldBe`
      Just
        ( "Parse error: expected ['for identifier in expression'], but got keyword for"
        , "test-fixture.rs"
        , (1, 9)
        , (1, 12)
        )

  test "for expressions require a binder before in" $
    parseErrorDetails "fn f() {for in values {}}" `shouldBe`
      Just
        ( "Parse error: expected ['for identifier in expression'], but got keyword for"
        , "test-fixture.rs"
        , (1, 9)
        , (1, 12)
        )

  test "semicolon-free non-final block-like expression statements" $
    parseAndPrettyPrint
      "fn control() {if ready {work();} loop {break;} while ready {continue;} for x in values {use_value(x);} finish()}" `shouldBe`
      Just
        "fn control() { if ready { work(); } loop { break; } while ready { continue; } for x in values { use_value(x); } finish() }"

  test "block recursion terminates across every recursive continuation" $
    parseAndPrettyPrint
      "fn progress() {first(); if ready {second();} let x = third(); target.field = fourth(); loop {break;} last()}"
      `shouldBe`
      Just
        "fn progress() { first(); if ready { second(); } let x = third(); target.field = fourth(); loop { break; } last() }"

  test "block recursion terminates when a later statement is malformed" $
    parseAndPrettyPrint
      "fn progress() {first(); if ready {second();} let x = third(); fourth() let y = fifth();}"
      `shouldBe` Nothing

  test "statement-leading block expressions stop before following expression tokens" $
    parseAndPrettyPrint
      "fn boundaries() {if ready {} -value; loop {} (value); while ready {} [0]; for x in values {} {1} ctrl(&q0) {} -other; adjoint {} [1]}"
      `shouldBe`
      Just
        "fn boundaries() { if ready { } (-value); loop { } (value); while ready { } [0]; for x in values { } { 1 } ctrl((&q0)) { } (-other); adjoint { } [1] }"

  test "parenthesized block-like expressions retain ordinary continuation syntax" $
    parseAndPrettyPrint "fn continuation() {(if ready {1} else {2}) + 3}"
      `shouldBe`
      Just "fn continuation() { ((if ready { 1 } else { 2 }) + 3) }"

  test "break continue and return expressions" $
    parseAndPrettyPrint "fn exits() {break 1; continue; return; return value}" `shouldBe`
      Just "fn exits() { break 1; continue; return; return value }"

  test "state if expressions are not yet supported" $
    parseErrorDetails "fn f() {sif state {1} else {0}}" `shouldBe`
      Just ("State if expressions are not yet supported.",
            "test-fixture.rs", (1, 9), (1, 12))

  test "state match expressions are not yet supported" $
    parseErrorDetails "fn f() {smatch state {0 => 1}}" `shouldBe`
      Just ("State match expressions are not yet supported.",
            "test-fixture.rs", (1, 9), (1, 15))

  test "string literal expression" $
    parseAndPrettyPrint "fn string() {\"hello\"}" `shouldBe`
      Just "fn string() { \"hello\" }"

  test "name expressions" $
    parseAndPrettyPrint "fn names() {value; result}" `shouldBe`
      Just "fn names() { value; result }"

  test "builtin expressions" $
    parseAndPrettyPrint "fn builtins() {qalloc(); measr(q)}" `shouldBe`
      Just "fn builtins() { qalloc(); measr(q) }"

  test "function call expressions" $
    parseAndPrettyPrint "fn calls() {f(); f(x, y)}" `shouldBe`
      Just "fn calls() { f(); f(x, y) }"

  test "struct literal expressions are not yet supported" $
    parseErrorDetails "fn f() {Point {x: 1, y: 2}}" `shouldBe`
      Just ("Struct literal expressions are not yet supported.",
            "test-fixture.rs", (1, 9), (1, 14))

  test "self expressions are not yet supported" $
    parseErrorDetails "fn f() {self.field}" `shouldBe`
      Just ("Self expressions are not yet supported.",
            "test-fixture.rs", (1, 9), (1, 13))

  test "controlled callable expression" $
    parseAndPrettyPrint
      "fn f() {ctrl(q0, q1).apply(H)(q2)}" `shouldBe`
      Just "fn f() { ctrl(q0, q1).apply(H)(q2) }"

  test "controlled callable expression with borrowed qubits and basis" $
    parseAndPrettyPrint
      "fn f() {ctrl(&q0, &q1).on(bs\"10\").apply(H)(&q2)}" `shouldBe`
      Just "fn f() { ctrl((&q0), (&q1)).on(bs\"10\").apply(H)((&q2)) }"

  test "controlled generic callable expression" $
    parseAndPrettyPrint
      "fn f() {ctrl(q0, q1).on(bs\"++\").apply(f)(q2, q3)}" `shouldBe`
      Just "fn f() { ctrl(q0, q1).on(bs\"++\").apply(f)(q2, q3) }"

  test "controlled block expression" $
    parseAndPrettyPrint "fn f() {ctrl(&q0, &q1) {H(&q2);}}" `shouldBe`
      Just "fn f() { ctrl((&q0), (&q1)) { H((&q2)); } }"

  test "controlled block expression with basis" $
    parseAndPrettyPrint
      "fn f() {ctrl(&q0, &q1).on(bs\"++\") {f(&q2, &q3);}}" `shouldBe`
      Just
        "fn f() { ctrl((&q0), (&q1)).on(bs\"++\") { f((&q2), (&q3)); } }"

  test "semicolon-free non-final quantum modifier blocks" $
    parseAndPrettyPrint
      "fn f() {ctrl(&q0) {H(&q1);} adjoint {H(&q1);} finish()}" `shouldBe`
      Just
        "fn f() { ctrl((&q0)) { H((&q1)); } adjoint { H((&q1)); } finish() }"

  test "control expression requires a control qubit" $
    parseErrorDetails "fn f() {ctrl().apply(H)(q)}" `shouldBe`
      Just ("`ctrl` requires at least one control qubit.",
            "test-fixture.rs", (1, 9), (1, 15))

  test "adjoint as a higher-order callable" $
    parseAndPrettyPrint "fn use_adjoint() {let f_adjoint = adjoint(f);}" `shouldBe`
      Just "fn use_adjoint() { let f_adjoint = adjoint(f); }"

  test "adjoint callable application" $
    parseAndPrettyPrint "fn f() {adjoint(f)(q1, q2, q3)}" `shouldBe`
      Just "fn f() { adjoint(f)(q1, q2, q3) }"

  test "adjoint callable application with borrowed qubits" $
    parseAndPrettyPrint "fn f() {adjoint(f)(&q1, &q2, &q3)}" `shouldBe`
      Just "fn f() { adjoint(f)((&q1), (&q2), (&q3)) }"

  test "adjoint block expression" $
    parseAndPrettyPrint "fn f() {adjoint {f(&q1, &q2, &q3);}}" `shouldBe`
      Just "fn f() { adjoint { f((&q1), (&q2), (&q3)); } }"

  test "adjoint block with built-in gates" $
    parseAndPrettyPrint "fn f() {adjoint {H(&q1); CT(&q1, &q2)}}" `shouldBe`
      Just "fn f() { adjoint { H((&q1)); CT((&q1), (&q2)) } }"

  test "adjoint applied to built-in gates" $
    parseAndPrettyPrint "fn f() {adjoint(CT)(&q1, &q2); adjoint(H)(&q1)}" `shouldBe`
      Just "fn f() { adjoint(CT)((&q1), (&q2)); adjoint(H)((&q1)) }"

  test "adjoint requires one callable" $
    parseErrorDetails "fn f() {adjoint()}" `shouldBe`
      Just ("`adjoint(...)` requires one callable expression.",
            "test-fixture.rs", (1, 16), (1, 18))

  test "postfix index field tuple-index and method-call expressions" $
    parseAndPrettyPrint "fn postfix() {a[i]; p.x; t.0; a.len()}" `shouldBe`
      Just "fn postfix() { a[i]; p.x; t.0; a.len() }"

  test "chained postfix expressions" $
    parseAndPrettyPrint "fn postfix() {values()[i].field.len()}" `shouldBe`
      Just "fn postfix() { values()[i].field.len() }"

  test "postfix recursion terminates through a deep mixed chain" $
    parseAndPrettyPrint
      "fn postfix() {factory(a, b)[i].field.method(c)[j].0.next().value}"
      `shouldBe`
      Just
        "fn postfix() { factory(a, b)[i].field.method(c)[j].0.next().value }"

  test "postfix recursion terminates on an incomplete suffix" $
    parseAndPrettyPrint "fn postfix() {factory(a)[i].field.method(c)[j" `shouldBe`
      Nothing

  test "comma-list recursion terminates for nested trailing commas" $
    parseAndPrettyPrint
      "fn commas() {outer(inner(a, b,), [first(), second(),], (x, y,),)}"
      `shouldBe`
      Just
        "fn commas() { outer(inner(a, b), [first(), second()], (x, y)) }"

  test "comma-list recursion terminates on a missing middle element" $
    parseAndPrettyPrint "fn commas() {outer(first(),, third())}" `shouldBe`
      Nothing

  test "index and field assignment targets" $
    parseAndPrettyPrint "fn assign() {a[i] = 1; p.x = 2;}" `shouldBe`
      Just "fn assign() { a[i] = 1; p.x = 2; }"

  test "path expressions are not yet supported" $
    parseErrorDetails "fn f() {Data::Left}" `shouldBe`
      Just ("Path expressions are not yet supported.", "test-fixture.rs", (1, 9), (1, 13))

  test "byte literals are not yet supported" $
    parseErrorDetails "fn f() {b'a'}" `shouldBe`
      Just ("Byte literals are not yet supported.", "test-fixture.rs", (1, 9), (1, 13))

  test "byte string literals are not yet supported" $
    parseErrorDetails "fn f() {b\"hi\"}" `shouldBe`
      Just ("Byte string literals are not yet supported.", "test-fixture.rs", (1, 9), (1, 14))

  test "state literals are not yet supported" $
    parseErrorDetails "fn f() {zero}" `shouldBe`
      Just ("State literals are not yet supported.", "test-fixture.rs", (1, 9), (1, 13))

  test "node identifiers follow source order through nested control flow" $
    map parseAndListNodeIds
      [ "fn f() { if a {1} else if b {2} else {3} }"
      , "fn f() { for x in v { x } }"
      ] `shouldBe`
      [ Just [0, 1, 3, 19, 4]
      , Just [0, 1, 3, 12, 4, 7, 9, 10]
      ]

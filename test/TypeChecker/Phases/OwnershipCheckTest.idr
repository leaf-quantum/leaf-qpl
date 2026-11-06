module TypeChecker.Phases.OwnershipCheckTest

import Test.Simple

import Compiler.TypeChecker.Data
import Frontend.Syntax.Common
import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Pass C, part 2: ownership, initialization and cleanup
--------------------------------------------------------------------------------
-- OwnershipCheck interprets the recorded events over control flow (plan §8.2,
-- §8.3): definite initialization and mutability, linearity and affine drops,
-- partial moves, exclusive loans with non-lexical lifetimes, reference
-- lifetimes, and the proofs behind scratch, `:=`, uncompute and transformed
-- blocks. An initialization or mutability error points at the offending read
-- or write; a loan conflict at the conflicting access; an unconsumed or
-- unreclaimable qubit at the binding that introduced it.
--------------------------------------------------------------------------------

-- Initialization and mutability (plan §8.2 rule 1)
initializationTests : List ETest
initializationTests = Test.do
  test "a local may be initialized once after its declaration" $
    typeCheckOutcome "fn f() -> i32 { let x: i32; x = 1; x }" `shouldBe` accepted

  test "reading an uninitialized local is rejected" $
    typeCheckOutcome "fn f() -> i32 { let x: i32; x }"
      `shouldBe` rejectedWith (UninitializedPlace "x" (spanAt 1 29))

  test "a local initialized in one branch only is not definitely initialized" $
    typeCheckOutcome "fn f(c: bool) -> i32 { let x: i32; if c { x = 1; } x }"
      `shouldBe` rejectedWith (UninitializedPlace "x" (spanAt 1 52))

  test "a local initialized in both branches is definitely initialized" $
    typeCheckOutcome "fn f(c: bool) -> i32 { let x: i32; if c { x = 1; } else { x = 2; } x }"
      `shouldBe` accepted

  test "an uninitialized local in a const fn is rejected" $
    typeCheckOutcome "const fn f() -> u32 { let x: u32; x }"
      `shouldBe` rejectedWith (UninitializedPlace "x" (spanAt 1 35))

  test "a compound assignment needs an initialized target" $
    typeCheckOutcome "fn f() { let mut x: i32; x += 1; }"
      `shouldBe` rejectedWith (UninitializedPlace "x" (spanAt 1 26))

  test "a second assignment needs mut" $
    typeCheckOutcome "fn f() { let x: i32; x = 1; x = 2; }"
      `shouldBe` rejectedWith (ImmutableAssignment "x" (spanAt 1 29))

  test "an initialized immutable local cannot be reassigned" $
    typeCheckOutcome "fn f() { let x = 1; x = 2; }"
      `shouldBe` rejectedWith (ImmutableAssignment "x" (spanAt 1 21))

  test "a mutable local can be reassigned" $
    typeCheckOutcome "fn f() -> i32 { let mut x = 1; x = 2; x }" `shouldBe` accepted

  test "an element of an immutable array cannot be assigned" $
    typeCheckOutcome "fn f() { let a = [1, 2]; a[0] = 3; }"
      `shouldBe` rejectedWith (ImmutableAssignment "a" (spanAt 1 26))

  test "a field of an immutable tuple cannot be assigned" $
    typeCheckOutcome "fn f() { let t = (0, 0.0); t.0 = 3; }"
      `shouldBe` rejectedWith (ImmutableAssignment "t" (spanAt 1 28))

  test "elements of mutable arrays and tuples can be assigned" $
    typeCheckOutcome "fn f() { let mut x: [i32; 2] = [0, 0]; x[0] = 10; let mut t: (i32, f64) = (0, 0.0); t.0 = 3; }"
      `shouldBe` accepted

  test "a mutable borrow needs a mutable place" $
    typeCheckOutcome "fn f() { let x = 10; let r = &mut x; }"
      `shouldBe` rejectedWith (MutableBorrowOfImmutable "x" (spanAt 1 30))

  test "a qubit can be moved and replaced in place" $
    typeCheckOutcome "fn f() -> qbit { let mut q = qalloc(); q = H(q); q }" `shouldBe` accepted

  test "replacing a live linear qubit loses it" $
    typeCheckOutcome "fn f() -> qbit { let mut q = qalloc(); q = qalloc(); q }"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 40))

  test "a loop body runs before its break" $
    typeCheckOutcome "fn f() -> i32 { let x: i32; loop { x = 1; break; } x }" `shouldBe` accepted

  test "an immutable local assigned in a loop is assigned twice" $
    typeCheckOutcome "fn f() { let x: i32; loop { x = 1; } }"
      `shouldBe` rejectedWith (ImmutableAssignment "x" (spanAt 1 29))

  test "an immutable parameter cannot be assigned" $
    typeCheckOutcome "fn f(x: i32) { x = 1; }"
      `shouldBe` rejectedWith (ImmutableAssignment "x" (spanAt 1 16))

  test "a compound assignment needs a mutable target" $
    typeCheckOutcome "fn f() { let x = 1; x += 1; }"
      `shouldBe` rejectedWith (ImmutableAssignment "x" (spanAt 1 21))

  test "a constant cannot be assigned" $
    typeCheckOutcome "const N: i32 = 1; fn f() { N = 2; }"
      `shouldBe` rejectedWith (ImmutableAssignment "N" (spanAt 1 28))

-- Linearity and affine drops (plan §8.2 rule 2)
linearityTests : List ETest
linearityTests = Test.do
  test "a linear qubit must be consumed" $
    typeCheckOutcome "fn f() { let q = qalloc(); }"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 14))

  test "a linear qubit parameter must be consumed" $
    typeCheckOutcome "fn f(q: qbit) {}"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 6))

  test "returning a qubit consumes it" $
    typeCheckOutcome "fn f() -> qbit { qalloc() }" `shouldBe` accepted

  test "an affine qubit may be dropped" $
    typeCheckOutcome "fn f() { let affine q = qalloc(); H(&q); }" `shouldBe` accepted

  test "an affine parameter may be dropped" $
    typeCheckOutcome "fn f(q: affine qbit) {}" `shouldBe` accepted

  test "a dropped affine qubit needs a discard the effect allows" $
    typeCheckOutcome "unitary fn f(q: &qbit) { let affine a = qalloc(); CX(q, &a); }"
      `shouldBe` rejectedWith (EffectViolation EffectUnitary EffectGeneral (spanAt 1 37))

  test "a qubit consumed on one path only is not consumed" $
    typeCheckOutcome "fn f(c: bool) { let q = qalloc(); if c { discard(q); } }"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 21))

  test "a qubit consumed on every path is consumed" $
    typeCheckOutcome "fn f(c: bool) { let q = qalloc(); if c { discard(q); } else { let b = measr(q); } }"
      `shouldBe` accepted

  test "a qubit consumed only inside a loop that may not run is not consumed" $
    typeCheckOutcome "fn f(n: u32) { let q = qalloc(); for i in 0..n { discard(q); break; } }"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 20))

-- Partial moves (plan §8.2 rule 3)
partialMoveTests : List ETest
partialMoveTests = Test.do
  test "tuple components can be moved separately" $
    typeCheckOutcome "fn f() { let p = (qalloc(), qalloc()); discard(p.0); discard(p.1); }"
      `shouldBe` accepted

  test "a partially moved tuple cannot be used whole" $
    typeCheckOutcome "fn f() -> (qbit, qbit) { let p = (qalloc(), qalloc()); discard(p.0); p }"
      `shouldBe` rejectedWith (UseAfterMove "p" (spanAt 1 70))

  test "array elements at constant indexes can be moved separately" $
    typeCheckOutcome "fn f() -> [bit; 2] { let qs = qalloc(3); let (b0, b1) = measr(qs[0], qs[1]); discard(qs[2]); [b0, b1] }"
      `shouldBe` accepted

  test "an array with a moved element cannot be used whole" $
    typeCheckOutcome "fn f() { let qs = qalloc(2); discard(qs[0]); discard(qs); }"
      `shouldBe` rejectedWith (UseAfterMove "qs" (spanAt 1 54))

  test "the remaining elements of a partially moved array must be consumed" $
    typeCheckOutcome "fn f() { let qs = qalloc(2); discard(qs[0]); }"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 14))

  test "a move through a dynamic index is not tracked" $
    typeCheckOutcome "fn f(i: u32) { let qs = qalloc(2); discard(qs[i]); discard(qs[1 - i]); }"
      `shouldBe` rejectedWith (UntrackedElementMove (spanAt 1 44))

  test "a borrow through a dynamic index stays usable" $
    typeCheckOutcome "fn f(i: u32) { let qs = qalloc(4); H(&qs[i]); discard(qs); }" `shouldBe` accepted

  test "an owned qubit cannot be moved out through a reference" $
    typeCheckOutcome "fn f(qs: &[qbit]) { discard(qs[0]); }"
      `shouldBe` rejectedWith (MoveOutOfBorrow (spanAt 1 29))

  test "a moved array element can be replaced at a constant index" $
    typeCheckOutcome "fn f() { let mut qs = qalloc(2); discard(qs[0]); qs[0] = qalloc(); discard(qs); }"
      `shouldBe` accepted

-- Exclusive loans and non-lexical lifetimes (plan §8.2 rule 4)
loanTests : List ETest
loanTests = Test.do
  test "a qubit cannot be borrowed twice in one call" $
    typeCheckOutcome "fn f(q: &qbit) { CX(q, q); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 24))

  test "two different qubits can be borrowed in one call" $
    typeCheckOutcome "fn f(a: &qbit, b: &qbit) { CX(a, b); }" `shouldBe` accepted

  test "disjoint elements of a qubit slice can be borrowed together" $
    typeCheckOutcome "fn f() { let qs: [qbit; 4] = qalloc(4); let qv: &[qbit] = &qs[..]; CX(&qv[1], &qv[2]); discard(qs); }"
      `shouldBe` accepted

  test "the same element of a qubit slice cannot be borrowed twice" $
    typeCheckOutcome "fn f() { let qs: [qbit; 4] = qalloc(4); let qv: &[qbit] = &qs[..]; CX(&qv[1], &qv[1]); discard(qs); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 79))

  test "overlapping qubit slices cannot be live together" $
    typeCheckOutcome "fn f() { let qs: [qbit; 4] = qalloc(4); let a = &qs[0..2]; let b = &qs[1..3]; H(&a[0]); H(&b[0]); discard(qs); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 68))

  test "a loan ends at its last use" $
    typeCheckOutcome "fn f() { let mut a = [1, 2]; let r1 = &mut a; r1[0] = 3; let r2 = &mut a; r2[0] = 4; }"
      `shouldBe` accepted

  test "two live mutable loans of one place conflict" $
    typeCheckOutcome "fn f() { let mut a = [1, 2]; let r1 = &mut a; let r2 = &mut a; r1[0] = 3; r2[0] = 4; }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 56))

  test "shared classical loans can coexist" $
    typeCheckOutcome "fn f() -> i32 { let a = [1, 2]; let r1 = &a; let r2 = &a; r1[0] + r2[1] }"
      `shouldBe` accepted

  test "a place cannot be read while it is mutably borrowed" $
    typeCheckOutcome "fn f() { let mut a = [1, 2]; let r = &mut a; let y = a[0]; r[0] = 1; }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 54))

  test "a borrowed qubit cannot be moved while the loan is live" $
    typeCheckOutcome "fn f() { let q = qalloc(); let r = &q; discard(q); H(r); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 48))

  test "a loop index that cannot reach the target does not overlap it" $
    typeCheckOutcome "unitary fn f(qs: [qbit; 5]) -> [qbit; 5] { for i in 0..4 { ctrl(&qs[i]).apply(X)(&qs[4]); } qs }"
      `shouldBe` accepted

  test "a loop index that can reach the target overlaps it" $
    typeCheckOutcome "unitary fn f(qs: [qbit; 5]) -> [qbit; 5] { for i in 0..5 { ctrl(&qs[i]).apply(X)(&qs[4]); } qs }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 82))

  test "dynamic indexes are not proven disjoint" $
    typeCheckOutcome "fn f(qs: &[qbit], i: u32, j: u32) { CX(&qs[i], &qs[j]); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 48))

  test "a loan used again on the next iteration stays live" $
    typeCheckOutcome "fn f(qs: &[qbit]) { let r = &qs[0]; for i in 0..2 { H(r); H(&qs[0]); } }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 61))

  test "a place cannot be written while it is shared-borrowed" $
    typeCheckOutcome "fn f() { let mut a = [1, 2]; let r = &a; a[0] = 3; let y = r[0]; }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 42))

  test "a place cannot be mutably borrowed twice in one call" $
    typeCheckOutcome "fn g(a: &mut [i32], b: &mut [i32]) {} fn f() { let mut x = [1]; g(&mut x, &mut x); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 75))

  test "a place can be shared-borrowed twice in one call" $
    typeCheckOutcome "fn g(a: &[i32], b: &[i32]) {} fn f() { let x = [1]; g(&x, &x); }" `shouldBe` accepted

-- Reference lifetimes (plan §8.2 rule 5)
referenceLifetimeTests : List ETest
referenceLifetimeTests = Test.do
  test "a reference into a parameter may be returned" $
    typeCheckOutcome "fn first(xs: &[i32]) -> &i32 { &xs[0] }" `shouldBe` accepted

  test "a reference to a local cannot be returned" $
    typeCheckOutcome "fn f() -> &i32 { let x = 5; &x }"
      `shouldBe` rejectedWith (EscapingReference (spanAt 1 29))

  test "a reference to a local cannot escape inside a tuple" $
    typeCheckOutcome "fn f(a: &i32) -> (i32, &i32) { let x = 1; (x, &x) }"
      `shouldBe` rejectedWith (EscapingReference (spanAt 1 47))

  test "a block cannot return a reference to its own local" $
    typeCheckOutcome "fn f() -> i32 { let r = { let x = 1; &x }; r + 1 }"
      `shouldBe` rejectedWith (EscapingReference (spanAt 1 38))

  test "a reference to a constant may be returned without reference parameters" $
    typeCheckOutcome "const A: [i32; 2] = [1, 2]; fn f() -> &[i32] { &A }" `shouldBe` accepted

-- scratch, := and uncompute (plan §8.3)
cleanupTests : List ETest
cleanupTests = Test.do
  test "a scratch qubit computed reversibly is reclaimed at scope exit" $
    typeCheckOutcome "fn f(q: &qbit) { let scratch a = qalloc(); CX(q, &a); }" `shouldBe` accepted

  test "a scratch qubit is reclaimed on every iteration of a loop" $
    typeCheckOutcome "fn f(q: &qbit) { for i in 0..3 { let scratch a = qalloc(); CX(q, &a); } }"
      `shouldBe` accepted

  test "a scratch qubit is reclaimed when a break leaves its loop body" $
    typeCheckOutcome "fn f(q: &qbit) { for i in 0..3 { let scratch a = qalloc(); CX(q, &a); if i == 1 { break; } } }"
      `shouldBe` accepted

  test "a scratch qubit is reclaimed on an early return" $
    typeCheckOutcome "fn f(q: &qbit, c: bool) { let scratch a = qalloc(); CX(q, &a); if c { return; } }"
      `shouldBe` accepted

  test "a scratch qubit cannot be reclaimed after a gate that is not reversible classically" $
    typeCheckOutcome "fn f() { let scratch a = qalloc(); H(&a); }"
      `shouldBe` rejectedWith (UnprovableCleanup (spanAt 1 22))

  test "a scratch qubit cannot be reclaimed after its dependency changed" $
    typeCheckOutcome "fn f(q: &qbit) { let scratch a = qalloc(); CX(q, &a); H(q); }"
      `shouldBe` rejectedWith (UnprovableCleanup (spanAt 1 30))

  test "a scratch qubit cannot be reclaimed after a measurement" $
    typeCheckOutcome "fn f() -> bit { let scratch a = qalloc(); X(&a); measr(&a) }"
      `shouldBe` rejectedWith (UnprovableCleanup (spanAt 1 29))

  test "a scratch qubit cannot be returned" $
    typeCheckOutcome "fn f() -> qbit { let scratch a = qalloc(); a }"
      `shouldBe` rejectedWith (UnprovableCleanup (spanAt 1 30))

  test "a := qubit is uncomputed when the function returns" $
    typeCheckOutcome "fn f(t: &qbit) { let a: qbit := X(qalloc()); CX(&a, t); }" `shouldBe` accepted

  test "a := qubit outlives its inner block until the function returns" $
    typeCheckOutcome "fn f(t: &qbit) { { let a: qbit := X(qalloc()); CX(&a, t); } X(t); }" `shouldBe` accepted

  test "uncompute reverses a reversible computation" $
    typeCheckOutcome "fn f() { let q = X(qalloc()); let q = uncompute(q); discard(q); }" `shouldBe` accepted

  test "uncompute cannot reverse a computation that is not reversible classically" $
    typeCheckOutcome "fn f() { let q = H(qalloc()); let q = uncompute(q); discard(q); }"
      `shouldBe` rejectedWith (UnprovableCleanup (spanAt 1 39))

  test "a := qubit is uncomputed on an early return" $
    typeCheckOutcome "fn f(t: &qbit, c: bool) { let a: qbit := X(qalloc()); CX(&a, t); if c { return; } X(t); }"
      `shouldBe` accepted

  test "a := qubit cannot be returned" $
    typeCheckOutcome "fn f() -> qbit { let a: qbit := X(qalloc()); a }"
      `shouldBe` rejectedWith (UnprovableCleanup (spanAt 1 22))

  test "uncompute cannot reverse after its dependency changed" $
    typeCheckOutcome "fn f(c: &qbit) { let a = qalloc(); CX(c, &a); X(c); let a = uncompute(a); discard(a); }"
      `shouldBe` rejectedWith (UnprovableCleanup (spanAt 1 61))

  test "a scratch qubit cannot be reclaimed after its dependency is moved away" $
    typeCheckOutcome "fn f(q: qbit) { let scratch a = qalloc(); CX(&q, &a); discard(q); }"
      `shouldBe` rejectedWith (UnprovableCleanup (spanAt 1 29))

  test "shadowing a scratch qubit through a gate keeps its cleanup" $
    typeCheckOutcome "fn f(q: &qbit) { let scratch a = qalloc(); CX(q, &a); let a = X(a); CX(q, &a); }"
      `shouldBe` accepted

  test "a scratch array's cleanup skips an element discarded early" $
    typeCheckOutcome "fn f(q: &qbit) { let scratch qs = qalloc(2); CX(q, &qs[0]); discard(qs[1]); }"
      `shouldBe` accepted

-- Adjoint and control transformations (plan §7.2, §8.2 rule 6)
transformationTests : List ETest
transformationTests = Test.do
  test "an adjoint block of gates can be transformed" $
    typeCheckOutcome "fn f(q1: &qbit, q2: &qbit) { adjoint { H(q1); CT(q1, q2); } }" `shouldBe` accepted

  test "an adjoint block cannot overwrite classical state" $
    typeCheckOutcome "fn f(q: &qbit) { let mut n = 0; adjoint { n = 1; H(q); } }"
      `shouldBe` rejectedWith (UnprovableTransformation "adjoint" (spanAt 1 33))

  test "a control block cannot overwrite classical state" $
    typeCheckOutcome "fn f(c: &qbit, t: &qbit) { let mut n = 0; ctrl(c) { n = 1; X(t); } }"
      `shouldBe` rejectedWith (UnprovableTransformation "ctrl" (spanAt 1 43))

  test "an adjoint block cannot call a function that writes classical state" $
    typeCheckOutcome "unitary fn g(q: &qbit, xs: &mut [i32]) { xs[0] = 1; H(q); } fn f(q: &qbit) { let mut xs = [0]; adjoint { g(q, &mut xs); } }"
      `shouldBe` rejectedWith (UnprovableTransformation "adjoint" (spanAt 1 96))

  test "a control block may read classical state" $
    typeCheckOutcome "fn f(c: &qbit, q: &qbit, n: i32) { ctrl(c) { if n > 0 { X(q); } } }" `shouldBe` accepted

  test "an adjoint block may update a local declared inside it" $
    typeCheckOutcome "fn f(q: &qbit) { adjoint { let mut n = 0; n += 1; if n == 1 { H(q); } } }"
      `shouldBe` accepted

-- Joins, reference provenance and cleanup transfers (plan §8.1–§8.3; spec §9, §12, §42).
provenanceAndFlowTests : List ETest
provenanceAndFlowTests = Test.do
  test "a divergent branch does not invalidate initialization on the continuing branch" $
    typeCheckOutcome "fn f(c: bool) -> i32 { let x: i32; if c { return 0; } else { x = 1; } x }" `shouldBe` accepted

  test "a while body may execute zero times when establishing initialization" $
    typeCheckOutcome "fn f(c: bool) -> i32 { let x: i32; while c { x = 1; break; } x }"
      `shouldBe` rejectedWith (UninitializedPlace "x" (spanAt 1 62))

  test "a borrow also requires a definitely initialized referent" $
    typeCheckOutcome "fn f() { let x: i32; let r = &x; let y = r + 1; }"
      `shouldBe` rejectedWith (UninitializedPlace "x" (spanAt 1 30))

  test "a mutable moved local may receive a fresh resource" $
    typeCheckOutcome "fn f() { let mut q = qalloc(); discard(q); q = qalloc(); discard(q); }" `shouldBe` accepted

  test "replacing a moved tuple component restores whole-value usability" $
    typeCheckOutcome "fn f() -> (qbit, qbit) { let mut p = (qalloc(), qalloc()); discard(p.0); p.0 = qalloc(); p }"
      `shouldBe` accepted

  test "disjoint qubit subslices may be live together" $
    typeCheckOutcome "fn f() { let qs = qalloc(4); let a = &qs[..2]; let b = &qs[2..]; CX(&a[1], &b[0]); discard(qs); }" `shouldBe` accepted

  test "a child reborrow ends before the parent is used again" $
    typeCheckOutcome "fn f(qs: &[qbit]) { let r = &qs[0]; H(r); H(&qs[0]); }" `shouldBe` accepted

  test "a live child reborrow suspends conflicting parent access" $
    typeCheckOutcome "fn f(qs: &[qbit]) { let r = &qs[0]; H(&qs[0]); H(r); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 39))

  test "nested slice offsets are normalized when checking aliases" $
    typeCheckOutcome "fn f() { let qs = qalloc(4); let tail = &qs[1..]; CX(&tail[0], &qs[1]); discard(qs); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 64))

  test "conditional quantum aliases remain usable until their last use" $
    typeCheckOutcome "fn f(c: bool) { let qs = qalloc(2); let r = if c { &qs[0] } else { &qs[1] }; H(r); discard(qs); }" `shouldBe` accepted

  test "a conditional alias reserves every possible origin while live" $
    typeCheckOutcome "fn f(c: bool) { let qs = qalloc(2); let r = if c { &qs[0] } else { &qs[1] }; H(&qs[0]); H(r); discard(qs); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 80))

  test "a mutable reference binding can change its referent" $
    typeCheckOutcome "fn f() { let mut a = [1]; let mut b = [2]; let mut r = &mut a; r[0] = 3; r = &mut b; r[0] = 4; a[0] = 5; }" `shouldBe` accepted

  test "a reference returned by a function retains its input origin" $
    typeCheckOutcome "fn identity(x: &i32) -> &i32 { x } fn f() -> i32 { let x = 1; let r = identity(&x); r + 1 }" `shouldBe` accepted

  test "a reference to a local cannot escape inside an array" $
    typeCheckOutcome "fn f() -> [&i32; 1] { let x = 1; [&x] }"
      `shouldBe` rejectedWith (EscapingReference (spanAt 1 35))

  test "a parameter-origin reference may be returned inside an array" $
    typeCheckOutcome "fn f(x: &i32) -> [&i32; 1] { [x] }" `shouldBe` accepted

  test "a scratch qubit is reclaimed when continue exits its scope" $
    typeCheckOutcome "fn f(q: &qbit) { for i in 0..3 { let scratch a = qalloc(); CX(q, &a); continue; } }" `shouldBe` accepted

  test "moving a scratch resource to a different name preserves its cleanup" $
    typeCheckOutcome "fn f(q: &qbit) { let scratch a = qalloc(); let b = a; CX(q, &b); }" `shouldBe` accepted

  test "destructuring a scratch array preserves cleanup for each resource" $
    typeCheckOutcome "fn f(q: &qbit) { let scratch qs = qalloc(2); let [a, b] = qs; CX(q, &a); CX(q, &b); }" `shouldBe` accepted

-- A returned loan keeps its origin and lifetime across the call boundary
-- (plan §8.1, §8.2; spec §9, §51). The plan requires ambiguous lifetime
-- elision to fail (§5.6, §8.2), but does not prescribe a diagnostic
-- constructor. Require a reported type error for that boundary without
-- classifying it as a dangling-reference error.
returnedReferenceTests : List ETest
returnedReferenceTests = Test.do
  test "a returned qubit reference conflicts with access to its original element" $
    typeCheckOutcome "fn first(qs: &[qbit]) -> &qbit { &qs[0] } fn f(qs: &[qbit]) { let r = first(qs); H(&qs[0]); H(r); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 84))

  test "the original qubit becomes available after the returned reference's last use" $
    typeCheckOutcome "fn first(qs: &[qbit]) -> &qbit { &qs[0] } fn f(qs: &[qbit]) { let r = first(qs); H(r); H(&qs[0]); }"
      `shouldBe` accepted

  test "a returned mutable slice keeps the original array exclusively borrowed" $
    typeCheckOutcome "fn identity(xs: &mut [i32]) -> &mut [i32] { xs } fn f() { let mut a = [1, 2]; let r = identity(&mut a); a[0] = 3; r[0] = 4; }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 105))

  test "the original array is writable after a returned mutable slice's last use" $
    typeCheckOutcome "fn identity(xs: &mut [i32]) -> &mut [i32] { xs } fn f() { let mut a = [1, 2]; let r = identity(&mut a); r[0] = 4; a[0] = 3; }"
      `shouldBe` accepted

  test "a reference to a local cannot escape through a function result" $
    typeCheckOutcome "fn identity(x: &i32) -> &i32 { x } fn f() -> &i32 { let x = 1; identity(&x) }"
      `shouldBe` rejectedWith (EscapingReference (spanAt 1 64))

  test "a reference to a constant may escape through a function result" $
    typeCheckOutcome "const N: i32 = 1; fn identity(x: &i32) -> &i32 { x } fn f() -> &i32 { identity(&N) }"
      `shouldBe` accepted

  test "a return lifetime cannot be elided between two reference parameters" $
    rejected (typeCheckOutcome "fn choose(c: bool, a: &i32, b: &i32) -> &i32 { if c { a } else { b } }")
      `shouldBe` True

-- Modifier blocks need transformation evidence, independently of the callee's
-- declared effect (plan §7.2, §8.2 rule 6).
indirectTransformationTests : List ETest
indirectTransformationTests = Test.do
  test "an opaque unitary callee does not prove an adjoint block transformable" $
    typeCheckOutcome "fn f(g: unitary fn(q: &qbit), q: &qbit) { adjoint { g(q); } }"
      `shouldBe` rejectedWith (UnprovableTransformation "adjoint" (spanAt 1 43))

  test "an opaque unitary callee does not prove a control block transformable" $
    typeCheckOutcome "fn f(g: unitary fn(q: &qbit), c: &qbit, q: &qbit) { ctrl(c) { g(q); } }"
      `shouldBe` rejectedWith (UnprovableTransformation "ctrl" (spanAt 1 53))

  test "a known gate alias supplies transformation evidence inside an adjoint block" $
    typeCheckOutcome "fn f(q: &qbit) { let gate = H; adjoint { gate(q); } }" `shouldBe` accepted

  test "a known gate alias supplies transformation evidence inside a control block" $
    typeCheckOutcome "fn f(c: &qbit, q: &qbit) { let gate = X; ctrl(c) { gate(q); } }" `shouldBe` accepted


export
runOwnershipCheckTests : IO ()
runOwnershipCheckTests =
  runTests $ concat
    [ initializationTests
    , linearityTests
    , partialMoveTests
    , loanTests
    , referenceLifetimeTests
    , cleanupTests
    , transformationTests
    , provenanceAndFlowTests
    , returnedReferenceTests
    , indirectTransformationTests
    ]

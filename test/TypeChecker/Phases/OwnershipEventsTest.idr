module TypeChecker.Phases.OwnershipEventsTest

import Test.Simple

import Compiler.TypeChecker.Data
import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Pass C, part 1: ownership events
--------------------------------------------------------------------------------
-- OwnershipEvents records what each operation does to each place: a read, a
-- copy, a move, a borrow, a write or a consumption (plan §8.1). Recording
-- alone accepts or rejects nothing, so each test observes a classification
-- through the flow analysis that reads it: a copied value can be used again,
-- a moved one cannot, a borrow keeps its place usable, and a temporary that
-- still holds a linear qubit must be consumed. A use after a move points at
-- the use; an unconsumed qubit at the binding or temporary holding it.
--------------------------------------------------------------------------------

-- Copies, moves and borrows (plan §8.1)
copyAndMoveTests : List ETest
copyAndMoveTests = Test.do
  test "a classical value is copied, so it can be used again" $
    typeCheckOutcome "fn f() -> i32 { let x = 5; let y = x; x + y }" `shouldBe` accepted

  test "an owned qubit is moved by the call that consumes it" $
    typeCheckOutcome "fn f() { let q = qalloc(); discard(q); discard(q); }"
      `shouldBe` rejectedWith (UseAfterMove "q" (spanAt 1 48))

  test "a borrowed gate call does not move its qubit" $
    typeCheckOutcome "fn f() -> bit { let q = qalloc(); H(&q); measr(q) }" `shouldBe` accepted

  test "a borrowed measurement keeps its qubit" $
    typeCheckOutcome "fn f() -> bit { let q = qalloc(); let b = measr(&q); discard(q); b }"
      `shouldBe` accepted

  test "an owned measurement consumes its qubit" $
    typeCheckOutcome "fn f() -> bit { let q = qalloc(); let b = measr(q); H(&q); b }"
      `shouldBe` rejectedWith (UseAfterMove "q" (spanAt 1 55))

  test "an owned gate call moves its qubit and returns it" $
    typeCheckOutcome "fn f() -> qbit { let q = qalloc(); let q = H(q); q }" `shouldBe` accepted

  test "len reads an array's length without moving it" $
    typeCheckOutcome "fn f() -> u32 { let qs = qalloc(3); let n = len(qs); discard(qs); n }"
      `shouldBe` accepted

  test "a shared classical reference is copied" $
    typeCheckOutcome "fn f() -> i32 { let x = 5; let r = &x; let s = r; (r + 1) + (s + 1) }"
      `shouldBe` accepted

  test "an exclusive qubit reference is moved, not copied" $
    typeCheckOutcome "fn f(q: &qbit) { let r = q; H(q); H(r); }"
      `shouldBe` rejectedWith (UseAfterMove "q" (spanAt 1 31))

  test "passing a qubit reference to a call reborrows it" $
    typeCheckOutcome "fn g(q: &qbit) { H(q); } fn f(q: &qbit) { g(q); g(q); }" `shouldBe` accepted

  test "an owned qubit cannot be passed twice in one call" $
    typeCheckOutcome "fn f() { let q = qalloc(); let (a, b) = CX(q, q); discard(a, b); }"
      `shouldBe` rejectedWith (UseAfterMove "q" (spanAt 1 47))

-- Temporaries (plan §8.1, §8.2 rule 2)
temporaryTests : List ETest
temporaryTests = Test.do
  test "an unused owned gate result is a live linear temporary" $
    typeCheckOutcome "fn f(q: qbit) { H(q); }"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 17))

  test "an unselected tuple component is a live linear temporary" $
    typeCheckOutcome "fn f(a: qbit, b: qbit) -> qbit { CX(a, b).0 }"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 34))

  test "a wildcard component holds a live linear qubit" $
    typeCheckOutcome "fn f(a: qbit, b: qbit) -> qbit { let (x, _) = CX(a, b); x }"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 42))

  test "a wildcard binding holds a live linear qubit" $
    typeCheckOutcome "fn f() { let _ = qalloc(); }"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 14))

  test "an affine temporary may be dropped" $
    typeCheckOutcome "fn f(q: affine qbit) { H(q); }" `shouldBe` accepted

-- Controls, repetition and iteration (plan §5.6, §8.1)
controlAndRepetitionTests : List ETest
controlAndRepetitionTests = Test.do
  test "owned controls are moved into the call and returned" $
    typeCheckOutcome "fn f(c: qbit, t: qbit) -> (qbit, qbit) { ctrl(c).apply(X)(t) }" `shouldBe` accepted

  test "a borrowed control is reserved for the whole call" $
    typeCheckOutcome "fn f(c: &qbit) { ctrl(c).apply(X)(c); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 35))

  test "a borrowed control conflicts with a write to it inside its block" $
    typeCheckOutcome "fn f(c: &qbit) { ctrl(c) { X(c); } }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 30))

  test "repeating a classical value copies it" $
    typeCheckOutcome "fn f() { let x = 1; let a = [x; 3]; let y = x; }" `shouldBe` accepted

  test "a repeat count of zero drops its operand" $
    typeCheckOutcome "fn f() { let a = [qalloc(); 0]; }"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 19))

  test "a repeat count of one moves its operand" $
    typeCheckOutcome "fn f() { let qs = [qalloc(); 1]; discard(qs); }" `shouldBe` accepted

  test "a for loop over borrowed qubits lends one element at a time" $
    typeCheckOutcome "fn f() { let qs = qalloc(3); for q in &qs { H(q); } discard(qs); }" `shouldBe` accepted

  test "a for loop over an owned array moves its elements" $
    typeCheckOutcome "fn f() { let qs = qalloc(2); for q in qs { discard(q); } }" `shouldBe` accepted

  test "an array iterated by value is moved" $
    typeCheckOutcome "fn f() { let qs = qalloc(2); for q in qs { discard(q); } discard(qs); }"
      `shouldBe` rejectedWith (UseAfterMove "qs" (spanAt 1 66))

-- Moves along control flow (plan §8.2)
moveFlowTests : List ETest
moveFlowTests = Test.do
  test "a move inside a loop body happens again on the next iteration" $
    typeCheckOutcome "fn f() { let q = qalloc(); for i in 0..3 { discard(q); } }"
      `shouldBe` rejectedWith (UseAfterMove "q" (spanAt 1 52))

  test "a move in one branch leaves the qubit possibly moved" $
    typeCheckOutcome "fn f(c: bool) { let q = qalloc(); if c { discard(q); } discard(q); }"
      `shouldBe` rejectedWith (UseAfterMove "q" (spanAt 1 64))

  test "moves in both branches consume the qubit" $
    typeCheckOutcome "fn f(c: bool) -> bit { let q = qalloc(); if c { discard(q); 0 } else { measr(q) } }"
      `shouldBe` accepted

  test "the right side of && may not run" $
    typeCheckOutcome "fn f(c: bool) { let q = qalloc(); let b = c && { discard(q); true }; discard(q); }"
      `shouldBe` rejectedWith (UseAfterMove "q" (spanAt 1 78))

  test "a compound assignment evaluates an indexed target once" $
    typeCheckOutcome "fn f() -> i32 { let mut a = [1, 2]; let q = qalloc(); a[{ discard(q); 0 }] += 1; a[0] }"
      `shouldBe` accepted

  test "a loop can break with an owned qubit" $
    typeCheckOutcome "fn f() { let q = loop { break qalloc(); }; discard(q); }" `shouldBe` accepted

-- Aggregate copies, exclusive references and conditional transfers (plan §8.1–§8.2).
additionalEventTests : List ETest
additionalEventTests = Test.do
  test "an array of classical values is copied as a whole" $
    typeCheckOutcome "fn f() -> i32 { let a = [1, 2]; let b = a; a[0] + b[1] }" `shouldBe` accepted

  test "an exclusive classical reference is moved into a local" $
    typeCheckOutcome "fn f(a: &mut [i32]) { let b = a; a[0] = 1; b[0] = 2; }"
      `shouldBe` rejectedWith (UseAfterMove "a" (spanAt 1 34))

  test "passing a mutable classical reference reborrows it for each call" $
    typeCheckOutcome "fn set(a: &mut [i32]) { a[0] = 1; } fn f(a: &mut [i32]) { set(a); set(a); }" `shouldBe` accepted

  test "an owned barrier transfers its input to its result" $
    typeCheckOutcome "fn f(q: qbit) { let r = barrier(q); discard(q); discard(r); }"
      `shouldBe` rejectedWith (UseAfterMove "q" (spanAt 1 45))

  test "weaken moves the original linear resource" $
    typeCheckOutcome "fn f(q: qbit) { let affine r = weaken(q); discard(q); }"
      `shouldBe` rejectedWith (UseAfterMove "q" (spanAt 1 51))

  test "owned control capture consumes the old control binding" $
    typeCheckOutcome "fn f(c: qbit, q: qbit) { let pair = ctrl(c).apply(X)(q); discard(c); discard(pair.0, pair.1); }"
      `shouldBe` rejectedWith (UseAfterMove "c" (spanAt 1 66))

  test "a zero repeat count permits an affine operand to be dropped" $
    typeCheckOutcome "fn f() { let qs = [weaken(qalloc()); 0]; }" `shouldBe` accepted

  test "a single exclusive reference in a repeat is moved" $
    typeCheckOutcome "fn f(q: &qbit) { let refs = [q; 1]; H(q); H(refs[0]); }"
      `shouldBe` rejectedWith (UseAfterMove "q" (spanAt 1 39))

  test "the right side of || may not run" $
    typeCheckOutcome "fn f(c: bool) { let q = qalloc(); let b = c || { discard(q); false }; discard(q); }"
      `shouldBe` rejectedWith (UseAfterMove "q" (spanAt 1 79))

  test "a branch that returns does not make the continuing branch use a moved qubit" $
    typeCheckOutcome "fn f(c: bool) -> bit { let q = qalloc(); if c { return measr(q); } measr(q) }" `shouldBe` accepted

-- Early exits retain obligations for elements still owned by the iterator
-- (plan §8.1, §8.2). Temporary arrays have no local binding to report instead.
iterationExitTests : List ETest
iterationExitTests = Test.do
  test "breaking from owned iteration leaves the remaining linear elements live" $
    typeCheckOutcome "fn f() { for q in qalloc(2) { discard(q); break; } }"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 19))

  test "returning from owned iteration leaves the remaining linear elements live" $
    typeCheckOutcome "fn f() { for q in qalloc(2) { discard(q); return; } }"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 19))

  test "breaking after consuming the sole owned element leaves no linear remainder" $
    typeCheckOutcome "fn f() { for q in qalloc(1) { discard(q); break; } }" `shouldBe` accepted

  test "returning after consuming the sole owned element leaves no linear remainder" $
    typeCheckOutcome "fn f() { for q in qalloc(1) { discard(q); return; } }" `shouldBe` accepted

  test "breaking from owned iteration may discard remaining affine elements" $
    typeCheckOutcome "fn f() { for q in weaken(qalloc(2)) { discard(q); break; } }" `shouldBe` accepted

  test "returning from owned iteration may discard remaining affine elements" $
    typeCheckOutcome "fn f() { for q in weaken(qalloc(2)) { discard(q); return; } }" `shouldBe` accepted

  test "continue advances owned iteration until every linear element is consumed" $
    typeCheckOutcome "fn f() { for q in qalloc(2) { discard(q); continue; } }" `shouldBe` accepted

  test "breaking from borrowed iteration leaves the original array available" $
    typeCheckOutcome "fn f() { let qs = qalloc(2); for q in &qs { H(q); break; } discard(qs); }" `shouldBe` accepted


-- Repetition evaluates its operand once and copies it (plan §5.6, §8.2). Owned
-- qubits and exclusive references are not Copy, and the plan names no
-- diagnostic for duplicating them, so those tests require only a reported error.
repetitionCopyTests : List ETest
repetitionCopyTests = Test.do
  test "repeating a linear qubit more than once is rejected" $
    rejected (typeCheckOutcome "fn f() { let qs = [qalloc(); 2]; discard(qs); }")
      `shouldBe` True

  test "repeating an affine qubit more than once is rejected" $
    rejected (typeCheckOutcome "fn f() { let qs = [weaken(qalloc()); 2]; }")
      `shouldBe` True

  test "repeating a qubit reference more than once is rejected" $
    rejected (typeCheckOutcome "fn f(q: &qbit) { let rs = [q; 2]; }")
      `shouldBe` True

  test "repeating a mutable classical reference more than once is rejected" $
    rejected (typeCheckOutcome "fn f() { let mut x = 1; let rs = [&mut x; 2]; }")
      `shouldBe` True

  test "repeating a shared classical reference copies it" $
    typeCheckOutcome "fn f() -> i32 { let x = 1; let rs = [&x; 2]; rs[0] + rs[1] }" `shouldBe` accepted

export
runOwnershipEventsTests : IO ()
runOwnershipEventsTests =
  runTests $ concat
    [ copyAndMoveTests
    , temporaryTests
    , controlAndRepetitionTests
    , moveFlowTests
    , additionalEventTests
    , iterationExitTests
    , repetitionCopyTests
    ]

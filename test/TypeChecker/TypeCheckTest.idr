module TypeChecker.TypeCheckTest

import System.File
import Test.Simple

import Compiler.TypeChecker.Data
import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Type checker integration tests
--------------------------------------------------------------------------------
-- Whole programs through every phase (plan §9 items 1 and 4): the examples in
-- `examples/`, read at run time, and the in-scope sections of the language
-- specification, each placed in the smallest context that declares what it
-- uses. Example 08 is excluded: the parser rejects its qmatch. Spec snippets
-- that the parser or post-parse validation rejects are left to those phases.
--------------------------------------------------------------------------------

||| Spec §5: every primitive type except qstate.
primitiveTypesProgram : String
primitiveTypesProgram = """
  fn primitive_types(
      b: bit, q: qbit, a32: angle32, a64: angle64, p: param,
      i1: i8, i2: i16, i3: i32, i4: i64, i5: i128,
      u1: u8, u2: u16, u3: u32, u4: u64, u5: u128,
      f1: f32, f2: f64, flag: bool, unit: ()
  ) {
      discard(q);
  }
  """

||| Spec §6: primitive types, literals, mutation, references and casts.
basicTypesProgram : String
basicTypesProgram = """
  fn basic_types() {
      let f: f32 = 1.234567;
      let d: f64 = -1.2345678901234567;
      let d = -1000.0;
      let i: i8 = -1;
      let i: i16 = -1;
      let i: i32 = 1;
      let i: i64 = 1;
      let i: i128 = -1;
      let i = -7;
      let u: u8 = 1;
      let u: u16 = 1;
      let u: u32 = 1;
      let u: u64 = 1;
      let u: u128 = 1;
      let unit: () = ();
      let unit = ();
      let theta: param = Param("theta");
      let mut x: i32 = 0;
      x = 5;
      let mut x: [i32; 2] = [0, 0];
      x[0] = 10;
      let mut t: (i32, f64) = (0, 0.0);
      t.0 = 3;
      let x = 10;
      let r: &i32 = &x;
      let mut x = 10;
      let r: &mut i32 = &mut x;
  }
  const FIVE: i32 = 5;
  fn qubit_declarations() {
      let q: qbit = qalloc();
      discard(q);
      let q: linear qbit = qalloc();
      discard(q);
      let linear q: qbit = qalloc();
      discard(q);
      let q = qalloc();
      discard(q);
  }
  fn casts() {
      let x: i8 = 34;
      let x = 34 as i8;
      let x: i16 = 34;
      let x = 34 as i16;
      let x: i32 = 34;
      let x = 34 as i32;
      let x: i64 = 34;
      let x = 34 as i64;
      let x: i128 = 34;
      let x = 34 as i128;
      let x: u8 = 34;
      let x = 34 as u8;
      let x: u16 = 34;
      let x = 34 as u16;
      let x: u32 = 34;
      let x = 34 as u32;
      let x: u64 = 34;
      let x = 34 as u64;
      let x: u128 = 34;
      let x = 34 as u128;
      let x: f32 = 34.0;
      let x = 34 as f32;
      let x: f64 = 34.0;
      let x = 34 as f64;
      let x: angle32 = 34.0;
      let x = 34 as angle32;
      let x: angle64 = 34.0;
      let x = 34 as angle64;
      let b: bit = 1;
      let x = b as i32;
  }
  """

||| Spec §7 and §8: arrays, lengths and len.
arraysProgram : String
arraysProgram = """
  const N: u64 = 4;
  fn arrays() {
      let bs: [bool; 4] = [true, false, true, false];
      let is: [i32; 3] = [1, 2, 3];
      let us: [u64; 2] = [10, 20];
      let fs: [f64; 3] = [1.0, 2.0, 3.0];
      let bits: [bit; 3] = [1, 0, 1];
      let angles: [angle64; 2] = [3.14, 1.57];
      let units: [(); 5] = [(), (), (), (), ()];
      let params: [param; 2] = [Param("theta"), Param("phi")];
      let qbits: [qbit; 2] = qalloc(2);
      discard(qbits);
      let linear qbits: [qbit; 2] = qalloc(2);
      discard(qbits);
      let affine qbits: [qbit; 2] = qalloc(2);
      let a: [i32; 4];
      let b: [i32; 2 + 2];
      let c: [i32; N];
      let d: [i32; 4u32];
      let bools = [true, false, true, false];
      let ints = [1, 2, 3];
      let zeros = [0; 3];
      let fs = [1.0, 2.0, 3.0];
      let qbits = qalloc(2);
      discard(qbits);
      let units = [(), (), (), (), ()];
  }
  fn member_access() -> u32 {
      let a = [1, 2, 3];
      let first = a[0];
      let n = len(a);
      n
  }
  """

||| Spec §9: slices, mutable slices, qubit slices and array-to-slice coercion.
slicesProgram : String
slicesProgram = """
  classical fn sum(xs: &[i32]) -> i32 {
      let mut total = 0;
      for i in 0..len(xs) {
          total += xs[i];
      }
      total
  }
  classical fn zero_out(xs: &mut [i32]) {
      for i in 0..len(xs) {
          xs[i] = 0;
      }
  }
  unitary fn apply_hadamard_layer(qs: &[qbit]) {
      if len(qs) == 0 {
          return;
      }
      H(&qs[0]);
      apply_hadamard_layer(&qs[1..]);
  }
  fn slices() -> i32 {
      let a: [i32; 5] = [10, 20, 30, 40, 50];
      let s: &[i32] = &a[..];
      let s: &[i32] = &a[1..4];
      let s: &[i32] = &a[1..=3];
      let s: &[i32] = &a[2..];
      let s: &[i32] = &a[..3];
      let s: &[i32] = &a[..=3];
      let s = &a[1..4];
      let n = len(s);
      let x = s[0];
      let mid: &[i32] = &s[1..n - 1];
      let mut m: [i32; 5] = [10, 20, 30, 40, 50];
      let w: &mut [i32] = &mut m[1..4];
      w[0] = 99;
      let r: &[i32] = &m[..];
      zero_out(&mut m);
      let qs: [qbit; 4] = qalloc(4);
      let qv: &[qbit] = &qs[..];
      H(&qv[0]);
      CX(&qv[1], &qv[2]);
      apply_hadamard_layer(&qs);
      discard(qs);
      sum(&a) + x
  }
  """

||| Spec §9: `&mut` is never written on qubits.
mutableQubitSliceProgram : String
mutableQubitSliceProgram = """
  fn f() {
      let qs: [qbit; 4] = qalloc(4);
      let bad = &mut qs[..];
      discard(qs);
  }
  """

||| Spec §9: a shared slice cannot be written through.
sharedSliceWriteProgram : String
sharedSliceWriteProgram = """
  fn f() {
      let mut m: [i32; 5] = [10, 20, 30, 40, 50];
      let r: &[i32] = &m[..];
      r[0] = 0;
  }
  """

||| Spec §10 and §12: allocation, measurement and qubit qualifiers.
qubitsProgram : String
qubitsProgram = """
  fn allocation_and_measurement() -> bit {
      let q: qbit = qalloc();
      let q2: linear qbit = qalloc();
      let linear q3: qbit = qalloc();
      let qs: [qbit; 1] = qalloc(1);
      let rs: [qbit; 3] = qalloc(3);
      let b: bit = measr(q);
      let b: bit = 0;
      let bs: [bit; 3] = measr(rs);
      let q = qalloc();
      let qs3 = qalloc(3);
      let b = measr(&q);
      let b = measr(q);
      discard(q2);
      discard(q3);
      discard(qs);
      discard(qs3);
      b
  }
  fn qualifiers() {
      let linear q: qbit = qalloc();
      let linear qs: [qbit; 2] = qalloc(2);
      let q2: linear qbit = qalloc();
      let qs2: [linear qbit; 2] = qalloc(2);
      let affine a: qbit = qalloc();
      let affine aqs: [qbit; 2] = qalloc(2);
      let a2: affine qbit = qalloc();
      let aqs2: [affine qbit; 2] = qalloc(2);
      let p: (affine qbit, affine qbit) = (qalloc(), qalloc());
      let r: &qbit = &q;
      let v: &[qbit] = &qs[..];
      discard(q);
      discard(qs);
      discard(q2);
      discard(qs2);
  }
  fn scratch_qubits() {
      let scratch q: qbit = qalloc();
      let scratch qs: [qbit; 2] = qalloc(2);
      let scratch linear q1: qbit = qalloc();
      let scratch q2: linear qbit = qalloc();
      let linear scratch qs3: [qbit; 2] = qalloc(2);
      let scratch affine q4: qbit = qalloc();
      let affine scratch q5: qbit = qalloc();
      let scratch q6: affine qbit = qalloc();
  }
  fn applyHadamard(q: linear qbit) -> linear qbit {
      H(q)
  }
  """

||| Spec §10: a qubit consumed by measr cannot be used after the measurement.
measuredQubitProgram : String
measuredQubitProgram = """
  fn f() -> bit {
      let q = qalloc();
      let b = measr(q);
      H(&q);
      b
  }
  """

||| Spec §13 and §14: owned and borrowed gate calls and angle arguments.
gatesProgram : String
gatesProgram = """
  fn gates() -> (qbit, qbit) {
      let q = qalloc();
      let q: qbit = H(q);
      let linear q: qbit = H(q);
      let q: linear qbit = H(q);
      let q = H(q);
      H(&q);
      let q: qbit = U3(1.0, 2.0, 3.0, q);
      let q = U3(1.0, 2.0, 3.0, q);
      U3(1.0, 2.0, 3.0, &q);
      let q0 = qalloc();
      let q1 = qalloc();
      let (q0, q1): (qbit, qbit) = CX(q0, q1);
      let (q0, q1) = CX(q0, q1);
      CX(&q0, &q1);
      let q: qbit = U1(0.25, q);
      let angle: angle64 = 3.141592653589793;
      let q: qbit = U1(angle, q);
      let angle: angle64 = turns(0.25);
      let q: qbit = U1(angle, q);
      let theta = Param("theta");
      let q: qbit = U1(theta, q);
      let q: qbit = U1(turns(0.25), q);
      discard(q);
      (q0, q1)
  }
  """

||| Spec §15: ctrl over gates, as a callable and as a block, with and without a selector.
controlledGatesProgram : String
controlledGatesProgram = """
  fn controlled_gates() {
      let q0 = qalloc();
      let q1 = qalloc();
      let q2 = qalloc();
      let (q0, q1, q2): (qbit, qbit, qbit) = ctrl(q0, q1).apply(H)(q2);
      let (q0, q1, q2) = ctrl(q0, q1).apply(H)(q2);
      ctrl(&q0, &q1).apply(H)(&q2);
      ctrl(&q0, &q1) {
          H(&q2);
      }
      let (q0, q1, q2) = ctrl(q0, q1).on(bs"10").apply(H)(q2);
      ctrl(&q0, &q1).on(bs"10").apply(H)(&q2);
      ctrl(&q0, &q1).on(bs"10") {
          H(&q2);
      }
      discard(q0, q1, q2);
  }
  """

||| Spec §15: control blocks over a user function. The spec's `f` takes owned qubits in
||| the callable form and references in the block form; here it takes references.
controlledBlocksProgram : String
controlledBlocksProgram = """
  unitary fn f(a: &qbit, b: &qbit) {
      CX(a, b);
  }
  fn controlled_blocks() {
      let q0 = qalloc();
      let q1 = qalloc();
      let q2 = qalloc();
      let q3 = qalloc();
      ctrl(&q0, &q1) {
          f(&q2, &q3);
      }
      ctrl(&q0, &q1).on(bs"++") {
          f(&q2, &q3);
      }
      discard(q0, q1, q2, q3);
  }
  """

||| Spec §15: ctrl applied to a user function as a callable.
controlledCallableProgram : String
controlledCallableProgram = """
  unitary fn f(a: &qbit, b: &qbit) {
      CX(a, b);
  }
  fn controlled_callable() {
      let q0 = qalloc();
      let q1 = qalloc();
      let q2 = qalloc();
      let q3 = qalloc();
      ctrl(&q0, &q1).apply(f)(&q2, &q3);
      discard(q0, q1, q2, q3);
  }
  """

||| Spec §16: adjoint of gates and adjoint blocks.
adjointsProgram : String
adjointsProgram = """
  unitary fn f(a: &qbit, b: &qbit, c: &qbit) {
      CCX(a, b, c);
  }
  fn adjoints() {
      let q1 = qalloc();
      let q2 = qalloc();
      let q3 = qalloc();
      adjoint {
          f(&q1, &q2, &q3);
      }
      adjoint {
          H(&q1);
          CT(&q1, &q2)
      }
      adjoint(CT)(&q1, &q2);
      adjoint(H)(&q1);
      discard(q1, q2, q3);
  }
  """

||| Spec §16: adjoint applied to a user function as a callable.
adjointCallableProgram : String
adjointCallableProgram = """
  unitary fn f(a: &qbit, b: &qbit, c: &qbit) {
      CCX(a, b, c);
  }
  fn adjoint_callable() {
      let f_adjoint = adjoint(f);
  }
  """

||| Spec §17 to §19: arithmetic, boolean and bitwise operators. The spec reuses `a`
||| for bits and integers; here bits and integers have their own names.
operatorsProgram : String
operatorsProgram = """
  fn operators(a: bool, b: bool, p: bit, q: bit, y: u32) {
      let add = 5 + 3;
      let sub = 10 - 4;
      let mul = 6 * 2;
      let div = 12 / 3;
      let rem = 10 % 3;
      let mut x = 10;
      x += 5;
      x -= 2;
      x *= 2;
      x /= 3;
      x %= 4;
      let c = !a;
      let d = a && b;
      let e = a || b;
      let and_bit: bit = p & q;
      let or_bit: bit = p | q;
      let xor_bit: bit = p ^ q;
      let mut z: u32 = 12;
      z &= y;
      z |= y;
      z ^= y;
      let l = z << 2;
      let r = z >> 1;
      z <<= 1;
      z >>= 1;
  }
  """

||| Spec §20 and §36: if and else with bool and bit conditions.
conditionalsProgram : String
conditionalsProgram = """
  fn f1() -> i32 {
      -1
  }
  fn f2() -> i32 {
      0
  }
  fn f3() -> i32 {
      1
  }
  fn fun(q: &qbit) {
      X(q);
  }
  fn conditionals(x: i32, b: bit) -> i32 {
      let q = qalloc();
      if 7 > 5 {
          H(&q);
      } else {
          X(&q);
      }
      if b { fun(&q); }
      if b == 1 { fun(&q); }
      let sign = if x < 0 {
          f1()
      } else if x == 0 {
          f2()
      } else {
          f3()
      };
      discard(q);
      let boolflag = true;
      let y: i32 = if boolflag { 1 } else { 2 };
      if x < 0 {
          -1
      } else if x == 0 {
          0
      } else {
          1
      }
  }
  """

||| Spec §27 to §35: blocks, loops, ranges, for loops and tuples.
blocksAndLoopsProgram : String
blocksAndLoopsProgram = """
  fn blocks_and_loops(xs: [i32; 3]) -> i32 {
      let x = {
          let a = 1;
          let b = 2;
          a + b
      };
      let unit = {
          let a = 1;
      };
      let mut count = 0;
      loop {
          if count == 3 {
              break;
          }
          count += 1;
      }
      let mut count = 0;
      let result = loop {
          if count == 3 {
              break count;
          }
          count += 1;
      };
      while count <= 5 {
          count += 1;
      }
      for i in 1..6 {
          count += 1;
      }
      for i in rev(1..6) {
          count -= 1;
      }
      for i in 0..len(xs) {
          count += xs[i];
      }
      let t: (i32, f64, bool) = (1, 3.14, true);
      let t = (1, 3.14, true);
      let x0 = t.0;
      let y0 = t.1;
      let z0 = t.2;
      let (a, b, c) = (1, 2, 3);
      let (p, _, r) = (1, 2, 3);
      x + result + count
  }
  fn ranges(a: i32, b: i32, n: u32) {
      let r1 = a..b;
      let r2 = a..=b;
      let r3 = 1..;
      let r4 = ..5;
      let r5 = ..=5;
      let r6 = rev(0..n);
  }
  fn tuple_qubits() -> (qbit, qbit, qbit) {
      let q0 = qalloc();
      let q1 = qalloc();
      let q2 = qalloc();
      let qbits = CNOT(q0, q1);
      let q0 = qbits.0;
      let q1 = qbits.1;
      let (q0, q1, q2) = (H(q0), H(q1), H(q2));
      (q0, q1, q2)
  }
  """

||| Spec §31: rev needs a range with both endpoints.
reversedOpenRangeProgram : String
reversedOpenRangeProgram = """
  fn reversed() {
      for i in rev(..6) {
      }
  }
  """

||| Spec §38 to §44: reset, discard, uncompute, weaken, measr and barrier.
builtinsProgram : String
builtinsProgram = """
  fn resets() {
      let q: qbit = qalloc();
      let q = reset(q);
      reset(&q);
      let qs: [qbit; 3] = qalloc(3);
      let qs = reset(qs);
      reset(&qs);
      let q1 = qalloc();
      let q2 = qalloc();
      let q3 = qalloc();
      let (q1, q2, q3): (qbit, qbit, qbit) = reset(q1, q2, q3);
      let (q1, q2, q3) = reset(q1, q2, q3);
      discard(q);
      discard(qs);
      discard(q1, q2, q3);
  }
  fn discards() {
      let q: qbit = qalloc();
      discard(q);
      let q1: qbit = qalloc();
      let q2: qbit = qalloc();
      discard(q1, q2);
      let qs: [qbit; 3] = qalloc(3);
      discard(qs);
  }
  fn uncomputation() {
      let q: qbit = X(qalloc());
      let q = uncompute(q);
      let r: qbit = X(qalloc());
      uncompute(&r);
      let qs: [qbit; 3] = qalloc(3);
      X(&qs[0]);
      let qs = uncompute(qs);
      discard(q);
      discard(r);
      discard(qs);
  }
  fn weakening() {
      let linear q: qbit = qalloc();
      let affine q = weaken(q);
      let linear qs: [qbit; 3] = qalloc(3);
      let affine qs = weaken(qs);
      let q1 = qalloc();
      let q2 = qalloc();
      let q3 = qalloc();
      let affine (q1, q2, q3): (qbit, qbit, qbit) = weaken(q1, q2, q3);
  }
  fn measurements() -> [bit; 3] {
      let q: qbit = qalloc();
      let b: bit = measr(&q);
      let b: bit = measr(q);
      let q1 = qalloc();
      let q2 = qalloc();
      let q3 = qalloc();
      let (b1, b2, b3): (bit, bit, bit) = measr(q1, q2, q3);
      let qs: [qbit; 3] = qalloc(3);
      let bs: [bit; 3] = measr(&qs);
      let [b0, b1, b2]: [bit; 3] = measr(qs);
      [b0, b1, b2]
  }
  fn barriers() {
      barrier();
      let q0 = qalloc();
      let q1 = qalloc();
      let q2 = qalloc();
      let (q0, q1, q2) = barrier(q0, q1, q2);
      barrier(&q0, &q1);
      let qs = qalloc(2);
      let qs = barrier(qs);
      barrier(&qs);
      discard(q0, q1, q2);
      discard(qs);
  }
  """

||| Spec §46 to §50 and §52: functions, const fns, returns and local scopes.
functionsProgram : String
functionsProgram = """
  fn function_name() {
  }
  const fn square(x: i32) -> i32 {
      x * x
  }
  fn add(x: i32, y: i32) -> i32 {
      x + y
  }
  fn f(x: f32) -> f32 {
      let y = 2.0;
      x + y
  }
  fn g() -> f64 {
      let x = 2.0;
      return x;
  }
  fn my_function() {
      let i = 10;
  }
  fn increment(mut x: i32) -> i32 {
      x += 1;
      x
  }
  fn local_block() {
      {
          let mut x = 0;
          x = x + 1;
      }
  }
  """

||| Spec §53: the effect qualifiers, except the contract-bearing coisometry.
effectsProgram : String
effectsProgram = """
  classical fn f(x: i32) -> i32 {
      x + 1
  }
  uncompsafe fn g(q: qbit) -> qbit {
      let q = X(q);
      q
  }
  unitary fn h(q: qbit) -> qbit {
      let q = X(q);
      let q = H(q);
      q
  }
  isometry fn grow(qs: [qbit; 2]) -> [qbit; 4] {
      let q1 = X(qs[0]);
      let q2 = H(qs[1]);
      let q3 = qalloc();
      let q4 = qalloc();
      let q3 = X(q3);
      let (q3, q4) = CX(q3, q4);
      [q1, q2, q3, q4]
  }
  general fn sample(q: qbit) -> bit {
      measr(q)
  }
  """

||| Spec §54 and §55: integer and floating-point literals.
literalsProgram : String
literalsProgram = """
  fn integer_literals() {
      let x = 1000;
      let x = 1_000;
      let x = 1_000_000;
      let h = 0xff;
      let h = 0xFF;
      let h = 0xff_u8;
      let o = 0o77;
      let o = 0o70_i16;
      let b = 0b1010;
      let b = 0b1111_0000;
      let b = 0b1111_1111_1001_0000i64;
      let z = 10u32;
      let z = 10_u32;
      let z = 123i32;
      let z = 123_i32;
  }
  fn float_literals() {
      let x = 1.0;
      let x = 0.1;
      let x = 1.0e-3;
      let x = 12E+99;
      let x = 12E+99_f64;
      let f = 1.0f64;
      let f = 1.0_f64;
      let f = 0.1f32;
      let f = 5f32;
  }
  """

||| Spec §61, with the `prepare_minus` it calls. The scratch ancilla's history
||| includes H and an opaque oracle, so its cleanup cannot be proved (plan §8.3,
||| §11.2); which check reports it first is not fixed.
phaseKickbackProgram : String
phaseKickbackProgram = """
  unitary fn prepare_minus(q: qbit) -> qbit {
      let q = X(q);
      H(q)
  }
  general fn phase_kickback(
      qs: [qbit; 4],
      oracle: unitary fn(qs: [qbit; 4], target: qbit) -> ([qbit; 4], qbit)
  ) -> [qbit; 4] {
      let scratch ancilla = qalloc();
      let ancilla = prepare_minus(ancilla);
      let (qs, ancilla) = oracle(qs, ancilla);
      qs
  }
  """

||| Spec §66: a qubit reference argument.
referenceArgumentsProgram : String
referenceArgumentsProgram = """
  fn apply_gate(q: &qbit)
  {
    H(q);
  }
  fn main() -> bit {
    let q = qalloc();
    apply_gate(&q);
    let b = measr(q);
    b
  }
  """

||| Spec §67: a function and a constant item. The constant `I` shadows the
||| prelude gate of the same name.
itemsProgram : String
itemsProgram = """
  fn main() {
  }
  const I: i32 = 1;
  fn uses_constant() -> i32 {
      I
  }
  """

||| Spec §68: qasm_gate and qasm_def, with distinct function names.
attributesProgram : String
attributesProgram = """
  #[qasm_gate]
  unitary fn myfun1(q: qbit) -> qbit {
    let q = X(q);
    let q = H(q);
    q
  }
  #[qasm_gate("qasm_subroutine_name")]
  unitary fn myfun2(q: qbit) -> qbit {
    let q = X(q);
    let q = H(q);
    q
  }
  #[qasm_def]
  general fn myfun3(q: qbit) -> bit {
    let q = X(q);
    let q = H(q);
    measr(q)
  }
  #[qasm_def("qasm_subroutine_name")]
  general fn myfun4(q: qbit) -> bit {
    let q = X(q);
    let q = H(q);
    measr(q)
  }
  """

||| Spec §69: classical, circuit-generating and classically controlled recursion.
recursionProgram : String
recursionProgram = """
  classical fn fact(n: u32) -> u32 {
      if n == 0 { 1 } else { n * fact(n - 1) }
  }
  unitary fn apply_hadamard_layer(qs: &[qbit]) {
      if len(qs) == 0 {
          return;
      }
      H(&qs[0]);
      apply_hadamard_layer(&qs[1..]);
  }
  general fn sample_until_zero() -> qbit {
      let q = qalloc();
      H(&q);
      let b = measr(&q);
      if b == 0 {
          return q;
      } else {
          discard(q);
          sample_until_zero()
      }
  }
  """

-- Language specification sections (plan §1.4, §9 item 4)
specificationTests : List ETest
specificationTests = Test.do
  test "spec §5 every primitive type except qstate type-checks" $
    typeCheckOutcome primitiveTypesProgram `shouldBe` accepted

  test "spec §6 basic types, mutation, references and casts type-check" $
    typeCheckOutcome basicTypesProgram `shouldBe` accepted

  test "spec §7 and §8 arrays and len type-check" $
    typeCheckOutcome arraysProgram `shouldBe` accepted

  test "spec §9 slices and array-to-slice coercion type-check" $
    typeCheckOutcome slicesProgram `shouldBe` accepted

  test "spec §9 rejects &mut on qubits" $
    typeCheckOutcome mutableQubitSliceProgram
      `shouldBe` rejectedWith (InvalidQbitReference (spanAt 3 15))

  test "spec §9 rejects writes through a shared slice" $
    typeCheckOutcome sharedSliceWriteProgram
      `shouldBe` rejectedWith (AssignmentThroughSharedReference (spanAt 4 5))

  test "spec §10 and §12 qubit allocation, measurement and qualifiers type-check" $
    typeCheckOutcome qubitsProgram `shouldBe` accepted

  test "spec §10 rejects a qubit used after measr consumed it" $
    typeCheckOutcome measuredQubitProgram
      `shouldBe` rejectedWith (UseAfterMove "q" (spanAt 4 7))

  test "spec §13 and §14 gate calls type-check" $
    typeCheckOutcome gatesProgram `shouldBe` accepted

  test "spec §15 controlled gates type-check" $
    typeCheckOutcome controlledGatesProgram `shouldBe` accepted

  test "spec §15 control blocks over a user function type-check" $
    typeCheckOutcome controlledBlocksProgram `shouldBe` accepted

  test "spec §15 rejects ctrl applied to a user function without ctrl support" $
    typeCheckOutcome controlledCallableProgram
      `shouldBe` rejectedWith (MissingCapability "ctrl" (spanAt 9 26))

  test "spec §16 adjoints of gates and adjoint blocks type-check" $
    typeCheckOutcome adjointsProgram `shouldBe` accepted

  test "spec §16 rejects adjoint applied to a user function without adjoint support" $
    typeCheckOutcome adjointCallableProgram
      `shouldBe` rejectedWith (MissingCapability "adjoint" (spanAt 5 29))

  test "spec §17 to §19 operators type-check" $
    typeCheckOutcome operatorsProgram `shouldBe` accepted

  test "spec §20 and §36 conditionals type-check" $
    typeCheckOutcome conditionalsProgram `shouldBe` accepted

  test "spec §27 to §35 blocks, loops, ranges and tuples type-check" $
    typeCheckOutcome blocksAndLoopsProgram `shouldBe` accepted

  test "spec §31 rejects rev of a range without a start" $
    typeCheckOutcome reversedOpenRangeProgram
      `shouldBe` rejectedWith (MissingRangeEndpoint "rev" (spanAt 2 14))

  test "spec §38 to §44 qubit builtins type-check" $
    typeCheckOutcome builtinsProgram `shouldBe` accepted

  test "spec §46 to §52 functions type-check" $
    typeCheckOutcome functionsProgram `shouldBe` accepted

  test "spec §53 effect qualifiers type-check" $
    typeCheckOutcome effectsProgram `shouldBe` accepted

  test "spec §54 and §55 integer and floating-point literals type-check" $
    typeCheckOutcome literalsProgram `shouldBe` accepted

  test "spec §61 rejects a scratch ancilla whose cleanup crosses an opaque oracle" $
    rejected (typeCheckOutcome phaseKickbackProgram)
      `shouldBe` True

  test "spec §66 qubit reference arguments type-check" $
    typeCheckOutcome referenceArgumentsProgram `shouldBe` accepted

  test "spec §67 a function and a constant shadowing the gate I type-check" $
    typeCheckOutcome itemsProgram `shouldBe` accepted

  test "spec §68 attributes type-check" $
    typeCheckOutcome attributesProgram `shouldBe` accepted

  test "spec §69 recursion type-checks" $
    typeCheckOutcome recursionProgram `shouldBe` accepted

||| Every example the parser accepts, each with its test name.
examples : List (String, String)
examples =
  [ ("01_coin_flip.rs", "example 01, a coin flip, type-checks")
  , ("02_phase_kickback.rs", "example 02, phase kickback, type-checks")
  , ("03_deutsch.rs", "example 03, Deutsch's algorithm, type-checks")
  , ("04_deutsch_jozsa.rs", "example 04, Deutsch-Jozsa, type-checks")
  , ("05_deutsch_jozsa_compact_syntax.rs", "example 05, compact Deutsch-Jozsa with indexed qubits, type-checks")
  , ("06_deutsch_jozsa_even_more_compact_syntax.rs", "example 06, Deutsch-Jozsa with borrowed iteration, type-checks")
  , ("07_deutsch_jozsa_emphasizing_phase_kickback.rs", "example 07, Deutsch-Jozsa with an oracle argument, type-checks")
  , ("09_bernstein_vazirani.rs", "example 09, Bernstein-Vazirani, type-checks")
  , ("10_simons.rs", "example 10, Simon's algorithm, type-checks")
  , ("11_grover.rs", "example 11, Grover's search, type-checks")
  ]

-- The examples are read from `examples/`, relative to where the tests run.
covering
exampleOutcome : (String, String) -> IO (String, Either String ())
exampleOutcome (fileName, testName) = do
  Right source <- readFile ("examples/" ++ fileName)
    | Left err => pure (testName, Left ("Failed to read examples/" ++ fileName ++ ": " ++ show err))
  pure (testName, typeCheckOutcome source)

exampleTests : List (String, Either String ()) -> List ETest
exampleTests = concatMap (\(testName, outcome) => test testName (outcome `shouldBe` accepted))

export covering
runTypeCheckTests : IO ()
runTypeCheckTests = do
  outcomes <- traverse exampleOutcome examples
  runTests (exampleTests outcomes ++ specificationTests)

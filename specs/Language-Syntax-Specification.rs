//////////////////////////////////////
// Leaf Language Syntax Specification
//////////////////////////////////////

// Leaf is deliberately designed to replicate Rust’s basic syntax, with minimal extensions for quantum programming which are meant to look and feel like Rust.

///////////////////////////////////////////////////////////////////////////////////////////////////////////////
// (1) Comments syntax for the Leaf language follows the same syntax as Rust, including nested block comments:
///////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // single line comment

  /*
     multi-line comment
  */

  /*
    This is an outer block comment.

    /*
        This is a nested block comment.
        Leaf allows this.
    */

    Back in the outer comment.
  */

  /// Documentation comment for a function, struct, or module. Leaf supports Rust-style documentation comments.

  /** Documentation comment. */

  //! Documentation comment.

  /*! Documentation comment. */

///////////////////////////////////
// (2) Basic Leaf Language Syntax
///////////////////////////////////

// Leaf follows Rust-style semicolon rules:
// most statements end with ';', while the final expression of a block or function body
// may omit ';' when its value is returned by that block or function.

// Parentheses, square brackets and curly braces follow the same rules from Rust.

/////////////////////////////////////////////////////////////////////////////////////
// (3) Reserved Keywords + Built-in Identifiers + Literals for Leaf Language Syntax:
/////////////////////////////////////////////////////////////////////////////////////

// reserved boolean literals, belong to language syntax and should be parsed such
false
true

// reserved quantum state literals, belong to language syntax and should be parsed such
one
zero
minus
minusi
plus
plusi

// Leaf Keywords, belong to language syntax and should be parsed as keywords:
adjoint
affine
as
break
classical
coisometry
const
continue
else
ensures
enum
fn
for
general
if
impl
in
isometry
let
linear
loop
match
mod
mut
pub
qif
qelse
qenum
qmatch
requires
return
scratch
self
selse
sif
smatch
struct
supports
then
unitary
uncompsafe
use
while

// keyword usable as both a higher-order operator and a block operator:
// CANNOT be shadowed by a local declaration, belong to language syntax and should be parsed as a keyword:
adjoint()
adjoint {
    // block of code
}

// Leaf Reserved Built-in Functions, built-in Functions CANNOT be shadowed by a local declaration, belong to language syntax and should be parsed as built-in functions:
barrier()
ctrl().on().apply()
basis()
clean()
discard()
isolated()
measr()
product()
qalloc()
reset()
tensor()
separable()
stabilized()
uncompute()
weaken()

// Leaf Prelude Functions, prelude functions CAN be shadowed by a local declaration and should be parsed as regular functions, NOT keywords or built-in functions:
abs()
acos()
asin()
atan()
ceil()
cos()
exp()
floor()
ln()
log2()
log10()
max()
min()
Param()
phase()
round()
sin()
sqrt()
tan()
turns()


// (I) The following are built-in identifiers that can be used in Leaf programs which ARE part of language syntax and should be parsed as keywords or built-in functions:

// Quantum contracts
clean(), basis(), isolated(), product(), separable(), stabilized()
// Circuit operations
barrier()
// Adjoint operations
adjoint()
// Control operations
ctrl().on().apply()

// (II) The following are prelude mathematical functions that can be used in Leaf programs. These are NOT part of language syntax, they should be parsed as regular functions:
cos(), acos(), sin(), asin(), tan(), atan()
abs(), exp(), ceil(), floor(), ln(), log2(), log10(), max(), min(), round(), sqrt()
// Declaring angle parameters, part of prelude:
Param()
// phase() is a complex-valued helper function part of prelude needed for quantum states specification: phase(1.23) = exp(i * 1.23)
phase()
// turns() part of prelude translates floating point numbers representing fractions of 2π into angle types, so turns(0.25) = π/2, turns(0.5) = π, turns(1.0) = 2π, etc.
turns()

//////////////////////////////////////////////////////////////
// (4) Reserved delimiters, punctuation, and operator tokens:
//////////////////////////////////////////////////////////////

'(', ')', '[', ']', '{', '}', ',', ';', ':', '::', '.', '->', '=', ':=', '+=', '-=', '*=', '/=', '%=', '+', '-', '*', '/', '%', '==', '!=', '>', '>=', '<', '<=', '=>', '>>', '>>=',  '<<', '<<=', '!', '&&', '||', '&', '|', '^', '..', '..=', '&=', '|=', '^=', '#'

///////////////////////////////////////
// (5) Built-in primitive type syntax:
///////////////////////////////////////

// quantum computing specific:
bit, qubit, qstate

// additional quantum types:
// - angle type is similar to OpenQasm3's angle type,  represents values modulo 2π using 32 or 64 bits
// - symbolic compile-time parameters param type is similar to Qiskit's Parameter type
angle32, angle64, param

// signed integer types:  
i8, i16, i32, i64, i128

// unsigned integer types:
u8, u16, u32, u64, u128

// floating-point types:
f32, f64

// boolean type:
bool

// unit type:
()

////////////////////////////////
// (6) Syntax for Basic Types
////////////////////////////////

let f : f32 = 1.234567;
let d : f64 = -1.2345678901234567;

// inferred types for floating point literals
let d = -1000.0;

let i : i8 = -1;
let i : i16 = -1;
let i : i32 = 1;
let i : i64 = 1;
let i : i128 = -1;

// inferred types for integer literals
let i = -7;

// qubit declaration 
let q: qubit = qalloc();
let q: linear qubit = qalloc();
let linear q: qubit = qalloc();

// inferred type for qubit allocation
let q = qalloc();

let u : u8 = 1;
let u : u16 = 1;
let u : u32 = 1;
let u : u64 = 1;
let u : u128 = 1;

let unit : () = ();

// inferred type for unit literal
let unit = ();

// syntax for declaring parameters:
let theta : param = Param("theta");

// var assignment syntax for basic types:
let mut x : i32 = 0;
x = 5;

// var assignment syntax for arrays and tuples:
let mut x : [i32; 2] = [0, 0];
x[0] = 10;

// assignment for tuple members:
let mut t : (i32, f64) = (0, 0.0);
t.0 = 3;

// shared reference
let x = 10;
let r: &i32 = &x;

// mutable reference
let mut x = 10;
let r: &mut i32 = &mut x;

// const variables
const FIVE: i32 = 5;

// Rust-style casts are supported for primitive types:

  // signed integers
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

  // unsigned integers
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

  // floating-point numbers
  let x: f32 = 34.0;
  let x = 34 as f32;

  let x: f64 = 34.0;
  let x = 34 as f64;

  // angle types
  let x: angle32 = 34.0;
  let x = 34 as angle32;

  let x: angle64 = 34.0;
  let x = 34 as angle64;

///////////////////////////////////
// (7) Syntax for declaring arrays
///////////////////////////////////

// canonical array declarations
let bs: [bool; 4] = [true, false, true, false];
let is: [i32; 3] = [1, 2, 3];
let us: [u64; 2] = [10, 20];
let fs: [f64; 3] = [1.0, 2.0, 3.0];
let bits: [bit; 3] = [1, 0, 1];
let qubits: [qubit; 2] = qalloc(2);
let linear qubits: [qubit; 2] = qalloc(2);
let affine qubits: [qubit; 2] = qalloc(2);
let angles: [angle64; 2] = [3.14, 1.57];
let units: [(); 5] = [(), (), (), (), ()];
let params: [param; 2] = [Param("theta"), Param("phi")];

// arrays can be declared with [T; N] where N must be a const expression:
let a: [i32; 4];          // integer literal, inferred as u32
let b: [i32; 2 + 2];      // constant expression
const N: u64 = 4;
let c: [i32; N];          // named constant
let d: [i32; 4u32];       // an integer literal length may have an unsigned suffix
let e: [i32; 4i32];       // INVALID: an array length cannot have a signed suffix
let f: [i32; 256u8];      // INVALID: 256 does not fit in u8

// array declarations with inferred type
let bools = [true, false, true, false];
let ints  = [1, 2, 3];
let zeros = [0; 3];
let fs = [1.0, 2.0, 3.0];
let qubits = qalloc(2);
let units = [(), (), (), (), ()];

////////////////////////////////////////
// (8) Array member access and length:
////////////////////////////////////////

let a = [1, 2, 3];
let first = a[0];
let n = a.len();

//////////////////////////////////////////////
// (9) Array slices and slice references:
//////////////////////////////////////////////

// A slice is a borrowed view into a contiguous part of an array.
// Its type is &[T] (shared) or &mut [T] (mutable), exactly as in Rust.
//
// QUBIT EXCEPTION: qubit references are mutable by default,
// so a qubit slice is written &[qubit] and is already mutable. 'mut' is never
// written on a qubit reference: there is no &mut [qubit] and no &mut qubit.
// For every other element type slices behave exactly like Rust: &[T] is
// read-only and &mut [T] is required to mutate.

// --- Creating a slice from an array (range syntax, identical to Rust) ---

let a: [i32; 5] = [10, 20, 30, 40, 50];

let s: &[i32] = &a[..];      // whole array as a slice
let s: &[i32] = &a[1..4];    // exclusive range: indices 1, 2, 3
let s: &[i32] = &a[1..=3];   // inclusive range: indices 1, 2, 3
let s: &[i32] = &a[2..];     // from index 2 to the end
let s: &[i32] = &a[..3];     // from the start, up to (excluding) index 3
let s: &[i32] = &a[..=3];    // from the start, up to and including index 3

// the slice type can be inferred:
let s = &a[1..4];

// --- Length, indexing, and re-slicing a slice ---

let n = s.len();             // number of elements in the slice
let x = s[0];                // element access
let mid: &[i32] = &s[1..n - 1];   // a slice can itself be re-sliced

// out-of-range indices and ranges are an error, as in Rust.

// --- Mutable slices for non-qubit types (needs 'mut', like Rust) ---

let mut m: [i32; 5] = [10, 20, 30, 40, 50];
let w: &mut [i32] = &mut m[1..4];
w[0] = 99;                   // writes m[1]

let r: &[i32] = &m[..];
// r[0] = 0;                 // ERROR: cannot assign through a shared &[i32]

// --- Qubit slices: mutable by default, never write 'mut' ---

let qs: [qubit; 4] = qalloc(4);

let qv: &[qubit] = &qs[..];  // borrowed view; the range forms above apply unchanged

H(&qv[0]);                   // gates apply in place through the slice
CX(&qv[1], &qv[2]);          // borrowed (in-place) two-qubit form

// let bad: &mut [qubit] = &mut qs[..];   // ERROR: 'mut' not allowed on qubit refs
//
// Because qubit references are mutable by default, qubit slices follow the
// EXCLUSIVE borrow rule (like &mut): two overlapping qubit slices cannot be
// live at the same time, which is what preserves linearity / no-cloning.
// Shared &[T] slices of non-qubit types may overlap freely, exactly as in Rust.

// --- Slices as function parameters ---

// non-qubit, read-only:
classical fn sum(xs: &[i32]) -> i32 {
    let mut total = 0;
    for i in 0..xs.len() {
        total += xs[i];
    }
    total
}

// non-qubit, mutable: requires &mut, exactly like Rust:
classical fn zero_out(xs: &mut [i32]) {
    for i in 0..xs.len() {
        xs[i] = 0;
    }
}

// qubit slice: plain &[qubit] (mutable by default), recursing over the tail:
unitary fn apply_hadamard_layer(qs: &[qubit]) {
    if qs.len() == 0 {
        return;
    }
    H(&qs[0]);
    apply_hadamard_layer(&qs[1..]);
}

// --- Array-to-slice coercion at call sites (like Rust) ---

sum(&a);                     // &[i32; 5] coerces to &[i32]
apply_hadamard_layer(&qs);   // &[qubit; 4] coerces to &[qubit]

/////////////////////////////////////////////////////////////////
// (10) Syntax for allocating qubits and working with bits/qubits
/////////////////////////////////////////////////////////////////

// explicit type annotations for qubits and bits
let q: qubit = qalloc();
let q: linear qubit = qalloc();
let linear q: qubit = qalloc();
let qs: [qubit; 1] = qalloc(1);
let qs: [qubit; 3] = qalloc(3);
let b : bit = measr(q);
let b : bit = 0;
let bs : [bit; 3] = measr(qs);

// inferred types for qubits and bits
let q = qalloc();
let qs = qalloc(3);
let b = measr(q);

// What happens when a qubit is measured?
// if qubit is consumed by measr(), cannot be used after measurement:
let b = measr(q);
// if qubit is borrowed by measr(), can be used after measurement:
let b = measr(&q);

//////////////////////////////////////////////////////////////////////////
// (11) Declaring basis strings literals (arrays of 0 and 1, +, -, I, i):
//////////////////////////////////////////////////////////////////////////

let state = bs"10110010";
let state = bs"++----++";
let state = bs"10+-+-001";
let state = bs"iiiiIIIII";

//////////////////////////////////////////////
// (12) Syntax for qubit qualifiers
//////////////////////////////////////////////

// linear qubits: must be consumed exactly once, no copying or implicit discarding allowed (discarding must be explicit via the discard built-in function)
// this is the default, so the 'linear' keyword is optional
let linear q: qubit = qalloc();
let linear qs: [qubit; 2] = qalloc(2);

// the code above is equivalent to:
let q: linear qubit = qalloc();
let qs: [linear qubit; 2] = qalloc(2);

// affine qubits: must be consumed at most once, no copying allowed, but implicit discarding is allowed
let affine q: qubit = qalloc();
let affine qs: [qubit; 2] = qalloc(2);

// the code above is equivalent to:
let q: affine qubit = qalloc();
let qs: [affine qubit; 2] = qalloc(2);

// in a type, a linear/affine qualifier applies to a single qubit only: arrays and tuples qualify each of their qubits
let qs: [affine qubit; 2] = qalloc(2);                          // valid
let p: (affine qubit, affine qubit) = (qalloc(), qalloc());     // valid
let qs: affine [qubit; 2] = qalloc(2);                          // INVALID
let p: affine (qubit, qubit) = (qalloc(), qalloc());            // INVALID

// a reference borrows its referent without owning it, so no linear/affine qualifier is ever written behind a reference:
// borrowing a linear qubit and borrowing an affine qubit both give a &qubit
let r: &qubit = &q;                                             // valid, whether q is linear or affine
let v: &[qubit] = &qs[..];                                      // valid, whether qs holds linear or affine qubits
let r: &affine qubit = &q;                                      // INVALID
let v: &[linear qubit] = &qs[..];                               // INVALID

// scratch qubits are automatically uncomputed when they go out of scope and reclaimed automatically (no explicit discard is needed)
// the scratch qualifier belongs to let binding and CANNOT appear on qubit type specifications
let scratch q: qubit = qalloc();
let scratch qs: [qubit; 2] = qalloc(2);


// linear/affine type qualifiers can be combined with scratch
// both "scratch linear" and "linear scratch" are accepted syntax for linear scratch qubits, and the same applies for affine scratch qubits
let scratch linear q: qubit = qalloc();
let scratch q: linear qubit = qalloc();
let scratch linear qs: [qubit; 2] = qalloc(2);
let linear scratch qs: [qubit; 2] = qalloc(2);
let scratch qs: [linear qubit; 2] = qalloc(2);
let scratch affine q: qubit = qalloc();
let linear scratch q: qubit = qalloc();
let affine scratch q: qubit = qalloc();
let scratch q: affine qubit = qalloc();
let scratch affine qs: [qubit; 2] = qalloc(2);
let affine scratch qs: [qubit; 2] = qalloc(2);
let scratch qs: [affine qubit; 2] = qalloc(2);

// linear/affine type annotations can be added to a function signature
fn applyHadamard(q: linear qubit) -> linear qubit {
  H(q)
}

/////////////////////////////////////////
// (13) Syntax for working with Quantum Gates
/////////////////////////////////////////

// canonical gate application syntax:
let q: qubit = H(q);
let linear q: qubit = H(q);
let q: linear qubit = H(q);
// gate application syntax with inferred types:
let q = H(q);
// borrowing qubit syntax if the qubit will be needed later.
// Note that Leaf borrows for qubits intentionally differ from Rust borrows since qubits are mutable by default
H(&q);

// parameterized gates:
let q: qubit = U3(1.0, 2.0, 3.0, q);
let q = U3(1.0, 2.0, 3.0, q);
U3(1.0, 2.0, 3.0, &q);

// two-qubit gates:
let (q0, q1) : (qubit, qubit) = CX(q0, q1);
let (q0, q1) = CX(q0, q1);
CX(&q0, &q1);

//////////////////////////////////////////////////////////////////////
// (14) Prelude quantum gates, CAN be shadowed by a local declaration
//////////////////////////////////////////////////////////////////////

I, X, Y, Z, H, S, SDG, T, TDG, SX, SXDG, RX, RY, RZ, U1, U2, U3, CNOT, CX, CY, CZ, CS, CSDG, CT, CTDG, CSX, CSXDG, CRX, CRY, CRZ, CU1, CU2, CU3, SWAP, RXX, RYY, RZZ, CCX, CSWAP, GPI, GPI2, MS, ZZ

// Handling parameterized gates in general: the angle input arguments can be of type: param, angle32, angle64 or floating point numbers

// (i) when the angle argument is a float32/ float64 number, it will be casted to an angle32/ angle64 value.
let q: qubit = U1(0.25, q);

// (ii) angle32 and angle64 represent floating point numbers radians modulo 2π using 32 or 64 bits
let angle: angle64 = 3.141592653589793;
let q: qubit = U1(angle, q);

// (iii) angle32 and angle64 can be specified using the turns() prelude function to convert integer to angles: turns(0.25) = π/2
let angle: angle64 = turns(0.25);
let q: qubit = U1(angle, q);

// (iv) use of symbolic compile-time parameters for parameterized gates:
let theta = Param("theta");
let q: qubit = U1(theta, q);

// Single-Qubit Gates
let q: qubit = I(q);
let q: qubit = X(q);
let q: qubit = Y(q);
let q: qubit = Z(q);
let q: qubit = H(q);
let q: qubit = S(q);
let q: qubit = SDG(q);
let q: qubit = T(q);
let q: qubit = TDG(q);
let q: qubit = SX(q);
let q: qubit = SXDG(q);

// Parametric Single-Qubit Gates
// the angle input arguments can be of type: param, angle32, angle64 or floating point numbers
let q: qubit = RX(1.0, q);
let q: qubit = RY(1.0, q);
let q: qubit = RZ(1.0, q);
let q: qubit = U1(1.0, q);
let q: qubit = U2(1.0, 2.0, q);
let q: qubit = U3(1.0, 2.0, 3.0, q);

// Controlled Gates
// the angle input arguments can be of type: param, angle32, angle64 or floating point numbers
let (q0, q1): (qubit, qubit) = CNOT(q0, q1);
let (q0, q1) = CX(q0, q1);
let (q0, q1) = CY(q0, q1);
let (q0, q1) = CZ(q0, q1);
let (q0, q1) = CS(q0, q1);
let (q0, q1) = CSDG(q0, q1);
let (q0, q1) = CT(q0, q1);
let (q0, q1) = CTDG(q0, q1);
let (q0, q1) = CSX(q0, q1);
let (q0, q1) = CSXDG(q0, q1);

// Controlled Gates with parameters
// the angle input arguments can be of type: param, angle32, angle64 or floating point numbers
let (q0, q1) = CRX(1.0, q0, q1);
let (q0, q1) = CRY(1.0, q0, q1);
let (q0, q1) = CRZ(1.0, q0, q1);
let (q0, q1) = CU1(1.0, q0, q1);
let (q0, q1) = CU2(1.0, 2.0, q0, q1);
let (q0, q1) = CU3(1.0, 2.0, 3.0, q0, q1);

// Two-Qubit Interaction Gates
// the angle input arguments when present can be of type angle32, angle64 or floating point numbers
let (q0, q1) = SWAP(q0, q1);
let (q0, q1) = RXX(1.0, q0, q1);
let (q0, q1) = RYY(1.0, q0, q1);
let (q0, q1) = RZZ(1.0, q0, q1);

// Three-Qubit Gates
let (q0, q1, q2) = CCX(q0, q1, q2);
let (q0, q1, q2) = CSWAP(q0, q1, q2);

// Ion-Native Gates
let q: qubit = GPI(1.0, q);
let q: qubit = GPI2(1.0, q);
let (q0, q1) = MS(1.0, 2.0, q0, q1);
let (q0, q1) = ZZ(1.0, q0, q1);

// Parameterized gates rotation angle arguments can be of type: param, angle32, angle64.

// angle32 and angle64 represent floating point numbers radians modulo 2π using 32 or 64 bits
let angle: angle64 = 3.141592653589793;
let q: qubit = U1(angle, q);

// use the turns() prelude function to convert integer to angles: turns(0.25) = π/2
let q: qubit = U1(turns(0.25), q);

// use of symbolic compile-time parameters for parameterized gates:
let theta = Param("theta");
let q: qubit = U1(theta, q);


////////////////////////////////////////////////////////
// (15) Apply higher-order control gate modifiers: ctrl
////////////////////////////////////////////////////////

// canonical controlled gate
let (q0, q1, q2): (qubit, qubit, qubit) = ctrl(q0, q1).apply(H)(q2);
// controlled gate with inferred types:
let (q0, q1, q2) = ctrl(q0, q1).apply(H)(q2);
// controlled gate with borrowed qubits:
ctrl(&q0, &q1).apply(H)(&q2);
// block syntax
ctrl(&q0, &q1) {
  H(&q2);
}

// applying controls on "10" state
let (q0, q1, q2) = ctrl(q0, q1).on(bs"10").apply(H)(q2);
// same as borrowed qubits:
ctrl(&q0, &q1).on(bs"10").apply(H)(&q2);
// block syntax
ctrl(&q0, &q1).on(bs"10") {
  H(&q2);
}

// apply controls on some generic function of qubits:
let (q0, q1, q2, q3) = ctrl(q0, q1).apply(f)(q2, q3);
// same as borrowed qubits:
ctrl(&q0, &q1).apply(f)(&q2, &q3);
// block syntax
ctrl(&q0, &q1) {
  f(&q2, &q3);
}

// apply controls on some generic function of qubits on ++ state:
let (q0, q1, q2, q3) = ctrl(q0, q1).on(bs"++").apply(f)(q2, q3);
// same as borrowed qubits:
ctrl(&q0, &q1).on(bs"++").apply(f)(&q2, &q3);
// block syntax
ctrl(&q0, &q1).on(bs"++") {
  f(&q2, &q3);
}

//////////////////////////
// (16) Adjoint Operator:
//////////////////////////

// adjoint as higher order function:
let f_adjoint = adjoint(f);

// applying adjoint to generic function of qubits:
let (q1, q2, q3): (qubit, qubit, qubit)  = adjoint(f)(q1, q2, q3);
// adjoint with inferred types
let (q1, q2, q3)  = adjoint(f)(q1, q2, q3);
// adjoint with borrowed qubits:
adjoint(f)(&q1, &q2, &q3);
// block syntax for adjoint:
adjoint {
    f(&q1, &q2, &q3);
}
// applying adjoint to built-in gates:
adjoint {
    H(&q1);
    CT(&q1, &q2)
}
// or equivalently:
adjoint(CT)(&q1, &q2);
adjoint(H)(&q1);

//////////////////////////////
// (17) Arithmetic Operators:
//////////////////////////////

let add = 5 + 3;
let sub = 10 - 4;
let mul = 6 * 2;
let div = 12 / 3;
let rem = 10 % 3;

x += 5;
x -= 2;
x *= 2;
x /= 3;
x %= 4;

//////////////////////////////
// (18) Boolean Operators:
//////////////////////////////

let c = !a;
let d = a && b;
let e = a || b;


////////////////////////////
// (19) Bitwise operations:
////////////////////////////

let and_bit : bit = a & b;
let or_bit  : bit = a | b;
let xor_bit : bit = a ^ b;

x &= y;
x |= y;
x ^= y;

let x = a << 2;
let y = a >> 1;

x <<= 1;
x >>= 1;

//////////////////////////////////
// (20) Classical If/Else syntax:
//////////////////////////////////

  // Like in Rust,else associates with the nearest preceding unmatched if.
  // Like in Rust, else is optional
  // Like in Rust, if/else branches are either expressions or statements

// conditions must be boolean expressions or bits
if 7 > 5 {
  // do something
} else { // else branch is optional
  // do something else
}

//a bit may be used as a classical condition, where 0 means false and 1 means true.
if b { fun(&q); }
// this is syntactic sugar for:
if b == 1 { fun(&q); }

// if else syntax:
let sign = if x < 0 {
  f1()
} else if x == 0 {
  f2()
} else {
  f3()
};

// if else expression syntax:
if x < 0 {
  -1
} else if x == 0 {
  0
} else {
  1
};

// Like in Rust, else associates with the nearest preceding unmatched if. 

///////////////////////////////////////////////
// (21) qif/qelse quantum conditionals syntax:
///////////////////////////////////////////////

  // Like in Rust, qelse associates with the nearest preceding unmatched qif.
  // Like in Rust, qelse is optional
  // Like in Rust, qif/qelse branches are either expressions or statements

  // q is a qubit and must be borrowed
  qif &q {
    // some unitary operation(s)
    X(&t);
  } qelse {
    // some other unitary operation(s)
    H(&t);
  }

  // provided expression1(q2, q3) returns a tuple of qubits, and expression2(q2, q3) returns a tuple of qubits, then the following is valid syntax:
  let (q1, q2, q3) = qif q1 expression1(q2, q3) qelse expression2(q2, q3);

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// (22) qubit quantum state expressions syntax: zero/one/plus/minus/plusi/minusi basis string literals
// phase() and/or turns() prelude helper function are used for applying complex phases
// tensor() built-in function is used for combining states of multiple qstate variables into an array of qstates
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

// zero/one/plus/minus/plusi/minusi are all of type qstate
let sq1: qstate = one;
let sq2: qstate = one;

// zero/one/plus/minus/plusi/minusi can be added/subtracted and multiplied by complex phases using the phase() and possibly turns() built-in functions
// the normalization factor of a qstate expression is ignored, same goes for the global phase of a qstate, so the following are all valid qstate expressions:
let sq: qstate = zero + one;
let sq: qstate = zero - phase(turns(1.0/3.0)) * one;

// qstate variables can be combined into an array of qstates using the tensor() built-in function:
let sq1: qstate = zero + one;
let sq2: qstate = zero - one;
let sq: [qstate; 2] = sq1.tensor(sq2);
let sq: [qstate; 2] = plus.tensor(zero - phase(turns(1.0/3.0)) * one);

// qstate type variable can be initialized from a basis string literals:
let sq: qstate = bs"0";
let sq: qstate = bs"1";
let sq: [qstate; 2] = bs"++";
let sq: [qstate; 4] = bs"iI01";

//////////////////////////////////////////////////////////////////////
// (23) sif/selse quantum conditionals syntax over state expressions:
//////////////////////////////////////////////////////////////////////

  // Unlike in Rust, selse is NOT optional
  // Unlike in Rust, sif/selse branches are always expressions, no statement branches allowed.
  // Unlike in Rust syntax includes the "then" keyword for better readability and to emphasise 'then' should be necessarily followed by an 'selse'

  let qs = sif &q
    then
      // some quantum state expression
    selse
      // some other quantum state expression
  ;

  let (q1, q2, q3) = sif q1 then expression1(q2, q3) selse expression2(q2, q3);

   // state expressions are built using zero/one/plus/minus/plusi/minusi basis string literals, phase() function for applying complex phases, and tensor operator for combining states of multiple qubits:
  sif q then
    (zero + one).tensor(zero - phase(turns(1.0/3.0)) * one)
  selse
    (plus - minus).tensor(plus + phase(turns(1.0/3.0)) * minus);

  // an implementation of X gate using sif/selse syntax, note that while the branches of sif/then/selse are both qstate expressions the type returned by the quantum conditional expression sif/then/selse is qubit.
  unitary fn x(q: qubit) -> qubit {
    sif q then
        zero
    selse
        one
  }

  // an implementation of H gate using sif/selse syntax:
  unitary fn had(q: qubit) -> qubit {
    sif q then
        (zero - one)
    selse
        (zero + one)
  }
  // another implementation of H gate using sif/selse syntax:
  unitary fn had(q: qubit) -> qubit {
    sif q then minus selse plus
  }
  // another implementation of H gate using sif/selse syntax:
  let plusAlias : qstate = zero + one;
  let minusAlias : qstate = zero - one;

  unitary fn had(q: qubit) -> qubit {
      sif q then minusAlias selse plusAlias
  }
  // an implementation of CNOT gate using sif/selse syntax:
  unitary fn cnot(c: qubit, t: qubit) -> (qubit, qubit) {
    sif c then
        // c = |1>, so flip t
        sif t then
            one.tensor(zero)   // |1>|1> ↦ |1>|0>
        selse
            one.tensor(one)    // |1>|0> ↦ |1>|1>
    selse
        // c = |0>, so leave t unchanged
        sif t then
            zero.tensor(one)   // |0>|1> ↦ |0>|1>
        selse
            zero.tensor(zero)  // |0>|0> ↦ |0>|0>
  }

///////////////////////////////////////////
// (24) Classical Rust-style match syntax:
///////////////////////////////////////////

match x {
    1 => foo(),   // comma required
    2 => bar(),   // comma required
    _ => baz(),   // trailing comma optional
}

match x {
    1 => { foo(); }   // comma optional
    2 => { bar(); }
    _ => { baz(); }
}

fn main() {
  let day = 4;

  match day {
    1 => { day_is_monday(); }
    2 => { day_is_tuesday(); }
    3 => { day_is_wednesday(); }
    4 => { day_is_thursday(); }
    5 => { day_is_friday(); }
    6 => { day_is_saturday(); }
    7 => { day_is_sunday(); }
    _ => { day_is_invalid(); }
  }
}

match boolflag {
  true => { /* todo */ }
  false => { /* todo */ }
}

match x {
  n if n > 0 => { /* positive */ }
  _ => { /* other */ }
}

////////////////////////////////////////////////
// (25) Quantum match style expressions qmatch:
////////////////////////////////////////////////

let (qs, q1, q2, q3) = qmatch qs {
  bs"00" => f00(q1, q2, q3),
  bs"01" => f01(q1, q2, q3),
  bs"10" => f10(q1, q2, q3),
  bs"11" => f11(q1, q2, q3),
}

qmatch &qs {
  bs"0+" => f00(&q1, &q2, &q3),
  bs"0-" => f01(&q1, &q2, &q3),
  bs"1+" => f10(&q1, &q2, &q3),
  bs"1-" => f11(&q1, &q2, &q3),
}

// following syntax integer based branch condition syntax is also supported:

qmatch &qs {
  0 => f00(&q1, &q2, &q3),
  1 => f01(&q1, &q2, &q3),
  2 => f10(&q1, &q2, &q3),
  3 => f11(&q1, &q2, &q3),
}

// where the above is the same as:

qmatch &qs {
  bs"00" => f00(&q1, &q2, &q3),
  bs"01" => f01(&q1, &q2, &q3),
  bs"10" => f10(&q1, &q2, &q3),
  bs"11" => f11(&q1, &q2, &q3),
}

// Like in Rust, wildcard patterns are supported for qmatch: 
_ => f()

// mixing basis string expressions bs"00" with digits 0,1,2 in the same qmatch expression is not permitted.

////////////////////////////////////////////////
// (26) Quantum match style expressions smatch:
////////////////////////////////////////////////

// Unlike in Rust, wildcard patterns are NOT supported for smatch. 

smatch &q {
  0 => state_expression0(data),
  1 => state_expression1(data),
}

smatch &qs {
  bs"00" => state_expression_00(data),
  bs"01" => state_expression_01(data),
  bs"10" => state_expression_10(data),
  bs"11" => state_expression_11(data),
}

// mixing basis string expressions bs"00" with digits 0,1,2 in the same smatch expression is not permitted.
smatch &qs {
  0 => state_expression_0(data),
  1 => state_expression_1(data),
  2 => state_expression_2(data),
  3 => state_expression_3(data),
}

// state expressions are built using zero/one/plus/minus/plusi/minusi basis string literals, phase() and possibly turns function for applying complex phases, and tensor operator for combining states of multiple qubits.
smatch &qs {
  bs"00" => (zero + one).tensor(zero - phase(turns(1.0/4.0)) * one),
  bs"01" => (plus - minus).tensor(plus + phase(turns(1.0/4.0)) * minus),
  bs"10" => (zero - one).tensor(zero + phase(turns(1.0/4.0)) * one),
  bs"11" => (plus - minus).tensor(plus - phase(turns(1.0/4.0)) * minus),
}

phase(turns(1.0/4.0))  // the same as: exp(i * π/2)

////////////////////////////////
// (27) Rust block expressions:
////////////////////////////////

let x = {
  let a = 1;
  let b = 2;
  a + b
};

let unit = {
  let a = 1;
};

///////////////////////////////////
// (28) Syntax for declaring loops:
///////////////////////////////////

let mut count = 0;
loop {
    if count == 3 {
        break;
    }
    count += 1;
}

///////////////////////////////////////////////////////
// (29) Syntax for declaring loops that return a value:
///////////////////////////////////////////////////////

let mut count = 0;
let result = loop {

    if count == 3 {
        break count;
    }

    count += 1;
};

///////////////////////////
// (30) While loop syntax:
///////////////////////////

while count <= 5 {
  count += 1;
}

////////////////
// (31) Ranges:
///////////////

// exclusive range:
a..b

// inclusive range:
a..=b

// range from 1 onward
1..     

// range to: everything before 5
..5

// range to inclusive: everything up to and including 5
..=5

// full range
..      

// reverse range
(0..n).rev()

/////////////////////////
// (32) For loop syntax:
/////////////////////////

// using a range in a for loop:

for i in 1..6 {
  // do something
}

/////////////////////////
// (33) Declaring tuples:
/////////////////////////

let t: (i32, f64, bool) = (1, 3.14, true);
let t = (1, 3.14, true);
  
////////////////////////////////////
// (34) Tuples positional indexing:
////////////////////////////////////

let x = t.0;
let y = t.1;
let z = t.2;

// signature of CNOT is: fn CNOT(q0: qubit, q1: qubit) -> (qubit, qubit)
let qubits = CNOT(q0, q1);
let q0 = qubits.0;
let q1 = qubits.1;

//////////////////////////////////////////
// (35) Extracting variables from tuples:
//////////////////////////////////////////

let (a, b, c) = (1, 2, 3);
let (x, _, z) = (1, 2, 3);
let (q0, q1, q2) = (H(q0), H(q1), H(q2));

///////////////////////
// (36) If expressions
////////////////////////

let boolflag = true;
let x : i32 = if boolflag { 1 } else { 2 };

///////////////////////
// (37) Type casting:
///////////////////////

let b : bit = 1;
let x = b as i32;

//////////////////////
// (38) Reset qubits:
//////////////////////

let q: qubit = qalloc();
let q = reset(q);
reset(&q);

let qs: [qubit; 3] = qalloc(3);
// qubits are consumed and returned in reset state
let qs = reset(qs);
// qubits are borrowed and reset in place
reset(&qs);

// resetting multiple qubits:
let (q1, q2, q3): (qubit, qubit, qubit) = reset(q1, q2, q3);
// resetting multiple qubits with inferred:
let (q1, q2, q3) = reset(q1, q2, q3);

//////////////////////
// (39) Discard qubits:
//////////////////////

let q: qubit = qalloc();
discard(q);

let q1: qubit = qalloc();
let q2: qubit = qalloc();
discard(q1, q2);

let qs: [qubit; 3] = qalloc(3);
discard(qs);

/////////////////////////////////////////////////////////////////////////////////
// (40) uncompute qubits: reverse the reversible computation that produced these
// qubits, returning them to |0⟩ when the compiler can verify that this is valid.
//////////////////////////////////////////////////////////////////////////////////

let q: qubit = qalloc();
// qubit is consumed and returned after valid uncomputation
let q = uncompute(q);
// qubit is borrowed and uncomputed in place
uncompute(&q);

let qs: [qubit; 3] = qalloc(3);
let qs = uncompute(qs);
uncompute(&qs);

// uncomputing multiple qubits:
let (q1, q2, q3): (qubit, qubit, qubit) = uncompute(q1, q2, q3);
// uncomputing multiple qubits with inferred types:
let (q1, q2, q3) = uncompute(q1, q2, q3);

//////////////////////////////////////////////////////////
// (41) Weakening qubits: demote linear qubits to affine:
//////////////////////////////////////////////////////////

let linear q: qubit = qalloc();
let affine q = weaken(q);

let linear qs: [qubit; 3] = qalloc(3);
let affine qs = weaken(qs);

let affine (q1, q2, q3): (qubit, qubit, qubit) = weaken(q1, q2, q3);
let (q1, q2, q3) = weaken(q1, q2, q3);

////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// (42) ':=' marks the resulting qubit binding as automatically uncomputed when the enclosing function returns:
////////////////////////////////////////////////////////////////////////////////////////////////////////////////

// The := operator marks the resulting qubit binding as automatically uncomputed when the enclosing function returns. This is similar to Silq's automatic uncomputation feature.

let q: qubit := f(q);
let qs: [qubit; 3] := f(qs);

//////////////////////////
// (43) Measuring qubits:
//////////////////////////

let q: qubit = qalloc();
// qubit is consumed permanently
let b : bit = measr(q);
// qubit is borrowed
let b : bit = measr(&q);

// measuring multiple qubits:
let (b1, b2, b3): (bit, bit, bit) = measr(q1, q2, q3);
// measuring multiple qubits wiyh inferred types:
let (b1, b2, b3) = measr(q1, q2, q3);

let qs: [qubit; 3] = qalloc(3);
// qubits are consumed permanently
let bs : [bit; 3] = measr(qs);
// qubits are borrowed
let bs : [bit; 3] = measr(&qs);

let [b0, b1, b2]: [bit; 3] = measr(qs);

////////////////////////
// (44) Barrier syntax:
////////////////////////

barrier();
let (q0, q1, q2) = barrier(q0, q1, q2);
barrier(&q0, &q1);
let qs = barrier(qs);
barrier(&qs);

////////////////////////////////////////////////////////////////////
// (45) declaring and using modules and imports follows Rust syntax:
////////////////////////////////////////////////////////////////////

// like in Rust, the pub keyword is an access modifier that makes items accessible outside of the module where are defined
mod my_module {
    pub fn helper() -> qubit {
        let q = qalloc(); // some code
        q
    }
}

mod my_library;

use my_library::helper;

fn main() {
    let q = helper();
    discard(q);
}

//////////////////////////
// (46) Functions syntax:
//////////////////////////

fn function_name() {
  // code to be executed
}

// a const fn is a function that may be evaluated at compile time:
const fn square(x: i32) -> i32 {
    x * x
}

///////////////////////////////////////
// (47) Function with typed arguments:
///////////////////////////////////////

fn add(x: i32, y: i32) -> i32 {
  x + y
}

//////////////////////////////////////////
// (48) Function returning some variable:
//////////////////////////////////////////

fn f(x: f32) -> f32 {
  let y = 2.0;
  x + y
}

///////////////////////////////////////////////////////////
// (49) Alternative syntax for function returning a value:
///////////////////////////////////////////////////////////
fn f() -> f64 {
    let x = 2.0;
    return x;
}

//////////////////////////////////////////////////////
// (50) Variable declared in the scope of a function:
//////////////////////////////////////////////////////
fn my_function() {
  let i = 10;
}

///////////////////////////////////////////////////////////
// (51) Functions using references and mutable references:
///////////////////////////////////////////////////////////

struct Person {
    id: i32,
    age: u32,
}

fn my_function(person: &Person) {
    // some code
}

fn my_function(person: &mut Person) {
    // some code
}

//////////////////////////////////////////////////////////
// (52) mutable variable declared in a local block scope:
//////////////////////////////////////////////////////////

{
  let mut x = 0;
  x = x + 1;
}

fn f(mut x: i32) -> i32 {
  x += 1;
  x
}

//////////////////////////////////////////////////////////////////////////////////////////////////
// (53) Function Effect Qualifiers: classical, uncompsafe, unitary, isometry, coisometry, general
//////////////////////////////////////////////////////////////////////////////////////////////////

// function effects are optional Rust-style function qualifiers used by the Leaf type checker to verify Leaf code.
// Function qualifiers appear before fn keyword and cannot be combined with each other

// no quantum operations allowed
classical fn f(x: i32) -> i32 {
  x + 1
}

// only uncomputation-safe quantum operations allowed
uncompsafe fn f(q: qubit) -> qubit {
  let q = X(q);
  q
}

// only unitary quantum operations allowed, nr. output qubits == nr. input qubits
unitary fn f(q: qubit) -> qubit {
  let q = X(q);
  let q = H(q);
  q
}

// only unitary quantum operations allowed, nr. output qubits > nr. input qubits
isometry fn f(qs: [qubit; 2]) -> [qubit; 4] {
  let q1 = X(qs[0]);
  let q2 = H(qs[1]);
  let q3 = qalloc();
  let q4 = qalloc();
  let q3 = X(q3);
  let (q3, q4) = CX(q3, q4);
  [q1, q2, q3, q4]
}

// only unitary quantum operations allowed, nr. output qubits < nr. input qubits
coisometry fn remove_clean_ancilla(
    qs: [qubit; 3]
) -> [qubit; 2]
requires clean(qs[2])
requires separable([qs[2], qs[0], qs[1]])
{
    discard(qs[2]);
    [qs[0], qs[1]]
}

// may include measurements, reset and discard quantum operations
general fn sample(q: qubit) -> bit {
  measr(q)
}

// Being the default effect, the general keyword is optional and is mainly used for generating explicit API specification. If a function does not have a qualifier the compiler will treat it as a general function.

/////////////////////////
// (54) Integer literals
/////////////////////////

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

////////////////////////////////
// (55) Floating point literals
////////////////////////////////

let x = 1.0; // at least one digit is required after the decimal point
let x = 0.1;
let x = 1.0e-3;
let x = 12E+99;
let x = 12E+99_f64;

let f = 1.0f64;
let f = 1.0_f64;
let f = 0.1f32;
let f = 5f32; 

///////////////////////////////////////
// (56) Byte and bytes string literals
///////////////////////////////////////

let b = b'a';
let b = b'\n';
let b = b'\x41';

let bs = b"hello";
let bs = b"ABC\x41";


////////////////////////////////////////////////////
// (57) Rust-style enums containing classical data:
////////////////////////////////////////////////////

// Unit-like enums:
enum ResultBit {
  Zero,
  One,
}

// usage of unit-like enums:
let r = ResultBit::Zero;

// Tuple-like enums:
enum Data {
    Left(i32),
    Right(i32, i32),
}

// usage of tuple-like enums:
let x = Data::Left(1);
let y = Data::Right(2, 3);

//  Struct-like enums:
enum Message {
    Move { x: i32, y: i32 },
    Write { age: i8 },
}

// usage of struct-like enums:
let msg = Message::Move { x: 10, y: 20 };

// important note: like Rust enums can mix unit-like, tuple-like and struct-like variants in the same enum declaration, but for brevity we only show one variant of each kind in the examples above.

//////////////////////////////////////////////////
// (58) Rust-style enums containing quantum data:
//////////////////////////////////////////////////

// Leaf qenum, only tuple-like qenums are supported for quantum data:
qenum Data {

    Left(qubit),
    Right(qubit, qubit),
}

// usage of qenums:
let x = Data::Left(q0);
let y = Data::Right(q1, q2);

///////////////////////////
// (59) Rust-style structs
///////////////////////////

struct Point {
  x: f64,
  y: f64,
}

let p = Point { x: 1.0, y: 2.0 };
let x = p.x;

// destructuring a struct:
struct Pair {
    q0: qubit,
    q1: qubit,
}
let mypair = Pair { q0, q1 };
let Pair { q0: q3, q1: q4 } = mypair;

// like in Rust structs can have methods:
struct Person {
    age: u32,
}

impl Person {
    fn new(age: u32) -> Person {
        Person {
            age,
        }
    }

    fn is_adult(&self) -> bool {
        self.age >= 18
    }
}

// creating a new instance of the struct and calling a method on it:
let person = Person::new(30);
let is_adult = person.is_adult();

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// (60) Quantum Contracts Function Clauses: requires, ensures + clean, stabilized, basis, separable, isolated, product
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

// These are optional code annotations for functions that specify pre- & post-conditions that the quantum data should satisfy:
// they may be used as: requires, ensures or both requires and ensures clauses, and they may be used in any combination with the function effect qualifiers
// from as well as with each other. They must be placed after the function signature and before the function body.
// either requires or ensures clauses may be used, both of them or neither as these are optional annotations.
// There can be multiple requires or ensures clauses for a function, and they can be used in any combination with each other.
//
// - clean(qs) - the qubit(s) are all in $|0\rangle$ state and separated from the rest of qubits in the program.
// - basis([q1, q2, q3], XYZ) - the qubit(s) are in a separable eigenstate of Pauli string like XYZ operator and separated from the rest of qubits in the program.
// - separable(qs) - these qubits are in a separable state meaning that they are not entangled among themselves and separated from the rest of qubits in the program.
// - isolated(qs) - these qubits are not entangled with the rest of qubits in the program even if possibly entangled among them.
// - stabilized(qs) - these qubits are in a state which is stabilized by the supplied operators and at the same time they are separated from the rest of qubits in the program.
// - product(qs, qs') - these qubit sets are not mutually entangled (their joint state in the program is a product state) but in each set qubits may be entangled among each other and may be entangled with other unspecified qubits in the program.

// Clean, stabilized, basis, separable, isolated are all unary predicates:
clean(q1)
basis(q1, X)
basis(q1, Y)
basis(q1, Z)
separable(qs)
isolated(q1)

// For unary predicates, when we need multiple qubits as arguments we can specify them as an array of qubits:
clean([q1, q2])

// second argument is a Pauli string:
basis([q1, q2], XX)

separable([q1, q2])
isolated([q1, q2])

// stabilized, takes as second argument as a list signed Pauli strings representing stabilizers, where each element in the list is a stabilizer and the contract expresses an exact stabilizer state for the qubits in the first argument:
stabilized(qs, [ +ZI, -ZZ ])

// only X/Y/Z/I gates can appear in stabilizer expressions, and the sign of each stabilizer is important, as it represents the eigenvalue of the stabilizer operator for the qubits in the first argument.

// product takes multiple arguments which are either qubits or arrays of qubits:
product(q1, q2, qs)

// products can take multiple arrays of qubits as arguments:
product([q1, q2], [q3, q4], qs)

fn oracle(x: qubit, ancillas: [qubit; 3])
  requires clean(ancillas)
  ensures clean(ancillas) {
    // some code here
}

fn oracle(q1: qubit, q2: qubit, qs: [qubit; 2])
  requires clean(q1)
  requires isolated(qs)
  ensures product([q1, q2], qs){
    // some code here
}

// stabilizer simple examples
requires stabilized(q, [ -Z ])

// more complex stabilizer example with multiple qubits and multi-term stabilizers:
fn make_ghz(q0: &qubit, q1: &qubit, q2: &qubit)
  requires clean([q0, q1, q2])
  ensures stabilized([q0, q1, q2], [+XXX, +ZZI, +IZZ])
{
    H(q0);
    CNOT(q0, q1);
    CNOT(q0, q2);
}

The following gates can appear in stabilizer expressions: I, X, Y, Z, H, S, SDG, SX, SXDG

The "requires" clauses specify the pre-conditions that must hold on the quantum data before the function is called, while the "ensures" clauses specify the post-conditions that must hold on the quantum data after the function returns ao "requires" clauses should precede "ensures" clauses in function signature.

///////////////////////////////////////////////////////////////
// (61) Using function as arguments to higher-order functions:
///////////////////////////////////////////////////////////////
general fn phase_kickback(
    qs: [qubit; 4],
    oracle: unitary fn(qs: [qubit; 4], target: qubit) -> ([qubit; 4], qubit)
) -> [qubit; 4] {
    let scratch ancilla = qalloc();
    let ancilla = prepare_minus(ancilla);
    let (qs, ancilla) = oracle(qs, ancilla);
    qs
}

//////////////////////////////////////////////////////////
// (62) Declaring adjoint/control support for functions:
//////////////////////////////////////////////////////////

// Leaf has a special syntax for those functions where the compiler is able to infer that the function is invertible or controllable using the "supports" keyword combined with "adjoint" or "ctrl" keywords respectively.

unitary fn f(q: &qubit) supports adjoint {
    H(q);
}

unitary fn f(q: &qubit) supports ctrl {
    H(q);
}

unitary fn f(q: &qubit) supports adjoint, ctrl {
    H(q);
}

//////////////////////////////////////////////////////////////////////
// (63) Combining function qualifiers, contracts and support clauses:
//////////////////////////////////////////////////////////////////////

unitary fn f(q1: qubit, q2: qubit, qs: [qubit; 2])
    supports adjoint, ctrl
    requires clean(q1)
    requires isolated(qs)
    ensures basis(q2, X)
    ensures product(q1, q2, qs) {
    // some code here
}

///////////////////////////////////////////////
// (64) Combining qenums with quantum qmatch:
///////////////////////////////////////////////

qenum Data {
    Left(qubit),
    Right(qubit, qubit),
}

unitary fn transform(x: Data) -> Data {
    qmatch x {
        Data::Left(a) => Data::Left(H(a)),

        Data::Right(b, c) => {
            let (b, c) = CNOT(b, c);
            Data::Right(b, c)
        }
    }
}

////////////////////////////////////////////////////////
// (65) Phase function for representing complex phases:
////////////////////////////////////////////////////////

// the phase function can take as arguments a floating
phase(1.5)

// the phase function can take as arguments an angle
let angle: angle64 = 1.88;
phase(angle)

// you can combine the phase() prelude function with turns() prelude function: exp(i * π/2)
phase(turns(0.25))

///////////////////////////////////////////////////////////
// (66) Like in Rust function arguments can be references:
///////////////////////////////////////////////////////////

fn apply_gate(q: &qubit)
{
  H(q);
}

fn main() -> bit {
  let q = qalloc();
  apply_gate(&q);
  let b = measr(q);
  b
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////
// (67) Top level expressions must be items: functions, structs, enums, impl blocks, use statements, consts:
////////////////////////////////////////////////////////////////////////////////////////////////////////////

// Like in Rust at the top level Leaf expects items:

fn main() {
}

struct Person {
    height: i32,
    age: i32,
}

enum Color {
    Red,
    Green,
    Blue,
}

const I: i32 = 1;

impl Person {
    fn new(height: i32, age: i32) -> Person {
        Person { height, age }
    }
}

use my_library::helper;
use my_library::helper as help;

// Top-level code must be made of items, not normal executable statement. These are not allowed at the top level:
let i = 1;
let p = Person { height: 10, age: 20 };

/////////////////////////////////////////////////////////////////////////////
// (68) Function attributes (only qasm_gate/qasm_def is supported for now):
/////////////////////////////////////////////////////////////////////////////

// qasm_gate and qasm_def are mutually exclusive: a function may have at most
// one of these annotations.

// this function is compiled to a OpenQASM3 subroutine representing an unitary operation
#[qasm_gate]
unitary fn myfun(q: qubit) -> qubit {
  let q = X(q);
  let q = H(q);
  q
}

// annotating the function with a string argument
#[qasm_gate("qasm_subroutine_name")]
unitary fn myfun(q: qubit) -> qubit {
  let q = X(q);
  let q = H(q);
  q
}

// this function is compiled to a named QASM subroutine with same signature
#[qasm_def]
general fn myfun(q: qubit) -> bit {
  let q = X(q);
  let q = H(q);
  measr(q)
}

// annotating the function with a string argument
#[qasm_def("qasm_subroutine_name")]
general fn myfun(q: qubit) -> bit {
  let q = X(q);
  let q = H(q);
  measr(q)
}

///////////////////
// (69) Recursion:
//////////////////

// Purely classical recursion.
classical fn fact(n: u32) -> u32 {
    if n == 0 { 1 } else { n * fact(n - 1) }
}

// Circuit-generating unitary recursion over a classical parameter, safe if total and structurally decreasing:
unitary fn apply_hadamard_layer(qs: &[qubit]) {
    if qs.len() == 0 {
        return;
    }

    H(&qs[0]);

    apply_hadamard_layer(&qs[1..]);
}

// Classically controlled recursion:
general fn sample_until_zero() -> qubit {
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

// Quantum controlled recursion and recursive quantum types are not supported at this moment








// /////////////////
// // (70) Strings:
// /////////////////

// // Like in Rust, Leaf supports string literals. Leaf does not have a print statement and since Leaf commpiles to OpenQasm3 and OpenQASM3 does not have a string type, strings in Leaf are used mainly to help write more expressive code:

// let mut string = String::new();

// // String literal using the string-slice type:
// let message: &str = "Hello, world!";

// // Owned strings: String
// let message: String = String::from("Hello");

// // A String type owns its allocated text and can be modified:
// let mut text: String = String::from("Hello");
// text.push_str(", world");
// text.push('!');

// // String interpolation:
// let first = "Hello";
// let second = "world";
// let message = format!("{first}, {second}!");

// // Same code as above but with explicit type annotations and string concatenation:
// let first: &str = "Hello";
// let second: &str = "world";
// let message: String = String::from(first) + ", " + second + "!";

// // Strings may also be required lexically for Param types. Another example using string interpolation:
// let i: i32 = 1;
// let theta: param = Param(format!("theta_{i}"));

// // raw string literals are supported
// let s = r"hello\nworld";

// // String ownership and borrowing:
// let owned: String = String::from("Hello");
// let borrowed: &str = &owned;

// // Comparing strings:
// let a = "hello";
// let b = "hello";

// if a == b {
//     // some code
// }

// if a != "world" {
//     // some code
// }

// let a = "apple";
// let b = "banana";

// if a < b {
//     // some code
// }

// // String slices can be indexed and sliced:
// let text = "Hello";
// let a = &text[..2];  // "He"
// let b = &text[2..];  // "llo"
// let c = &text[..];   // "Hello"

// ////////////////////////////////////////////////
// // (71) format! macro for string interpolation:
// /////////////////////////////////////////////////

// // Leaf does not support macros yet but "format!" macro for string interpolation is supported as a built-in feature of the language. The syntax is similar to Rust's format! macro.

// let first: &str = "Trying";
// let second: i32 = 3;
// let third: &str = "times";
// let message: String = format!("{first} {second} {third}!");

// //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// // (73) Rust style characters, which are single Unicode scalar values, are supported in Leaf:
// ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

// let c: char = 'a';
// let digit: char = '7';
// let space: char = ' ';
// let newline: char = '\n';
// let quote: char = '\'';
// let backslash: char = '\\';

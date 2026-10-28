### Quantum Gates


Example gate applications:
```leaf
let q: qbit = H(q);

// or:

let q = H(q);
```

For a two qubit gate:

```leaf
let (q0, q1) : (qbit, qbit) = CX(q0, q1);

// or:

let (q1, q2) = CNOT(q1, q2);
```

These operations are built in, but conceptually they can also act like functions that borrow their qubit arguments:

```leaf
H(&q);
CNOT(&q1, &q2);
```

Qubits are mutable by default so the `H(&q)` syntax accepted by Leaf would have been written in Rust as: `H(&mut q)`.

All prelude quantum gates, CAN be shadowed by a local declaration:

### Identity

```leaf
I(&q);
```

### Single-Qubit Gates

```leaf
X(&q);
Y(&q);
Z(&q);
H(&q);
S(&q);
SDG(&q);
SX(&q);
SXDG(&q);
T(&q);
TDG(&q);
```

### Parametric Single-Qubit Gates

```leaf
RX(1.0, &q);
RY(1.0, &q);
RZ(1.0, &q);
U1(1.0, &q);
U2(1.0, 2.0, &q);
U3(1.0, 2.0, 3.0, &q);
```

### Controlled Gates

```leaf
CX(&q1, &q2);
CNOT(&q1, &q2);
CY(&q1, &q2);
CZ(&q1, &q2);
CS(&q1, &q2);
CSDG(&q1, &q2);
CSX(&q1, &q2);
CSXDG(&q1, &q2);
CT(&q1, &q2);
CTDG(&q1, &q2);
CRX(1.0, &q1, &q2);
CRY(1.0, &q1, &q2);
CRZ(1.0, &q1, &q2);
CU1(1.0, &q1, &q2);
CU2(1.0, 2.0, &q1, &q2);
CU3(1.0, 2.0, 3.0, &q1, &q2);
```

### Two-Qubit Interaction Gates

```leaf
SWAP(&q1, &q2);
RXX(1.0, &q1, &q2);
RYY(1.0, &q1, &q2);
RZZ(1.0, &q1, &q2);
```

### Three-Qubit Gates

```leaf
CCX(&q1, &q2, &q3);
CSWAP(&q1, &q2, &q3);
```

### IonQ-Native Gates

```leaf
GPI(1.0, &q);
GPI2(1.0, &q);
MS(1.0, 2.0, &q1, &q2);
ZZ(1.0, &q1, &q2);
```

### Barrier
Barrier is a built-in function not a quantum gate and is compiled directly to an OpenQasm3 barrier instruction:
```leaf
barrier();
barrier(&q1, &q2);
```

### Handling parameterized gates

Parameterized gates rotation angle arguments can be of type: param, angle32, angle64.

(i) angle32 and angle64 represent floating point numbers radians modulo 2π using 32 or 64 bits
```leaf
let angle: angle64 = 3.141592653589793;
let q: qbit = U1(angle, q);
```

(ii) use the turns() prelude function to convert integer to angles: turns(0.25) = π/2
```leaf
let q: qbit = U1(turns(0.25), q);
```

// (iii) use of symbolic compile-time parameters for parameterized gates:
```leaf
let theta = Param("theta");
let q: qbit = U1(theta, q);
```

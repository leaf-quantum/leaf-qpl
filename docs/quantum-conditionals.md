
## Quantum Conditionals and Generalizations

Quantum conditionals are the first step in an attempt to go beyond the *quantum data + classical control* paradigm of quantum programming [[Selinger (2004)]](./bibliography.md#selinger-2004-towards-quantum-programming-language) which is based on the QRAM model of a quantum computation [[Knill (1996)]](./bibliography.md#knill-1996-conventions-quantum-pseudocode). The path from here toward more general quantum control over quantum data will probably be an interesting journey.

### (1) Resource-oriented qubits model: `qif`/`qelse`/`qmatch`

For a [resource-oriented](qubit-representations.md#resource-oriented-qubit-model) qubits model, a quantum conditional on qubit q means applying two quantum operations on a distinct set of qubits depending on the state of `q`, coherently, without measuring `q`. The precise semantics of this construction is discussed [here](defining-terms.md#what-are-quantum-conditionals).

```leaf
fn f1(q1 : qbit, q2 : qbit) -> (qbit, qbit) { ... }
fn f2(q1 : qbit, q2 : qbit) -> (qbit, qbit) { ... }

let (q1, q2, q3) = qif q1 {
  f1(q2, q3)
} qelse {
  f2(q2, q3)
}
```

Besides expressions, statements are also supported in the qif/qelse branches:

```leaf
fn f3(q1 : qbit, q2 : qbit) { ... }
fn f4(q1 : qbit, q2 : qbit) { ... }

qif &q1 {
  f3(&q2, &q3);
} qelse {
  f4(&q2, &q3);
}
```

It is required of f1/f2 or f3/f4 to be unitary functions (no discarding on input qubits, no measurements or resets), to operate on the same number of qubits, and to not act on the control qubit. Any ancilla qubits created inside the two functions must be returned in a clean pure zero state and in the end safely discarded. The `qelse` branch is optional and if missing it is equivalent to applying the identity operator in the second branch. If both branches are present the operations implemented by the two branches are in no way conditioned with respect to each other.

#### Generalizing `qif/qelse` to `qmatch`

A straightforward generalization of a quantum conditional for multiple branches implies coherent control over qubits `qs` without performing measurements:

```leaf
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
```

  Assuming branching is done in computational basis states, the following syntax is supported as well:

```leaf
  qmatch &qs {
    0 => f00(&q1, &q2, &q3),
    1 => f01(&q1, &q2, &q3),
    2 => f10(&q1, &q2, &q3),
    3 => f11(&q1, &q2, &q3),
  }

  // which is the same as:

  qmatch &qs {
    bs"00" => f00(&q1, &q2, &q3),
    bs"01" => f01(&q1, &q2, &q3),
    bs"10" => f10(&q1, &q2, &q3),
    bs"11" => f11(&q1, &q2, &q3),
  }
```

Similar conditions that apply to quantum conditionals branches apply here as well for functions in `qmatch` branches. The operations implemented by different branches are in no way conditioned with respect to each other but must not act on the match condition qubits. Like in Rust, match must be exhaustive but the placeholder `_ => ` syntax is supported such that match expressions that are not specified can be assigned a default, possibly trivial operation. Mixing basis string expressions `bs"00"` with digits `0,1,2` in the same qmatch expression is not allowed.

### (2) State-oriented qubits model: `sif`/`selse/smatch`

For the [state-oriented](qubit-representations.md#state-oriented-qubit-model) qubits model, the elementary quantum conditional example is the X gate represented as a coherent operation like this:

```leaf
unitary fn x(q: qbit) -> qbit {
    sif q then
        zero
    selse
        one
}
```

The whole function maps a qubit to a qubit and denotes a transformation on q. To grasp this more easily it is useful to realize that `zero` could have been named: `qfalse` and `one`: `qtrue`, following the notation from [Grattage (2008)](./bibliography.md#grattage-2008-overview-qml-haskell). The function returns a symbolic state expression which cannot contain quantum gates or non-unitary qubit operations like measure, reset or discard. In order for the operation to describe a unitary transformation the `sif`/`selse` branches must be provably orthogonal which in the example above is obvious. Unlike `qelse`, the `selse` branch is NOT optional. A slightly more involved example the following implementation of the CNOT gate:

```leaf
unitary fn cnot(c: qbit, t: qbit) -> (qbit, qbit) {
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
```

#### Generalizing `sif/then/selse` to `smatch`

A generalization of quantum conditional state expressions for multiple branches implies coherent control over qubits `qs` without performing measurements:

```leaf
smatch &qs {
  bs"00" => (zero + one).tensor(zero - phase(turns(1.0/4.0)) * one),
  bs"01" => (plus - minus).tensor(plus + phase(turns(1.0/4.0)) * minus),
  bs"10" => (zero - one).tensor(zero + phase(turns(1.0/4.0)) * one),
  bs"11" => (plus - minus).tensor(plus - phase(turns(1.0/4.0)) * minus),
}
```

All possible branches must be specified and must describe states that are provably orthogonal with respect to each other. This implies the wildcard placeholder is not supported in this case. The `phase(turns(1.0/4.0))` expression based on built-in helper functions [phase()](builtins.md#built-in-functions) and [turns()](builtins.md#built-in-functions), is equivalent to: `exp(i * π/2)`. Mixing basis string expressions `bs"00"` with digits `0,1,2` in the same smatch expression is not allowed.

### Modeling Qubits

#### Resource-oriented qubit model

Qubits are treated as mutable computational resources whose quantum state evolves when quantum gates are applied.

```leaf
let q: qbit = qalloc();
let q = H(q);
```

#### State-oriented qubit model

Qubits are represented using a language of expressions denoting vectors or states in a Hilbert space built using the `qstate` typed language constants: `zero`, `one`, `plus`, `minus`, `plusi` and `minusi`. These constants are used inside state quantum state expressions and do not denote allocated runtime qubits. These constants can be combined into state expressions using addition, subtraction operators and complex phases specified using the prelude functions: phase() and turns(). The quantum state denoted by such a state expression is always a separable quantum state, making circuit the synthesis of quantum circuits based on specified state expressions workable by the compiler. The normalization factor of a state expression is ignored, same goes for the global phase of a state, so the following are all valid `qstate` expressions:

```leaf
let sq: qstate = zero + one;
let sq: qstate = zero - phase(turns(1.0/3.0)) * one;
```

Variables of type `qstate` can be combined into an array of same type using the tensor() prelude function:
```leaf
let sq1: qstate = zero + one;
let sq2: qstate = zero - one;
let sq: [qstate; 2] = sq1.tensor(sq2);
let sq: [qstate; 2] = plus.tensor(zero - phase(turns(1.0/3.0)) * one);
```

An implementation of Hadamard gate using `sif/then/selse` pattern is shown next:

```leaf
unitary fn had(q: qbit) -> qbit {
    sif q then
        (zero - one)
    selse
        (zero + one)
}
```

Note that while the branches of `sif/then/selse` are both `qstate` expressions the type returned by the quantum conditional expression `sif/then/selse` is `qbit`. The above code is equivalent to:

```leaf
unitary fn had(q: qbit) -> qbit {
    sif q then minus selse plus
}
```

Using `qstate` variables, the Hadamard operation can be implemented as:

```leaf
let plusAlias : qstate = zero + one;
let minusAlias : qstate = zero - one;

unitary fn had(q: qbit) -> qbit {
    sif q then minusAlias selse plusAlias
}
```

Note that the overall normalization factor is ignored in quantum state expressions. The state-oriented representation of qubits establishes a denotational unitary expression fragment which is useful among others for generating quantum programs starting from physics denotation instead of relying on an abstract quantum circuit model. The prototypical example for this use case is generating a circuit for QFT from its mathematical definition within the Leaf programming language.

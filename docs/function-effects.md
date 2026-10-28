### Function Effects

These are Rust-style function qualifiers used by the Leaf type checker to verify the code. The function effects form a lattice:

```leaf
         general
          /   \
    isometry coisometry
          \   /
         unitary
            |
        uncompsafe
            |
        classical
```

- `classical` is used to classify strictly classical functions i.e. functions that do not have qubit arguments, do not return qubits and do not perform any quantum operations like qubit allocation or operations on quantum data:

```leaf
classical fn parity (x : u32) -> bool { ... }
```

- `uncompsafe` effect is used to classify functions that implement reversible classical computation lifted to quantum data. These contain a subset of strictly unitary quantum gates that do not generate or destroy entanglement *on basis states*. For example X and CNOT gates are `uncompsafe` while H is not, These basis-preserving quantum gates are used to generate circuits whose effects can be undone automatically such that the ancilla qubits can be subsequently discarded safely. Since the quantum gates preserve the number of qubits, for such functions the number of output qubits must be the same as the number of input qubits. Such a function can allocate local ancilla qubits as long as the ancilla qubits are being restored to a clean state and discarded. Automatic [uncomputation](defining-terms.md#what-does-uncomputation-mean) is possible when the computation of the temporary value can be described classically on basis states which is exactly what `uncompsafe` effect is capturing. In addition to this condition, if the operation to be uncomputed depends on some variable, this variable needs to be available at the moment of uncomputation, so it needs to act like a constant value. This means that it is either a classical constant variable, or some quantum data that we can infer was not altered by the computation we want to undo.

```leaf
uncompsafe fn oracle (ancillas : [qbit; 3]) -> [qbit; 3] { ... }
```

- `unitary` is used to classify functions containing unitary quantum gates or invoking `unitary` functions:
 
```leaf
unitary fn grover (qbits : [qbit; 7]) -> [qbit; 7] { ... }
```

A function qualified as `unitary` contains only unitary quantum operations. Since the quantum gates preserve the number of qubits, for such functions the number of qubits must be the same as the number of output qubits. Such a function can allocate local ancilla qubits as long as the ancilla qubits are being restored to a clean state and discarded.

- a `isometry` function is the same as a `unitary` function except that the number of output qubits is larger than the number of input qubits:

```leaf
isometry fn fanOut (qbits : [qbit; 3]) -> [qbit; 7] { ... }
```

- a `coisometry` function is the same as a `unitary` function except that the number of output qubits is smaller than the number of input qubits and the qubits which are thrown away must be driven into a clean state before discarding:

```leaf
coisometry fn fanIn (qbits : [qbit; 7]) -> [qbit; 3] { ... }
```

- `general` is used to classify functions which in addition to quantum gates contain `measr`, `reset` or `discard` operations or are invoking `general` functions:

```leaf
general fn sample (qs: [qbit; 7]) -> [bit; 7] { ... }
```

Being the default effect, the `general` keyword is optional and is mainly used for generating explicit API specification. If a function does not have a qualifier the compiler will treat it as a `general` function.

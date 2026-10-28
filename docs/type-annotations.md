### Qubit Type Annotations

Linear qubits must be used exactly once, no copying or implicit discarding allowed. Linear annotation is the default for qubits, so the 'linear' keyword is optional. Instead of implicit discarding, one should use the `discard()` function to mark qubits programmatically as discarded. Discarding qubits is the programmer's decision and any qubit can be discarded, it is not necessary for it to be in a clean state or separated from the rest of the program qubits. However, one should be aware that discarding a qubit can have [physical consequences](quantum-data-operations.md#operations-on-qubits).
```leaf
let linear q: qbit = qalloc();
let linear qs: [qbit; 2] = qalloc(2);
```

Affine qubits must be used at most once, no copying allowed but implicit discarding is allowed. While using affine qubits may be useful in certain situations this should be the exception rather than the rule.
```leaf
let affine q: qbit = qalloc();
let affine qs: [qbit; 2] = qalloc(2);
```

Scratch qubits are automatically uncomputed at the end of their scope and reclaimed automatically. The compiler must prove statically that these qubits to be safely uncomputed before implementing this operation.
```leaf
let scratch q: qbit = qalloc();
let scratch qs: [qbit; 2] = qalloc(2);
```

Linear or affine qubit type qualifiers can be combined with scratch type qualifier.
```leaf
let scratch linear q: qbit = qalloc();
let scratch linear qs: [qbit; 2] = qalloc(2);
let scratch affine q: qbit = qalloc();
let scratch affine qs: [qbit; 2] = qalloc(2);
```

### Uncomputation

User can trigger manually uncomputation for qubits that have been generated with `uncompsafe` functions:
```leaf
let q = uncompute(q);
let (q1, q2, q3) = uncompute(q1, q2, q3);
```

The `:=` operator marks the resulting qubit binding as automatically uncomputed when the enclosing function returns provided these are `uncompsafe` functions:

```leaf
let q: qbit := fun(q);
let qs: [qbit; 3] := fun(qs);
```

Scratch qubits are automatically uncomputed at the end of their scope. In order for this to work the compiler must be able to validate that uncomputation is possible by inferring the correct uncomputation sequence:
```leaf
fn uses_scratch() {
    let scratch q: qbit = qalloc();
    ...
}
```

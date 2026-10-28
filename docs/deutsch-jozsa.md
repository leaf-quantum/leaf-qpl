### Deutsch-Jozsa Algorithm

This is an elementary implementation of Deutsch-Jozsa:

```rust
// U_f : |x⟩|y⟩ ↦ |x⟩|y ⊕ f(x)⟩
unitary fn balanced_oracle(
    q0: qbit,
    q1: qbit,
    q2: qbit,
    q3: qbit,
    q4: qbit,
) -> (qbit, qbit, qbit, qbit, qbit) {

    // Negative controls on q0 and q2 by X-conjugation.
    let q0 = X(q0);
    let q2 = X(q2);

    let (q0, q4) = ctrl(q0).apply(X)(q4);
    let (q1, q4) = ctrl(q1).apply(X)(q4);
    let (q2, q4) = ctrl(q2).apply(X)(q4);
    let (q3, q4) = ctrl(q3).apply(X)(q4);

    // Restore q0 and q2.
    let q0 = X(q0);
    let q2 = X(q2);

    (q0, q1, q2, q3, q4)
}

general fn deutsch_jozsa_balanced() -> (bit, bit, bit, bit) {

    let q0 = qalloc();
    let q1 = qalloc();
    let q2 = qalloc();
    let q3 = qalloc();
    let q4 = qalloc();

    // Prepare ancilla in |1>.
    let q4 = X(q4);

    // Apply H to input register and ancilla.
    let q0 = H(q0);
    let q1 = H(q1);
    let q2 = H(q2);
    let q3 = H(q3);
    let q4 = H(q4);

    let (q0, q1, q2, q3, q4) =
        balanced_oracle(q0, q1, q2, q3, q4);

    // Interference step on the input register.
    let q0 = H(q0);
    let q1 = H(q1);
    let q2 = H(q2);
    let q3 = H(q3);

    let (b0, b1, b2, b3) = measr(q0, q1, q2, q3);
    
    // q4 is not part of the Deutsch-Jozsa result.
    discard(q4);

    (b0, b1, b2, b3)
}

general fn main() -> (bit, bit, bit, bit) {
    deutsch_jozsa_balanced()
}
```

### Deutsch-Jozsa Algorithm

This is an even more compact implementation of Deutsch-Jozsa:

```rust
// U_f : |x⟩|y⟩ ↦ |x⟩|y ⊕ f(x)⟩
unitary fn balanced_oracle(qs: [qbit; 4], ancilla: qbit) -> ([qbit; 4], qbit) {
    // Negative controls on qs[0] and qs[2] by X-conjugation.
    X(&qs[0]);
    X(&qs[2]);

    for q in &qs {
        ctrl(q) {
            X(&ancilla);
        }
    }

    // Restore qs[0] and qs[2].
    X(&qs[0]);
    X(&qs[2]);

    (qs, ancilla)
}

general fn deutsch_jozsa_balanced() -> [bit; 4] {
    let qs = qalloc(4);
    let ancilla = qalloc();

    // Prepare ancilla in |1>.
    X(&ancilla);

    // Apply H to input register and ancilla.
    for q in &qs {
        H(q);
    }

    H(&ancilla);

    let (qs, ancilla) = balanced_oracle(qs, ancilla);

    // Interference step on the input register only.
    for q in &qs {
        H(q);
    }

    let bs = measr(qs);

    // ancilla is not part of the Deutsch-Jozsa result.
    discard(ancilla);

    bs
}

general fn main() -> [bit; 4] {
    deutsch_jozsa_balanced()
}
```

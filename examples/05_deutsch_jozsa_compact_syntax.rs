//////////////////////////////////////////////////////////////
// More compact implementation of Deutsch-Jozsa algorithm
//
// The standard extension of Leaf code files should be `.lf`
// We use `.rs` here for syntax highlighting purposes only.
//////////////////////////////////////////////////////////////

unitary fn balanced_oracle(qs: [qbit; 5]) -> [qbit; 5] {
    // Negative controls on qs[0] and qs[2] by X-conjugation.
    X(&qs[0]);
    X(&qs[2]);

    for i in 0..4 {
        ctrl(&qs[i]).apply(X)(&qs[4]);
    }

    // Restore qs[0] and qs[2].
    X(&qs[0]);
    X(&qs[2]);

    qs
}

general fn deutsch_jozsa_balanced() -> [bit; 4] {
    let qs = qalloc(5);

    // Prepare ancilla in |1>.
    X(&qs[4]);

    // Apply H to input register and ancilla.
    for i in 0..5 {
        H(&qs[i]);
    }

    let qs = balanced_oracle(qs);

    // Interference step on the input register only.
    for i in 0..4 {
        H(&qs[i]);
    }

    // todo: partial moves out of arrays need explicit documentation
    let (b0, b1, b2, b3) = measr(qs[0], qs[1], qs[2], qs[3]);

    // qs[4] is not part of the Deutsch-Jozsa result.
    discard(qs[4]);

    [b0, b1, b2, b3]
}

general fn main() -> [bit; 4] {
    deutsch_jozsa_balanced()
}
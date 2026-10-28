/////////////////////////////////////////////////////////////////////
// Deutsch-Jozsa implementation using quantum conditional statement
//
// The standard extension of Leaf code files should be `.lf`
// We use `.rs` here for syntax highlighting purposes only.
/////////////////////////////////////////////////////////////////////

unitary fn prepare_minus(q: qbit) -> qbit {
    let q = X(q);
    let q = H(q);
    q
}

uncompsafe fn balanced_oracle(
    qs: [qbit; 3],
    ancilla: qbit
) -> ([qbit; 3], qbit) {
    qmatch &qs {
        bs"000" => Id(&ancilla),   // 0 ones  → f = 0
        bs"001" => Id(&ancilla),   // 1 one   → f = 0
        bs"010" => Id(&ancilla),   // 1 one   → f = 0
        bs"011" => X(&ancilla),    // 2 ones  → f = 1
        bs"100" => Id(&ancilla),   // 1 one   → f = 0
        bs"101" => X(&ancilla),    // 2 ones  → f = 1
        bs"110" => X(&ancilla),    // 2 ones  → f = 1
        bs"111" => X(&ancilla),    // 3 ones  → f = 1
    }
    (qs, ancilla)
}

general fn deutsch_jozsa() -> [bit; 3] {
    let qs = qalloc(3);
    let ancilla = qalloc();

    for q in &qs {
        H(q);
    }

    let ancilla = prepare_minus(ancilla);

    let (qs, ancilla) = balanced_oracle(qs, ancilla);

    for q in &qs {
        H(q);
    }

    let bs = measr(qs);
    discard(ancilla);
    bs
}

general fn main() -> [bit; 3] {
    deutsch_jozsa()
}

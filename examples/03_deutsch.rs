//////////////////////////////////////////////////////////////
// Implementation of Deutsch's algorithm in Leaf.
//
// The standard extension of Leaf code files should be `.lf`
// We use `.rs` here for syntax highlighting purposes only.
//////////////////////////////////////////////////////////////

unitary fn balanced_oracle(
    q0: qbit,
    q1: qbit,
) -> (qbit, qbit) {
    // This implements a balanced oracle using a negative control.
    //
    // The oracle maps:
    //
    //     |x, y> ↦ |x, y xor f(x)>

    X(&q0);

    ctrl(&q0) {
        X(&q1);
    }

    X(&q0);

    (q0, q1)
}

general fn deutsch_balanced() -> bit {
    let q0 = qalloc();
    let q1 = qalloc();

    // Prepare second qubit in |1>.
    X(&q1);

    // Prepare |+> on q0 and |-> on q1.
    H(&q0);
    H(&q1);

    let (q0, q1) = balanced_oracle(q0, q1);

    // Interference step on the input qubit.
    H(&q0);

    let b = measr(q0);

    // q1 is the phase-kickback ancilla, not part of the answer.
    discard(q1);

    b
}

general fn main() -> bit {
    deutsch_balanced()
}

// Mark the state 1011111, ordered as inputs[0] through inputs[6].
// With the ancilla in |−⟩, the controlled X flips this state's phase.
unitary fn oracle(inputs: &[qbit], ancilla: &qbit) {
    ctrl(
        &inputs[0], &inputs[1], &inputs[2], &inputs[3],
        &inputs[4], &inputs[5], &inputs[6]
    ).on(bs"1011111") {
        X(ancilla);
    }
}

// Implement inversion about the mean, up to an overall global phase.
unitary fn grover_diffusion_operator(inputs: &[qbit]) {
    for i in 0..7 {
        H(&inputs[i]);
    }

    // Map |0000000⟩ to |1111111⟩ so it can be phase-flipped.
    for i in 0..7 {
        X(&inputs[i]);
    }

    // Flip the phase only when all seven input qubits are |1⟩.
    ctrl(
        &inputs[0], &inputs[1], &inputs[2],
        &inputs[3], &inputs[4], &inputs[5]
    ).on(bs"111111") {
        Z(&inputs[6]);
    }

    for i in 0..7 {
        X(&inputs[i]);
    }

    for i in 0..7 {
        H(&inputs[i]);
    }
}

fn main() -> [bit; 7] {
    let inputs: [qbit; 7] = qalloc(7);
    let ancilla: qbit = qalloc();

    // Prepare |−⟩ for phase kickback from the oracle.
    X(&ancilla);
    H(&ancilla);

    // Prepare an equal superposition of all 128 candidate strings.
    for i in 0..7 {
        H(&inputs[i]);
    }

    // Preserve the diffusion-then-oracle order of the original code.
    for iteration in 0..7 {
        oracle(&inputs, &ancilla);
        grover_diffusion_operator(&inputs);
    }

    // The ancilla remains separable in |−⟩ and can be discarded.
    discard(ancilla);

    // Return the measured candidate in inputs[0] ... inputs[6] order.
    measr(inputs)
}

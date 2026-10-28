// For an output register initially in |000⟩, compute
// f(x0, x1, x2) = (x0, 0, x1 XOR x2).
// Thus f(x) = f(x XOR 011): the hidden period is 011.
unitary fn two_to_one_oracle(inputs: &[qbit], outputs: &[qbit]) {
    CX(&inputs[0], &outputs[0]);
    CX(&inputs[1], &outputs[1]);
    CX(&inputs[2], &outputs[2]);

    // This repeats and cancels the earlier CX on outputs[1],
    // preserving the gate sequence of your original code.
    CX(&inputs[1], &outputs[1]);
    CX(&inputs[1], &outputs[2]);
}

// Compute f(x) = x in the initially zero output register.
// This function is one-to-one, with no nonzero hidden period.
unitary fn one_to_one_oracle(inputs: &[qbit], outputs: &[qbit]) {
    CX(&inputs[0], &outputs[0]);
    CX(&inputs[1], &outputs[1]);
    CX(&inputs[2], &outputs[2]);
}

// Perform one quantum sampling round using the supplied oracle.
fn simon(
    oracle: unitary fn(inputs: &[qbit], outputs: &[qbit]) -> ()
) -> [bit; 3] {
    let inputs: [qbit; 3] = qalloc(3);
    let outputs: [qbit; 3] = qalloc(3);

    // Prepare an equal superposition of all eight inputs.
    for i in 0..3 {
        H(&inputs[i]);
    }

    // Correlate each input |x⟩ with its function value |f(x)⟩.
    oracle(&inputs, &outputs);

    // Interference restricts the measured strings y to those
    // satisfying y · s = 0 modulo 2, where s is the hidden period.
    for i in 0..3 {
        H(&inputs[i]);
    }

    // Discard the output register; its measurement result is not needed.
    discard(outputs);

    // Return one sample y, ordered as [y0, y1, y2].
    measr(inputs)
}

fn main() -> [bit; 3] {
    simon(two_to_one_oracle)
}

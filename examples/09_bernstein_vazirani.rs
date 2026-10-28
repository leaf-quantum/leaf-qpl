
// Encode the hidden string 01100:
// f(x) = x[1] XOR x[2], with bits ordered as q0, q1, q2, q3, q4.
unitary fn oracle(inputs: &[qbit], target: &qbit) {
    CX(&inputs[1], target);
    CX(&inputs[2], target);
}

fn main() -> [bit; 5] {
    let inputs: [qbit; 5] = qalloc(5);
    let ancilla: qbit = qalloc();

    // Prepare the ancilla in |−⟩ so that a controlled X
    // kicks back a phase of −1 onto the corresponding input branch.
    X(&ancilla);
    H(&ancilla);

    // Prepare an equal superposition of all 32 input bit strings.
    for i in 0..5 {
        H(&inputs[i]);
    }

    // Encode f(x) as the phase (−1)^f(x) of each input basis state.
    // The borrowed qubits remain available after the call.
    oracle(&inputs, &ancilla);

    // Interference transforms the phase pattern into the hidden string.
    for i in 0..5 {
        H(&inputs[i]);
    }

    // The ancilla remains in |−⟩ and is separable from the inputs.
    discard(ancilla);

    // Consume the input register and return [0, 1, 1, 0, 0]
    measr(inputs)
}

### Deutsch-Jozsa Algorithm

Implementing of Deutsch-Jozsa as an application of phase kickback phenomenon:

```rust
unitary fn prepare_minus(q: qbit) -> qbit {
    let q = X(q);
    let q = H(q);
    q
}

// U_f : |x⟩|y⟩ ↦ |x⟩|y ⊕ f(x)⟩
uncompsafe fn balanced_reversible_oracle(
    qs: [qbit; 4],
    target: qbit
) -> ([qbit; 4], qbit)
        requires basis(target, X)
        ensures  basis(target, X)
        ensures  product(target, qs) {
    ctrl(&qs[0]).on(bs"0").apply(X)(&target);
    ctrl(&qs[1]).on(bs"1").apply(X)(&target);
    ctrl(&qs[2]).on(bs"0").apply(X)(&target);
    ctrl(&qs[3]).on(bs"1").apply(X)(&target);
    (qs, target)
}

general fn phase_kickback(
    qs: [qbit; 4],
    oracle: uncompsafe fn(qs: [qbit; 4], target: qbit) -> ([qbit; 4], qbit)
        requires basis(target, X)
        ensures basis(target, X)
        ensures product(target, qs)
) -> [qbit; 4] {
    let ancilla = qalloc();
    let ancilla = prepare_minus(ancilla);
    let (qs, ancilla) = oracle(qs, ancilla);
    discard(ancilla);
    qs
}

general fn deutsch_jozsa(
    // contracts are inferred by the compiler
    oracle: uncompsafe fn(qs: [qbit; 4], target: qbit) -> ([qbit; 4], qbit)
) -> [bit; 4] {
    let qs = qalloc(4);

    for q in &qs {
        H(q);
    }

    // turn a bit-flip oracle into a phase oracle
    let qs = phase_kickback(qs, oracle);

    for q in &qs {
        H(q);
    }

    measr(qs)
}

general fn main() -> [bit; 4] {
    deutsch_jozsa(balanced_reversible_oracle)
}
```

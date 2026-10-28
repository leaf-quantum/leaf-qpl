### Recursion

Recursion does introduce a layer of complexity in a programming language and has consequences on what a programming language can and cannot do. For example the [principle of deferred measurement](defining-terms.md#what-is-principle-of-deferred-measurement) no longer applies automatically in the presence of recursion. A useful method to classify the effect of recursion is to use function effects:

(1) Purely classical recursion.
```leaf
classical fn fact(n: u32) -> u32 {
    if n == 0 { 1 } else { n * fact(n - 1) }
}
```

(2) Circuit-generating unitary recursion over a classical parameter, safe if total and structurally decreasing.
```leaf
unitary fn apply_hadamard_layer(qs: &[qbit]) {
    if qs.len() == 0 {
        return;
    }

    H(&qs[0]);
    
    apply_hadamard_layer(&qs[1..]);
}
```

(3) Classically controlled recursion. This can be mapped to OpenQasm3 while loops with mid-circuit measurements.
```leaf
general fn sample_until_zero() -> qbit {
    let q = qalloc();
    H(&q);
    let b = measr(&q);
    if b == 0 {
        return q;
    } else {
        discard(q);
        sample_until_zero()
    }
}
```

(4) Quantum controlled recursion.

Not yet supported.

(5) Recursive quantum types.

Not yet supported.

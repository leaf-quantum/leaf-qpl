### Control Gate Modifiers

Technically these are higher-order operators that change the way functions with quantum operations behave. Only `uncompsafe` and `unitary` functions can be controlled via apply() construct.

Canonical declaration:
```leaf
let (q0, q1, q2) = ctrl(q0, q1).apply(H)(q2);
```

... or with qubit borrowing syntax:
```leaf
ctrl(&q0, &q1).apply(H)(&q2);
```

... or equivalently using block syntax:
```leaf
ctrl(&q0, &q1) {
  H(&q2);
}
```

Controlling both $|0\rangle$ and $|1\rangle$:
```leaf
let (q0, q1, q2) = ctrl(q0, q1).on(bs"01").apply(H)(q2);

// or:

ctrl(&q0, &q1).on(bs"01").apply(H)(&q2);

// or:

ctrl(&q0, &q1).on(bs"01") {
  H(&q2);
}
```

Applying controls on a generic function and in a different basis:
```leaf
let (q0, q1, q2, q3) = ctrl(q0, q1).on(bs"+-").apply(f)(q2, q3);

// or:

ctrl(&q0, &q1).on(bs"+-").apply(f)(&q2, &q3);

// or:

ctrl(&q0, &q1).on(bs"+-") {
  f(&q2, &q3);
}
```

### Control Operator vs Control Block Expression

The control block expression applies the control operation to all unitary gates within the block expression and sub-expressions. It can be applied to blocks containing built-in unitary quantum gates and functions qualified with `classical`, `uncompsafe` or `unitary`, `isometry` or `coisometry` effects. On the other hand, the control function operator `ctrl().on().apply(f)` can be applied only to functions that declare control support in function signature as exemplified below.

### Declaring Control Support

Leaf has a special syntax for those functions where the compiler is able to infer that the function is controllable using the `supports` keyword combined with `ctrl`:

```leaf
unitary fn f(q: &qbit) supports ctrl {
    H(q);
}
```

Control and adjoint supports clauses can be combined:

```leaf
unitary fn f(q: &qbit) supports adjoint, ctrl {
    H(q);
}
```

A function that contains only unitary quantum gates can always be controlled and usually cannot when it measures, resets or discards qubits. Sometimes quantum code containing measure/reset/discard operations can be controlled as long as those operations are applied to qubits that are driven to a provable clean, all-zero, separable state. However, a function that returns classical data in general is usually not controllable since there is no general method to adjust classical output data for positive/negative control.

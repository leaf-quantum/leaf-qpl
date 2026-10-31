### Built-in Functions


[Qubit operations](quantum-data-operations.md#operations-on-qubits):
```leaf
qalloc(), measr(), discard(), reset(), uncompute(), weaken(), tensor()
```

[Quantum contracts](quantum-contracts.md#quantum-contracts):
```leaf
clean(), basis(), isolated(), product(), separable(), stabilized()
```

[Circuit operations](quantum-gates.md#barrier):
```leaf
barrier()
```

[Adjoint operations](adjoint-operator.md):
```leaf
adjoint()
```

[Control operations](control-modifiers.md):
```leaf
ctrl().on().apply()
```

Array, slice and range operations:
```leaf
len(), rev()
```

`len()` returns the number of elements of an array, a slice, or a reference to either, as a `u32`. For a fixed-size array `[T; N]` the length is part of the type, so the compiler knows the value statically:
```leaf
let a = [1, 2, 3];
let n = len(a);              // 3

for i in 0..len(a) {
    // do something with a[i]
}
```

`rev()` reverses a range, which is how a `for` loop counts down. It requires a range with both endpoints, so `rev(1..)` and `rev(..6)` are invalid:
```leaf
for i in rev(1..6) {
    // 5, 4, 3, 2, 1
}
```

Complex-valued phase() prelude function is often used as helper for quantum states specification:
```leaf
phase(1.23) = exp(i * 1.23);
```

The turns() prelude function translates floating point numbers representing fractions of 2π into angle type values:
```leaf
turns(0.25) = π/2;
```

Declaring angle parameters via Param() prelude built-in:
```leaf
Param()
```

Trigonometric prelude functions:
```leaf
cos(), acos(), sin(), asin(), tan(), atan()
```

Math utility prelude functions:
```leaf
abs(), exp(), ceil(), floor(), ln(), log2(), log10(), max(), min(), round(), sqrt()
```


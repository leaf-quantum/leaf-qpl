### Leaf Basic Types

(1) Quantum computing specific types:
```leaf
bit, qbit, qstate
```

where the `qbit` type is used for ordinary qubits to which gates can be applied:
```leaf
let q: qbit = H(q);
```

while the `qstate` is used for expression that declare quantum states like this:

```leaf
let plusAlias : qstate = 1/sqrt(2) * (zero + one);
let oneAlias  : qstate = 1/sqrt(2) * (plus - minus);
```

(2) Angle types: 32-bit or 64-bit floating-point values in the range [0, 2π)
```leaf
angle32, angle64
```

(3) Param type:
```leaf
let theta: param = Param("theta");
```

(4) Signed integer types:
```leaf
i8, i16, i32, i64, i128
```

(5) Unsigned integer types:
```leaf
u8, u16, u32, u64, u128
```

(6) Floating-point types:
```leaf
f32, f64
```

(7) Boolean type:
```leaf
bool
```

(9) Unit type:
```leaf
()
```

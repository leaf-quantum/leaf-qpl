### Function Attributes

By default, a quantum program written in Leaf is compiled as a flat OpenQASM file. Function attributes instruct the compiler to generate OpenQASM subroutines that correspond to functions in Leaf code, possibly generating more compact OpenQASM code. Two such attributes are currently supported: `qasm_gate` and `qasm_def` which are mutually exclusive. A function decorated with `qasm_gate` attribute is compiled to a `gate` unitary OpenQASM subroutine while a function decorated to `qasm_def` is compiled to a general `def` OpenQASM subroutine. Only functions with unitary, isometry and coisometry effects accept `qasm_gate` attribute. The attribute argument translates to OpenQASM routine name. If an attribute does not have a string argument, the function name is used instead for OpenQASM routine name, being interpreted as a default argument.

```leaf
#[qasm_gate]
unitary fn myfun(q: qbit) -> qbit {
  let q = H(q);
  q
}

#[qasm_gate("qasm_subroutine_name")]
unitary fn myfun(q: qbit) -> qbit {
  let q = H(q);
  q
}

#[qasm_def]
general fn myfun(q: qbit) -> bit {
  let q = H(q);
  measr(q)
}

#[qasm_def("qasm_subroutine_name")]
general fn myfun(q: qbit) -> bit {
  let q = H(q);
  measr(q)
}
```


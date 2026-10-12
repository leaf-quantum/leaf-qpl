
### Features Pending Implementation

This document compiles a list of features which are covered by the [language documentation](README.md) but not yet planned for the alpha release.

Higher priority:

- Modules, resolve imports, cycle detection, shadowing.
- Lean 4 code generation.
- Uncomputation support.
- `affine` & `scratch` qubits.
- Quantum contracts.
- Support for mutable variables.

Other:

- Quantum Boolean data and Boolean coherent operations.
- Signed/unsigned quantum integers and quantum arithmetic.
- Arrays, tuples formed from the 3 above must work.
- Quantum conditionals.
  - `qif`+`qelse` & `qmatch`.
  - `sif`+`selse` & `smatch`.
- Sum & Product data types:
  - `enum`
  - `qenum`
  - `struct` + `impl` blocks.
- Rust style slices.
- Recursion.
- Recursive data structures.
- Documentation comments.
- Classical subroutines.



### Features Pending Implementation

This document compiles a list of features which are covered by the [language documentation](README.md) but not yet planned for the alpha release.

Higher priority:

- Lean 4 code generation.
- Modules and imports.
- Handle supports adjoint/ctrl function clauses.
- Support for adjoint() operation.
- Uncomputation support.
- `affine` & `scratch` qubits.
- Quantum contracts.
- Support for mutable variables.
- Classical subroutines & support in Lean.
- Quantum conditionals.
  - `qif`+`qelse` & `qmatch`.
  - `sif`+`selse` & `smatch`.
- Rust style built-in methods.

Other:

- Quantum Boolean data and Boolean coherent operations.
- Signed/unsigned quantum integers and quantum arithmetic.
- Signed/unsigned quantum floats and quantum operations.
- Arrays, tuples formed from the 3 above must work.
- Sum & Product data types:
  - `enum`
  - `qenum`
  - `struct` + `impl` blocks.
- Rust style slices.
- Recursion.
- Recursive data structures.
- Documentation comments.



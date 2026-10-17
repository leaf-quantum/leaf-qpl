<table align="center">
  <tr>
    <td td align="center">
      <img src="files/leaf.png" alt="Leaf" height="200">
    </td>
    <td style="vertical-align: middle;">
      <h2 style="margin: 0;">
        Write in Leaf, prove with Lean.<br/>
        Quantum Programming 🍃⚡ 
      </h2>
    </td>
  </tr>
</table>

<br/>

![Alpha](https://img.shields.io/badge/alpha-Fall_2026-orange)
[![Tests](https://github.com/radumarg/leaf-qpl/actions/workflows/test.yml/badge.svg)](https://github.com/radumarg/leaf-qpl/actions/workflows/test.yml)
[![Commit activity](https://img.shields.io/github/commit-activity/m/radumarg/leaf-qpl.svg)](https://github.com/radumarg/leaf-qpl/commits)
[![Issues](https://img.shields.io/github/issues/radumarg/leaf-qpl)](https://github.com/radumarg/leaf-qpl/issues)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](https://github.com/radumarg/leaf-qpl/blob/main/LICENSE)
[![Idris 2](https://img.shields.io/badge/Idris%202-v0.8.0-blue.svg)](https://github.com/idris-lang/Idris2/releases/tag/v0.8.0)
[![OpenQASM 3](https://img.shields.io/badge/target-OpenQASM%203-2c8ebb)](https://openqasm.com/)
[![Lean4](https://img.shields.io/badge/Lean4-theorem%20proving-6f42c1)](https://lean-lang.org/)
<!-- ![Development status: Alpha](https://img.shields.io/badge/development%20status-alpha-orange) -->

## About

* A statically typed quantum programming language with Rust-like syntax and conservative quantum extensions that preserve the look and feel of Rust.
* Linear qubit ownership and mutable borrowing: no-cloning and qubit-use discipline are enforced statically by the type checker.
* Safe ancilla management, with support for automatic uncomputation.
* Lightweight quantum contracts for tracking properties of entanglement for program qubits at compile time.
* Designed for formal verification, with program properties proved in Lean 4 against a type-safe intermediate representation.
* Detailed diagnostics designed for both human developers and AI-assisted code generation.
* Practical by construction: compiles to OpenQASM 3, with QIR support planned.
* Built for the fault-tolerant quantum computing era.

Code example:

```leaf
general fn coin_flip() -> bit {
    let q = qalloc();
    H(&q);
    measr(q)
}

general fn main() -> bit {
    coin_flip()
}
```

## Docs

[Documentation](docs/README.md)

## Progress Status

| Capability                    | Status      |
| ----------------------------  | ----------- |
| Language Design & Docs        | Implemented |
| Lexer                         | Implemented |
| Parser                        | Implemented |
| Surface AST                   | Implemented |
| Post-Parse Validation         | Implemented |
| De-sugaring & Canonical AST   | Implemented |
| Scope & Name Resolution       | Implemented |
| Type Checker & Typed AST      | In progress |
| Quantum Lambda Calculus IR    | Planned     |
| Lambda Calculus Code Generator| Planned     |
| Idris2 DSL                    | Protoype    |
| Idris DSL Lowering Pass       | Planned     |
| OpenQASM 3 Serializer         | Protoype    |
| Alpha release                 | Fall 2026   |
| Lean Interface                | Planned     |

## Todo

[Pending Features](docs/todo.md)

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for contribution guidelines.

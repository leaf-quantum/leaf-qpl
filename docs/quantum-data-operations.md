### Operations on Qubits

Qubit variables are by default linear, meaning that a qubit once declared must be used exactly once. Since qubits cannot be cloned, qubits in Leaf are mutable by default and there is no need to use the `mut` keyword to mark a qubit as such. Also, a reference to a qubit q is marked as `&q` without needing to specify that this is a mutable reference since this is the only option that is physically possible. The following operations on qubits are supported:

- Allocating qubits (output type can be inferred):
```leaf
let q: qbit = qalloc();
let qs: [qbit; 2] = qalloc(2);
```

- Measuring qubits (result type can be inferred), the qubit variable(s) is consumed and cannot be reused:
```leaf
let b : bit = measr(q);
let (b1, b2, b3): (bit, bit, bit) = measr(q1, q2, q3);
let bs = measr(qs);
```

- Measuring borrowed qubits makes the qubit variable(s) usable later in the program:
```leaf
let b : bit = measr(&q);
let bs: [bit; 3] = measr(&q1, &q2, &q3);
let bs = measr(&qs);
```

- Unlike a linear qubit which must be used `exactly once`, an affine qubit must be used `at most once`. Downgrading qubit type from `linear` to `affine`:
```leaf
let q = weaken(q);
let (q1, q2, q3) = weaken(q1, q2, q3);
let qs = weaken(qs);
```

- Resetting qubits:
```leaf
let q = reset(q);
let (q1, q2, q3) = reset(q1, q2, q3);
let qs = reset(qs);

//or:

reset(&q);
reset(&q1, &q2, &q3);
reset(&qs);
```

- Discarding it is one way to use a qubit at the programmatic level, without actually performing any physical operation on the corresponding physical qubit. At the level of physical qubits this means allowing the qubits to dissipate. Programmatically this means: I will never use this qubit again, and I do not care what its state is. Semantically, discarding a qubit means taking a partial trace over that qubit. The remaining qubits are described by their reduced density matrix:
  - if the qubit is not entangled: $|\psi\rangle = |+\rangle_{q} \otimes |\phi\rangle_{r}$ and you discard $q$, the rest of the system remains exactly $|\phi\rangle_{r}$. No harm is done to the remaining qubits.
  - if the qubit is entangled: $\frac{1}{\sqrt{2}} \left( \lvert 00 \rangle + \lvert 11 \rangle \right)$ and you discard the first qubit, the second qubit becomes $\frac{1}{2}\left(|0\rangle\langle 0| + |1\rangle\langle 1|\right)$. That is, it becomes a mixed state, not a pure state. The quantum coherence between the branches is lost from the perspective of the remaining program state. Discarding an entangled qubit leaks quantum information into the environment and can decohere the remaining qubits in the program.

```leaf
discard(q);
discard(q1, q2, q3);
discard(qs);
```

- Automatic [uncomputation](defining-terms.md#what-does-uncomputation-mean), works only over circuits generated with `uncompsafe` functions:
```leaf
let q = uncompute(q);
let (q1, q2, q3) = uncompute(q1, q2, q3);
let qs = uncompute(qs);

//or:

uncompute(&q);
uncompute(&q1, &q2, &q3);
uncompute(&qs);
```

- Tensor product for state expressions - $|1\rangle \otimes |1\rangle$:
```leaf
let sq1: qstate = one;
let sq2: qstate = one;
let sq: [qstate; 2] = sq1.tensor(sq2);
```

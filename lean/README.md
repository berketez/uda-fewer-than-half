# Lean 4 formalization

This directory contains machine-checked proofs, in Lean 4 with Mathlib, of the main results of the
paper. Everything listed under "What is proved" compiles with no `sorry`, no custom axiom and no
`native_decide`; each theorem depends only on the three standard axioms of Mathlib.

## What is proved

**Theorem 1 (measure one), complete.** For Haar-almost every `n`-qubit pure state `ψ` (almost every
point of the unit sphere of `ℂ^(2^n)` for the uniform measure), `ψ` is uniquely determined among all
pure and mixed states by its reduced density matrices on all `K`-element sets of qubits, and `ψ` is
the unique zero-energy ground state of a positive semidefinite `K`-local Hamiltonian, where

| Statement | `K` | Range |
|---|---|---|
| `MainStatement` | `⌈n/2⌉ − 1` (fewer than half of the qubits) | every `n ≥ 139` |
| `Thm1FourTenths` | `⌈0.4 n⌉` | every `n ≥ 996` |
| `Thm1Kappa` | `⌈2 κ_c n + 4 log₂ n⌉` | every `n ≥ 274` |
| `Thm1Asymptotic` | `2 κ_c n + O(log n)` | all large `n` |

`KappaCStatement`: the constant `κ_c` (the root of `h₂(κ) + κ log₂ 3 = 1` in `(0, 1/2)`) exists, is
unique, and `0.1892896 < κ_c < 0.1892897`.

**Failure of the Jones–Linden lower bound.**
- `JonesLindenFails`: for every `N ≥ 139` there is `K < N/2` such that the `K`-UDA states have
  positive measure and their complement has measure zero.
- `JonesLindenFailsSmall`: the `K`-UDA states have positive measure for `(N, K) = (8, 3)` (so
  `K < N/2`) and for `(4, 2)`, `(6, 3)` (so `K = ⌊N/2⌋`).

**Lemmas of the paper.**
- `Lemma1Statement` (Lemma 1): complex spanning `C(L)` ⇒ `(2L+1)`-UDA and unique ground state.
- `GenericityStatement` (Lemma 2, genericity): `C(c)` at one vector ⇒ at almost every state.
- `Lemma3Statement` (Lemma 3): the covering condition ⇒ almost every state is `(2(L+t)+1)`-UDA.
- `PropTopStatement`: a simple top eigenvector of a real `K`-local Hamiltonian is `K`-UDA.
- `LemmaAStatement` (Lemma A): a certificate `S(n, K)` at one state gives a nonempty open set of
  states with a certificate `S(n, K)`.

**Theorem 3, small cases.** `Thm3Small`: for `(n, K) = (4, 2), (6, 3), (8, 3)` there is a nonempty
open set of `K`-UDA pure states. (Proved through the gluing route of the paper: product with `|0⟩`,
generic upgrade, and kernel-checked graph-state witnesses of `C(c)`; not through the floating-point
hinted certificates.)

**Theorem 2 (i), upper bound.** `Thm2Upper`: for some `C` and all large `n` there is
`K ≤ κ_c n + C log n` with a nonempty open set of `K`-UDA states.

## Check it yourself

Install [elan](https://github.com/leanprover/elan) (the Lean version manager), then:

```bash
cd lean
lake exe cache get     # downloads the precompiled Mathlib v4.35.0 (a few GB)
lake build             # compiles the formalization (a few minutes)
```

The build prints the axioms of each main theorem. Expected output (14 lines):

```
'UDA.mainStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'UDA.jonesLindenFails' depends on axioms: [propext, Classical.choice, Quot.sound]
'UDA.lemma1Statement' depends on axioms: [propext, Classical.choice, Quot.sound]
'UDA.genericityStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'UDA.lemma3Statement' depends on axioms: [propext, Classical.choice, Quot.sound]
'UDA.kappaCStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'UDA.thm1FourTenths' depends on axioms: [propext, Classical.choice, Quot.sound]
'UDA.thm1Kappa' depends on axioms: [propext, Classical.choice, Quot.sound]
'UDA.thm1Asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound]
'UDA.propTopStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'UDA.lemmaAStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'UDA.thm3Small' depends on axioms: [propext, Classical.choice, Quot.sound]
'UDA.thm2Upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'UDA.jonesLindenFailsSmall' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The finite computations (parameter tables for the thresholds, a few binomial inequalities, covering
radii of small graph states) are checked by the Lean kernel itself (`decide +kernel`). Lake also
prints one generic note, that `UDA/Defs.lean` imports Mathlib without using Lean's new `module`
system; it is harmless.

Size: 27 files, about 5,000 lines, about 300 theorems and lemmas.

## What to read

The statements are in five short files. Everything else is proof.

| File | Content |
|---|---|
| `UDA/Defs.lean` | Qubit basis, Pauli operators `X^x Z^z`, weight, density matrices, marginals (partial traces), `IsUDA`, `IsUGS`, the spanning condition `C(c)`, Lagrangian subspaces. |
| `UDA/Defs2.lean` | Hermitian Pauli strings, real `K`-local Hamiltonians, simple top eigenvectors, the real spanning condition `R(K)`, the certificate condition `S(n, K)`. |
| `UDA/Statement.lean`, `Statement2.lean`, `Statement3.lean` | The theorems as propositions. These files import only the definitions, so the proof files cannot change what the statements mean. |
| `UDA/Main.lean`, `UDA/Main2.lean` | Prove the propositions of the statement files and print their axioms. |

"Haar-almost every pure state" is formalized as "almost every point of the unit sphere of
`ℂ^(2^n)` for the uniform sphere measure" (`(volume : Measure (StateSpace n)).toSphere`).
`IsUDA n K` is meaningful for `K ≤ n` (for `K > n` there are no `K`-element sets of qubits).

## Proof files

| File | Paper | Content |
|---|---|---|
| `Pauli.lean` | — | Algebra of `X^x Z^z`: products, adjoints, commutation, traces, weights. |
| `Marginal.lean` | Sec. 2 | Equal `K`-body marginals ⇒ equal expectations of Paulis of weight `≤ K`. |
| `Lemma1.lean` | Lemma 1 | Annihilators, sum of squares, commutant argument. |
| `Ball.lean` | — | `#{weight ≤ L} = Σ_{j≤L} C(m,j) 3^j`. |
| `Covering.lean` | Lemma 3, steps 1–4 | A Lagrangian subspace with covering radius `≤ L + t` exists. |
| `Stabilizer.lean` | Lemma 2 | Covering radius `≤ R` ⇒ `C(R)` at a stabilized state. |
| `Generic.lean` | Lemma 2 (genericity) | Zero sets of nonzero complex polynomials are null; sphere measure. |
| `Thresholds.lean` | Table "Thresholds of Theorem 1" | Half threshold: kernel table for `139 ≤ n ≤ 268`, tail for `n ≥ 269`. |
| `Entropy.lean`, `Kappa.lean` | Sec. "Constants" | Entropy lower bound for a ball term; existence, uniqueness and value of `κ_c`. |
| `Thresholds2.lean`, `Thm1Rest.lean` | Table "Thresholds of Theorem 1" | `⌈0.4n⌉` (kernel table `996 ≤ n ≤ 1330`, tail), `⌈2κ_c n + 4 log₂ n⌉`, asymptotic form. |
| `TopEig.lean` | Proposition "simple top eigenvector" | Gapped top eigenvector ⇒ UDA. |
| `LemmaA.lean` | Lemma A | Certificate to open set. |
| `Witness.lean` | Table of generic `C(b, c)` witnesses (small `b`) | Graph states with covering radius 1 (`n = 2, 3`) and 2 (`n = 4, …, 7`). |
| `Gluing.lean` | Lemma B (case `ψ₂ = |0⟩`), generic upgrade | Data `(K_H, r, c)`, product with `|0⟩`, upgrade. |
| `Thm3.lean` | Theorem 3 | Chains for `(4,2)`, `(6,3)`, `(8,3)`. |
| `T2Wit.lean`, `T2Ind.lean`, `Thm2.lean` | Theorem 2′, Theorem 2 (i) | Witness orders `≈ κ_c m + O(log m)`, induction, upper bound. |

**Differences from the paper.**
- Lemma 3, step 1: the paper picks a uniform random Lagrangian subspace and uses Chebyshev's
  inequality. The formalization uses "graph-state" Lagrangians `{(x, Ax)}` with `A` symmetric over
  `𝔽₂` and a Cauchy–Schwarz counting argument, which avoids counting Lagrangian subspaces. The
  resulting condition, `(2^m + B_m(L))^(2^t) > 2^(m(2^t+2))`, is implied by the paper's condition
  `(*)`; the half threshold is the same (`139`; it fails at `138`).
- Lemma 2: only isotropy of the subspace is used (a common eigenvector of the commuting Paulis).
- Lemma A is proved by solving the eigen-equation linearly in the Hamiltonian (Cramer's rule) rather
  than through the derivative of the eigenvector map.
- The small cases of Theorem 3 use stabilizer (graph-state) witnesses of `C(c)` instead of the
  finite-field rank witnesses of the paper.

## What is not formalized

- Theorem 3 for `(10, 4)` and `(12, 4)`, the exact `S`/`C`/`R` certificates, and the finite-field
  witnesses for `b ≥ 9`: these involve matrices of size `2^9` to `2^13`, beyond what the Lean kernel
  can check in reasonable time. They are checked by the verifiers in `../verification/`.
- Theorem 2 (ii), the explicit bound `(3n+24)/13`, and the proposition `n ≥ 83` (both rest on the
  13-qubit witness).
- The lower bounds: the counting proposition (`K*₊(n) ≥ K_count(n) > κ_c n`) and hence the lower
  half of Theorem 2 (i); the non-UDA open sets of the Observation (uniform states).
- The general Lemma B and Lemma B′ (only the product with `|0⟩` is formalized).

## Toolchain

Lean `v4.35.0`, Mathlib `v4.35.0` (commit `56a005855ea17e0b0958f73ec801ae140b0a1679`), pinned in
`lean-toolchain` and `lake-manifest.json`.

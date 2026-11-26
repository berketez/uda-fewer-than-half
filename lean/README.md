# Lean 4 formalization

This directory contains a machine-checked proof, in Lean 4 with Mathlib, of the main theorem of the
paper (Theorem 1, half threshold):

> For every `n ≥ 139`, Haar-almost every `n`-qubit pure state is uniquely determined, among all
> pure and mixed states, by its reduced density matrices on all `⌈n/2⌉ − 1`-element sets of
> qubits (fewer than half of the qubits), and it is the unique ground state, with energy zero,
> of a positive semidefinite `(⌈n/2⌉ − 1)`-local Hamiltonian.

In particular, the Jones–Linden lower-bound statement ("the marginals of fewer than `N/2` parties
are insufficient for almost all states") fails for qubits for every `N ≥ 139`.

## Check it yourself

Install [elan](https://github.com/leanprover/elan) (the Lean version manager), then:

```bash
cd lean
lake exe cache get     # downloads the precompiled Mathlib v4.35.0 (a few GB)
lake build             # compiles the formalization (a few minutes)
```

The build prints the axioms that each main theorem depends on. Expected output:

```
'UDA.mainStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'UDA.jonesLindenFails' depends on axioms: [propext, Classical.choice, Quot.sound]
'UDA.lemma1Statement' depends on axioms: [propext, Classical.choice, Quot.sound]
'UDA.genericityStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'UDA.lemma3Statement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the three standard axioms of Lean's mathematics library. There is no `sorry`, no
custom axiom, and no `native_decide`. The finite computations (the parameter table for
`139 ≤ n ≤ 268` and one binomial inequality) are checked by the Lean kernel itself
(`decide +kernel`). With the Mathlib cache in place the build takes about one to two minutes.
Lake also prints one generic note, that `UDA/Defs.lean` imports Mathlib without using Lean's
new `module` system; it is harmless.

Size: 11 files, about 2,500 lines, 159 theorems and lemmas.

## What to read

The statements are in two short files. Everything else is proof.

| File | Content |
|---|---|
| `UDA/Defs.lean` | All definitions: qubit basis, Pauli operators `X^x Z^z`, weight, density matrices, marginals (partial traces), `IsUDA`, `IsUGS`, the spanning condition, Lagrangian subspaces. |
| `UDA/Statement.lean` | The theorems as propositions (`MainStatement`, `JonesLindenFails`, `Lemma1Statement`, `GenericityStatement`, `Lemma3Statement`). This file imports only `Defs`, so the proof files cannot change what the statements mean. |
| `UDA/Main.lean` | Proves the propositions of `Statement.lean` and prints their axioms. |

"Haar-almost every pure state" is formalized as "almost every point of the unit sphere of
`ℂ^(2^n)` for the uniform sphere measure" (`(volume : Measure (StateSpace n)).toSphere`).

## How the proof is organized

| File | Paper | Content |
|---|---|---|
| `UDA/Pauli.lean` | — | Algebra of `X^x Z^z`: products, adjoints, commutation, traces, weights. |
| `UDA/Marginal.lean` | Sec. 2 | Equal `K`-body marginals ⇒ equal expectations of all Paulis of weight `≤ K`. |
| `UDA/Lemma1.lean` | Lemma 1 | Complex spanning `C(L)` ⇒ `(2L+1)`-UDA and unique zero-energy ground state (annihilators, sum of squares, commutant argument). |
| `UDA/Ball.lean` | — | `#{weight ≤ L} = Σ_{j≤L} C(m,j) 3^j`. |
| `UDA/Covering.lean` | Lemma 3, steps 1–4 | Existence of a Lagrangian subspace with covering radius `≤ L + t`. |
| `UDA/Stabilizer.lean` | Lemma 2 | Covering radius `≤ R` ⇒ the stabilizer state satisfies `C(R)`. |
| `UDA/Generic.lean` | Lemma 2 (genericity) | `C(c)` at one vector ⇒ at almost every state (zero sets of nonzero complex polynomials are null). |
| `UDA/Thresholds.lean` | Table "Thresholds of Theorem 1" | Parameters for every `n ≥ 139`: kernel-checked table for `139 ≤ n ≤ 268`, analytic tail for `n ≥ 269`. |

**One difference from the paper.** Step 1 of Lemma 3 in the paper picks a *uniform random*
Lagrangian subspace and uses Chebyshev's inequality. The formalization uses "graph-state"
Lagrangians `{(x, Ax)}` with `A` a random symmetric matrix over `𝔽₂` and a Cauchy–Schwarz
counting argument instead, which avoids counting Lagrangian subspaces. The resulting condition,
`(2^m + B_m(L))^(2^t) > 2^(m(2^t+2))`, is implied by the paper's condition `(*)`, and with the
paper's parameter choice it gives the same threshold: it holds for every `n ≥ 139` and fails at
`n = 138`.

## What is not formalized

Only Theorem 1 at the half threshold, together with Lemmas 1–3 and genericity, is formalized.
**Not** formalized:
- the other explicit thresholds of Theorem 1 (`⌈0.4n⌉` for `n ≥ 996`, `⌈2κ_c n + 4 log₂ n⌉` for
  `n ≥ 274`) and the asymptotic form `K(n) = 2κ_c n + O(log n)`;
- Theorem 2 (positive-measure threshold), Theorem 3 (finite certificates), the gluing lemmas, and
  the counting proposition (lower bound).

The exact certificates behind Theorems 2–3 are checked separately by the verifiers in
`../verification/`.

## Toolchain

Lean `v4.35.0`, Mathlib `v4.35.0` (commit `56a005855ea17e0b0958f73ec801ae140b0a1679`), pinned in
`lean-toolchain` and `lake-manifest.json`.

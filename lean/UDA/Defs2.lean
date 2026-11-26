import UDA.Defs

/-!
# Further definitions (Theorems 2–3 and the certificate language)

Hermitian Pauli strings, real `K`-local Hamiltonians, simple top eigenvectors, the real spanning
condition `R(K)` and the certificate condition `S(n, K)` of the paper.
-/

open Matrix
open scoped ComplexOrder

namespace UDA

/-- Number of qubits on which a label acts as `Y` (both bits set). -/
def ycount {n : ℕ} (p : PL n) : ℕ :=
  (Finset.univ.filter fun j => p.1 j ≠ 0 ∧ p.2 j ≠ 0).card

/-- The Hermitian Pauli string with label `p`: `i^(#Y) X^x Z^z`, a tensor product of
`I, X, Y, Z` factors. -/
noncomputable def hpauli {n : ℕ} (p : PL n) : Matrix (Idx n) (Idx n) ℂ :=
  (Complex.I ^ ycount p) • pauli p

/-- Real `K`-local Hamiltonians: real linear combinations of Hermitian Pauli strings of weight
at most `K`. -/
noncomputable def realLocalOps (n K : ℕ) : Submodule ℝ (Matrix (Idx n) (Idx n) ℂ) :=
  Submodule.span ℝ {M | ∃ p : PL n, wt p ≤ K ∧ M = hpauli p}

/-- `ψ` is an eigenvector of `H` for an eigenvalue `E` that is the largest and simple: `H` is
strictly below `E` on the orthogonal complement of `ψ`. -/
def IsGappedTop {n : ℕ} (H : Matrix (Idx n) (Idx n) ℂ) (ψ : Idx n → ℂ) : Prop :=
  ∃ E : ℝ, H *ᵥ ψ = (E : ℂ) • ψ ∧
    ∀ v : Idx n → ℂ, v ≠ 0 → star v ⬝ᵥ ψ = 0 →
      (star v ⬝ᵥ (H *ᵥ v)).re < E * (star v ⬝ᵥ v).re

/-- The real spanning condition `R(K)`: the vectors `P ψ` (Hermitian Paulis of weight `≤ K`,
identity included) together with `i ψ` span `ℂ^(2^n)` over `ℝ`. -/
def SpanR (n K : ℕ) (ψ : Idx n → ℂ) : Prop :=
  Submodule.span ℝ ({v | ∃ p : PL n, wt p ≤ K ∧ v = hpauli p *ᵥ ψ} ∪ {Complex.I • ψ}) = ⊤

/-- The certificate condition `S(n, K)` at `(H, ψ)`: `H` is a real `K`-local Hamiltonian,
`ψ` is its simple top eigenvector, and `R(K)` holds at `ψ`. -/
def CertS (n K : ℕ) (H : Matrix (Idx n) (Idx n) ℂ) (ψ : Idx n → ℂ) : Prop :=
  H ∈ realLocalOps n K ∧ IsGappedTop H ψ ∧ SpanR n K ψ

end UDA

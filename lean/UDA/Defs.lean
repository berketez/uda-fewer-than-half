import Mathlib

/-!
# Definitions

Formal verification of the main theorem of

  B. Tezgöçen, *Pure qubit states determined by marginals on fewer than half of the qubits:
  a measure-one bound and a correction to the Jones–Linden lower bound* (2026).

This file fixes every definition that appears in the statement of the main theorem
(`UDA.main_half` in `UDA/Main.lean`). Nothing here is proved; the other files only add
lemmas about these definitions.

Conventions.
* `n` qubits; computational-basis states are bit strings `b : Fin n → ZMod 2`.
* A phase-free Pauli label is a pair `(x, z)` of bit strings; it stands for the operator
  `X^x Z^z`, which sends `|b⟩` to `(-1)^(z·b) |b + x⟩`. Up to a phase every Pauli string
  is of this form, and `X^x Z^z` is a phase times the Hermitian Pauli string with the
  same support.
* The weight of a label is the number of qubits on which it acts nontrivially.
-/

open Matrix
open scoped ComplexOrder

namespace UDA

/-- Computational-basis labels of `n` qubits (bit strings). -/
abbrev Idx (n : ℕ) := Fin n → ZMod 2

/-- Phase-free Pauli labels `(x, z) ∈ 𝔽₂ⁿ × 𝔽₂ⁿ`, standing for `X^x Z^z`. -/
abbrev PL (n : ℕ) := (Fin n → ZMod 2) × (Fin n → ZMod 2)

/-- The symplectic form on Pauli labels: `X^x Z^z` and `X^x' Z^z'` commute iff it vanishes. -/
def symp {n : ℕ} (p q : PL n) : ZMod 2 := ∑ j, (p.1 j * q.2 j + p.2 j * q.1 j)

/-- Weight of a Pauli label: number of qubits on which it acts nontrivially. -/
def wt {n : ℕ} (p : PL n) : ℕ := (Finset.univ.filter fun j => p.1 j ≠ 0 ∨ p.2 j ≠ 0).card

/-- The sign `(-1)^t` of a bit `t`, as a complex number. -/
def sgn (t : ZMod 2) : ℂ := if t = 0 then 1 else -1

/-- Dot product of bit strings over `𝔽₂`. -/
def bdot {n : ℕ} (a b : Fin n → ZMod 2) : ZMod 2 := ∑ j, a j * b j

/-- The Pauli operator `X^x Z^z` on `n` qubits: `|b⟩ ↦ (-1)^(z·b) |b + x⟩`.
Matrix entry `(a, b)` is the coefficient of `|a⟩` in the image of `|b⟩`. -/
def pauli {n : ℕ} (p : PL n) : Matrix (Idx n) (Idx n) ℂ :=
  fun a b => if a = b + p.1 then sgn (bdot p.2 b) else 0

/-- The projector `|ψ⟩⟨ψ|`. -/
def proj {n : ℕ} (ψ : Idx n → ℂ) : Matrix (Idx n) (Idx n) ℂ :=
  Matrix.vecMulVec ψ (star ψ)

/-- Density matrices: positive semidefinite with unit trace. -/
def IsDensity {n : ℕ} (ρ : Matrix (Idx n) (Idx n) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- The reduced density matrix (marginal) of `ρ` on the qubits in `A`, i.e. the partial
trace over the complement of `A`: entry `(i, j)` is the sum of `ρ a b` over all basis
states `a, b` that restrict to `i, j` on `A` and agree outside `A`. -/
def marginal {n : ℕ} (ρ : Matrix (Idx n) (Idx n) ℂ) (A : Finset (Fin n)) :
    Matrix (A → ZMod 2) (A → ZMod 2) ℂ :=
  fun i j => ∑ a : Idx n, ∑ b : Idx n,
    if (∀ l : A, a l = i l) ∧ (∀ l : A, b l = j l) ∧ (∀ l : Fin n, l ∉ A → a l = b l)
    then ρ a b else 0

/-- `ψ` is *uniquely determined among all states* by its `K`-body marginals (`K`-UDA):
every density matrix with the same marginals as `|ψ⟩⟨ψ|` on all `K`-element sets of
qubits equals `|ψ⟩⟨ψ|`. -/
def IsUDA (n K : ℕ) (ψ : Idx n → ℂ) : Prop :=
  ∀ ρ : Matrix (Idx n) (Idx n) ℂ, IsDensity ρ →
    (∀ A : Finset (Fin n), A.card = K → marginal ρ A = marginal (proj ψ) A) →
    ρ = proj ψ

/-- Pauli-expectation form of `K`-UDA (used in the proofs). -/
def IsUDAPauli (n K : ℕ) (ψ : Idx n → ℂ) : Prop :=
  ∀ ρ : Matrix (Idx n) (Idx n) ℂ, IsDensity ρ →
    (∀ p : PL n, wt p ≤ K → (ρ * pauli p).trace = (proj ψ * pauli p).trace) →
    ρ = proj ψ

/-- `K`-local operators: the complex span of the Pauli operators of weight at most `K`. -/
def localOps (n K : ℕ) : Submodule ℂ (Matrix (Idx n) (Idx n) ℂ) :=
  Submodule.span ℂ {M | ∃ p : PL n, wt p ≤ K ∧ M = pauli p}

/-- `ψ` is the unique ground state, with energy zero, of a positive semidefinite
`K`-local Hamiltonian `G` (its kernel is exactly the line through `ψ`). -/
def IsUGS (n K : ℕ) (ψ : Idx n → ℂ) : Prop :=
  ∃ G ∈ localOps n K, G.PosSemidef ∧ ∀ v : Idx n → ℂ, G *ᵥ v = 0 ↔ ∃ c : ℂ, v = c • ψ

/-- The complex spanning condition `C(c)`: the vectors `P ψ`, `P` a Pauli of weight at
most `c`, span the whole space. -/
def SpanC (n c : ℕ) (ψ : Idx n → ℂ) : Prop :=
  Submodule.span ℂ {v | ∃ p : PL n, wt p ≤ c ∧ v = pauli p *ᵥ ψ} = ⊤

/-- A Lagrangian subspace of `𝔽₂²ⁿ`: isotropic for `symp`, with `2^n` elements. -/
def IsLagrangian {n : ℕ} (S : Submodule (ZMod 2) (PL n)) : Prop :=
  (∀ u ∈ S, ∀ v ∈ S, symp u v = 0) ∧ Nat.card S = 2 ^ n

/-- Covering radius at most `R`: every coset `v + S` contains a label of weight `≤ R`. -/
def CoversWithin {n : ℕ} (S : Submodule (ZMod 2) (PL n)) (R : ℕ) : Prop :=
  ∀ v : PL n, ∃ s ∈ S, wt (v + s) ≤ R

/-- Number of Pauli labels of weight at most `L` on `m` qubits. -/
def ballCard (m L : ℕ) : ℕ :=
  (Finset.univ.filter fun p : PL m => wt p ≤ L).card

/-- Closed form of `ballCard`: `∑_{j ≤ L} C(m, j) 3^j`. -/
def ballSum (m L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (L + 1), m.choose j * 3 ^ j

/-- The state space `ℂ^(2^n)` with its Euclidean (Hilbert-space) structure. Haar-random
pure states correspond to the uniform measure `(volume : Measure (StateSpace n)).toSphere`
on its unit sphere. -/
abbrev StateSpace (n : ℕ) := EuclideanSpace ℂ (Idx n)

end UDA

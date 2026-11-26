import UDA.Defs

/-!
# The statements being verified

This file imports only `UDA.Defs` (and Mathlib), so the meaning of the statements below is
fixed here and cannot be affected by anything in the proof files. `UDA/Main.lean` proves
exactly these propositions.
-/

open MeasureTheory
open scoped ComplexOrder

namespace UDA

/-- **Theorem 1 of the paper, half threshold.** For every `n ≥ 139`, Haar-almost every
`n`-qubit pure state `ψ` (almost every point of the unit sphere of `ℂ^(2^n)` for the uniform
measure) satisfies, with `K = ⌈n/2⌉ - 1` (fewer than half of the qubits):
* `ψ` is uniquely determined, among all pure and mixed states, by its reduced density
  matrices on all `K`-element sets of qubits;
* `ψ` is the unique ground state, with energy zero, of a positive semidefinite `K`-local
  Hamiltonian. -/
def MainStatement : Prop :=
  ∀ n : ℕ, 139 ≤ n →
    ∀ᵐ (ψ : Metric.sphere (0 : StateSpace n) 1) ∂(volume : Measure (StateSpace n)).toSphere,
      IsUDA n ((n + 1) / 2 - 1) (ψ : StateSpace n).ofLp ∧
        IsUGS n ((n + 1) / 2 - 1) (ψ : StateSpace n).ofLp

/-- **Failure of the Jones–Linden lower bound.** Jones and Linden (2005) assert that marginals
of fewer than `N/2` parties are insufficient for almost all states, i.e. that the `K`-UDA states
form a null set for `K < N/2`. For qubits and every `N ≥ 139` the opposite holds: there is
`K < N/2` such that the `K`-UDA states have positive measure and their complement has measure
zero. -/
def JonesLindenFails : Prop :=
  ∀ n : ℕ, 139 ≤ n →
    ∃ K : ℕ, 2 * K < n ∧
      0 < (volume : Measure (StateSpace n)).toSphere
        {ψ | IsUDA n K (ψ : StateSpace n).ofLp} ∧
      (volume : Measure (StateSpace n)).toSphere
        {ψ | ¬ IsUDA n K (ψ : StateSpace n).ofLp} = 0

/-- **Lemma 1 of the paper.** If the vectors `P ψ` (Paulis `P` of weight at most `L`) span the
whole space, then the unit vector `ψ` is `(2L+1)`-UDA and the unique zero-energy ground state
of a positive semidefinite `(2L+1)`-local Hamiltonian. -/
def Lemma1Statement : Prop :=
  ∀ (n L : ℕ) (ψ : Idx n → ℂ), star ψ ⬝ᵥ ψ = 1 → SpanC n L ψ →
    IsUDAPauli n (2 * L + 1) ψ ∧ IsUGS n (2 * L + 1) ψ

/-- **Genericity (Lemma 2 of the paper, second part).** If `C(c)` holds at one vector, it holds
at Haar-almost every pure state. -/
def GenericityStatement : Prop :=
  ∀ (n c : ℕ), (∃ ψ₀ : Idx n → ℂ, SpanC n c ψ₀) →
    ∀ᵐ (ψ : Metric.sphere (0 : StateSpace n) 1) ∂(volume : Measure (StateSpace n)).toSphere,
      SpanC n c (ψ : StateSpace n).ofLp

/-- **Lemma 3 of the paper (covering with few extra qubits), in the form used here.** If
`(2^m + B_m(L))^(2^t) > 2^(m(2^t+2))`, where `B_m(L) = ∑_{j ≤ L} C(m,j) 3^j`, then
Haar-almost every `(m+t)`-qubit pure state is `(2(L+t)+1)`-UDA. (`IsUDA n K` is only meaningful
for `K ≤ n`: for `K > n` there are no `K`-element sets of qubits, so the order is assumed to be
at most the number of qubits.) -/
def Lemma3Statement : Prop :=
  ∀ m t L : ℕ, 2 * (L + t) + 1 ≤ m + t →
    2 ^ (m * (2 ^ t + 2)) < (2 ^ m + ballSum m L) ^ (2 ^ t) →
    ∀ᵐ (ψ : Metric.sphere (0 : StateSpace (m + t)) 1)
        ∂(volume : Measure (StateSpace (m + t))).toSphere,
      IsUDA (m + t) (2 * (L + t) + 1) (ψ : StateSpace (m + t)).ofLp

end UDA

import UDA.Defs2

/-!
# Statements of the remaining results

Like `UDA/Statement.lean`, this file imports only definitions, so the meaning of the statements
is fixed here.
-/

open MeasureTheory Filter
open scoped ComplexOrder

namespace UDA

/-! ## The constant `κ_c` -/

/-- `κ` is the constant `κ_c` of the paper: the root in `(0, 1/2)` of
`h₂(κ) + κ log₂ 3 = 1`. In natural units this is `qaryEntropy 4 κ = log 2`, where
`qaryEntropy 4 κ = κ log 3 − κ log κ − (1 − κ) log (1 − κ)` (Mathlib's `Real.qaryEntropy`). -/
def IsKappaC (κ : ℝ) : Prop :=
  0 < κ ∧ κ < 1 / 2 ∧ Real.qaryEntropy 4 κ = Real.log 2

/-- `κ_c` exists, is unique, and `0.1892896 < κ_c < 0.1892897`. -/
def KappaCStatement : Prop :=
  (∃! κ : ℝ, IsKappaC κ) ∧
    ∀ κ : ℝ, IsKappaC κ → (0.1892896 : ℝ) < κ ∧ κ < 0.1892897

/-! ## Theorem 1: the other thresholds -/

/-- **Theorem 1, `⌈0.4 n⌉`.** For every `n ≥ 996`, Haar-almost every `n`-qubit pure state is
`⌈2n/5⌉`-UDA and the unique zero-energy ground state of a PSD `⌈2n/5⌉`-local Hamiltonian. -/
def Thm1FourTenths : Prop :=
  ∀ n : ℕ, 996 ≤ n →
    ∀ᵐ (ψ : Metric.sphere (0 : StateSpace n) 1) ∂(volume : Measure (StateSpace n)).toSphere,
      IsUDA n ((2 * n + 4) / 5) (ψ : StateSpace n).ofLp ∧
        IsUGS n ((2 * n + 4) / 5) (ψ : StateSpace n).ofLp

/-- **Theorem 1, `⌈2 κ_c n + 4 log₂ n⌉`.** For every `n ≥ 274`. -/
def Thm1Kappa : Prop :=
  ∀ κ : ℝ, IsKappaC κ → ∀ n : ℕ, 274 ≤ n →
    ∀ᵐ (ψ : Metric.sphere (0 : StateSpace n) 1) ∂(volume : Measure (StateSpace n)).toSphere,
      IsUDA n ⌈2 * κ * n + 4 * Real.logb 2 n⌉₊ (ψ : StateSpace n).ofLp ∧
        IsUGS n ⌈2 * κ * n + 4 * Real.logb 2 n⌉₊ (ψ : StateSpace n).ofLp

/-- **Theorem 1, asymptotic form** `K(n) = 2 κ_c n + O(log n)`. -/
def Thm1Asymptotic : Prop :=
  ∀ κ : ℝ, IsKappaC κ → ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
    ∀ᵐ (ψ : Metric.sphere (0 : StateSpace n) 1) ∂(volume : Measure (StateSpace n)).toSphere,
      IsUDA n ⌈2 * κ * n + C * Real.log n⌉₊ (ψ : StateSpace n).ofLp

/-! ## Simple top eigenvectors and Lemma A -/

/-- **Proposition (simple top eigenvector is UDA).** -/
def PropTopStatement : Prop :=
  ∀ (n K : ℕ) (H : Matrix (Idx n) (Idx n) ℂ) (ψ : Idx n → ℂ), K ≤ n →
    H ∈ realLocalOps n K → star ψ ⬝ᵥ ψ = 1 → IsGappedTop H ψ → IsUDA n K ψ

/-- **Lemma A (certificate to open set).** If `S(n, K)` holds at `(H, ψ₀)`, then `S(n, K)` holds
at every state of a nonempty open subset of the unit sphere; in particular all of these states
are `K`-UDA. -/
def LemmaAStatement : Prop :=
  ∀ (n K : ℕ) (H : Matrix (Idx n) (Idx n) ℂ) (ψ₀ : Idx n → ℂ), K ≤ n →
    star ψ₀ ⬝ᵥ ψ₀ = 1 → CertS n K H ψ₀ →
      ∃ U : Set (Metric.sphere (0 : StateSpace n) 1), IsOpen U ∧ U.Nonempty ∧
        ∀ ψ ∈ U, ∃ H' : Matrix (Idx n) (Idx n) ℂ, CertS n K H' (ψ : StateSpace n).ofLp

/-! ## Theorem 3 (small cases) and Theorem 2 (upper bound) -/

/-- **Theorem 3 for `(n, K) = (4, 2), (6, 3), (8, 3)`.** There is a nonempty open set of
`n`-qubit pure states that are `K`-UDA. -/
def Thm3Small : Prop :=
  ∀ nK ∈ ({(4, 2), (6, 3), (8, 3)} : Finset (ℕ × ℕ)),
    ∃ U : Set (Metric.sphere (0 : StateSpace nK.1) 1), IsOpen U ∧ U.Nonempty ∧
      ∀ ψ ∈ U, IsUDA nK.1 nK.2 (ψ : StateSpace nK.1).ofLp

/-- **Theorem 2 (i), upper bound** `K*₊(n) ≤ κ_c n + O(log n)`: for some `C`, for all large `n`
there is `K ≤ κ_c n + C log n` such that a nonempty open set of `n`-qubit pure states is
`K`-UDA. -/
def Thm2Upper : Prop :=
  ∀ κ : ℝ, IsKappaC κ → ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∃ K : ℕ,
    (K : ℝ) ≤ κ * n + C * Real.log n ∧
      ∃ U : Set (Metric.sphere (0 : StateSpace n) 1), IsOpen U ∧ U.Nonempty ∧
        ∀ ψ ∈ U, IsUDA n K (ψ : StateSpace n).ofLp

end UDA

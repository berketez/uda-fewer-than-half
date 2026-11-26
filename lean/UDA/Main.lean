import UDA.Statement
import UDA.Marginal
import UDA.Lemma1
import UDA.Ball
import UDA.Covering
import UDA.Stabilizer
import UDA.Generic
import UDA.Thresholds

/-!
# Main theorem

Assembles the pieces:
* `UDA.lemma1` (Lemma 1): spanning `C(L)` ⇒ `(2L+1)`-UDA and unique ground state;
* `UDA.ae_spanC` (genericity): `C(c)` at one vector ⇒ at Haar-almost every state;
* `UDA.exists_lagrangian_covering` + `UDA.exists_spanC_of_lagrangian` (Lemmas 2–3): a
  Lagrangian subspace with small covering radius exists, and its stabilizer state is a witness;
* `UDA.half_params` (explicit thresholds): parameters for every `n ≥ 139`;
* `UDA.isUDA_of_isUDAPauli`: equal marginals ⇒ equal Pauli expectations.

The statements are fixed in `UDA/Statement.lean`.
-/

open MeasureTheory
open scoped ComplexOrder

namespace UDA

/-- Lemma 1 + genericity: a single spanning witness gives a measure-one set of states that are
`(2c+1)`-UDA and unique zero-energy ground states of `(2c+1)`-local PSD Hamiltonians. -/
theorem ae_of_witness {n c : ℕ} (h : ∃ ψ₀ : Idx n → ℂ, SpanC n c ψ₀) :
    ∀ᵐ (ψ : Metric.sphere (0 : StateSpace n) 1) ∂(volume : Measure (StateSpace n)).toSphere,
      IsUDAPauli n (2 * c + 1) (ψ : StateSpace n).ofLp ∧
        IsUGS n (2 * c + 1) (ψ : StateSpace n).ofLp := by
  filter_upwards [ae_spanC h] with ψ hψ
  exact lemma1 (star_dotProduct_self_of_sphere ψ) hψ

/-- Lemma 3 (Pauli form, with the ground-state statement). -/
theorem lemma3_pauli (m t L : ℕ) (h : 2 ^ (m * (2 ^ t + 2)) < (2 ^ m + ballSum m L) ^ (2 ^ t)) :
    ∀ᵐ (ψ : Metric.sphere (0 : StateSpace (m + t)) 1)
        ∂(volume : Measure (StateSpace (m + t))).toSphere,
      IsUDAPauli (m + t) (2 * (L + t) + 1) (ψ : StateSpace (m + t)).ofLp ∧
        IsUGS (m + t) (2 * (L + t) + 1) (ψ : StateSpace (m + t)).ofLp := by
  rw [← ballCard_eq_ballSum] at h
  obtain ⟨S, hS, hcov⟩ := exists_lagrangian_covering m t L h
  exact ae_of_witness (exists_spanC_of_lagrangian S hS hcov)

/-- **Theorem 1, half threshold.** -/
theorem main_half (n : ℕ) (hn : 139 ≤ n) :
    ∀ᵐ (ψ : Metric.sphere (0 : StateSpace n) 1) ∂(volume : Measure (StateSpace n)).toSphere,
      IsUDA n ((n + 1) / 2 - 1) (ψ : StateSpace n).ofLp ∧
        IsUGS n ((n + 1) / 2 - 1) (ψ : StateSpace n).ofLp := by
  obtain ⟨m, t, L, hmt, hK, hcond⟩ := half_params n hn
  subst hmt
  filter_upwards [lemma3_pauli m t L hcond] with ψ hψ
  exact ⟨isUDA_of_isUDAPauli (by omega) (isUDAPauli_mono hK hψ.1), isUGS_mono hK hψ.2⟩

theorem mainStatement : MainStatement := main_half

/-- The uniform sphere measure is not zero. -/
theorem toSphere_univ_pos (n : ℕ) :
    0 < (volume : Measure (StateSpace n)).toSphere Set.univ := by
  rw [Measure.toSphere_apply_univ']
  have hdim : (0 : ENNReal) < (Module.finrank ℝ (StateSpace n) : ENNReal) := by
    have : 0 < Module.finrank ℝ (StateSpace n) := Module.finrank_pos
    exact_mod_cast this
  have hball : 0 < (volume : Measure (StateSpace n)) (Metric.ball 0 1 \ {0}) := by
    rw [measure_sdiff_null (measure_singleton 0)]
    exact Metric.measure_ball_pos _ _ one_pos
  exact ENNReal.mul_pos hdim.ne' hball.ne'

theorem jonesLindenFails : JonesLindenFails := by
  intro n hn
  refine ⟨(n + 1) / 2 - 1, by omega, ?_, ?_⟩
  · have h := main_half n hn
    rw [ae_iff] at h
    have hnull : (volume : Measure (StateSpace n)).toSphere
        {ψ | ¬ IsUDA n ((n + 1) / 2 - 1) (ψ : StateSpace n).ofLp} = 0 :=
      measure_mono_null (fun ψ hψ => by
        simp only [Set.mem_ofPred_eq] at hψ ⊢
        exact fun hboth => hψ hboth.1) h
    have hle := measure_univ_le_add_compl (μ := (volume : Measure (StateSpace n)).toSphere)
      {ψ : Metric.sphere (0 : StateSpace n) 1 | IsUDA n ((n + 1) / 2 - 1) (ψ : StateSpace n).ofLp}
    rw [Set.compl_ofPred, hnull, add_zero] at hle
    exact lt_of_lt_of_le (toSphere_univ_pos n) hle
  · have h := main_half n hn
    rw [ae_iff] at h
    exact measure_mono_null (fun ψ hψ => by
        simp only [Set.mem_ofPred_eq] at hψ ⊢
        exact fun hboth => hψ hboth.1) h

theorem lemma1Statement : Lemma1Statement := fun _ _ _ hψ h => lemma1 hψ h

theorem genericityStatement : GenericityStatement := fun _ _ h => ae_spanC h

theorem lemma3Statement : Lemma3Statement := by
  intro m t L hK h
  filter_upwards [lemma3_pauli m t L h] with ψ hψ
  exact isUDA_of_isUDAPauli hK hψ.1

end UDA

/-! ## Axiom check (printed during `lake build`) -/

#print axioms UDA.mainStatement
#print axioms UDA.jonesLindenFails
#print axioms UDA.lemma1Statement
#print axioms UDA.genericityStatement
#print axioms UDA.lemma3Statement

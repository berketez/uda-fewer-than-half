import UDA.Pauli

/-!
# A state satisfying the spanning condition, from an isotropic subspace with small covering radius

We prove `UDA.exists_spanC_of_lagrangian`: if `S` is a Lagrangian subspace of Pauli labels
such that every coset of `S` contains a label of weight at most `R`, then some state `ψ`
satisfies the spanning condition `SpanC n R ψ`.

The proof has three steps.

1. *Stabilizer state.* The operators `pauli s`, `s ∈ S`, commute pairwise and each squares to
   `± 1`, so they have a common eigenvector `ψ ≠ 0` (`Stab.exists_common_eigenvector`).
2. *Reduction to low weight.* For any label `v` pick `s ∈ S` with `wt (v + s) ≤ R`; then
   `pauli v ψ` is a scalar multiple of `pauli (v + s) ψ` (`Stab.pauli_mulVec_mem`).
3. *All Paulis span.* For `ψ ≠ 0` the vectors `pauli v ψ`, `v` arbitrary, span the whole space:
   `∑_z (-1)^(z·c) X^(a+c) Z^z ψ = 2^n ψ(c) |a⟩` (`Stab.sum_pauli_mulVec`).

Only the isotropy of `S` is used; the cardinality condition in `IsLagrangian` is not needed.
-/

open Matrix

namespace UDA

namespace Stab

variable {n : ℕ}

theorem pauli_mul_self (s : PL n) : pauli s * pauli s = sgn (bdot s.2 s.1) • 1 := by
  rw [pauli_mul, pl_add_self, pauli_zero]

/-- Each sign `± 1` has a complex square root. -/
theorem exists_mul_self_eq_sgn (t : ZMod 2) : ∃ μ : ℂ, μ * μ = sgn t := by
  unfold sgn
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨Complex.I, Complex.I_mul_I⟩

/-- Pairwise commuting Pauli operators have a common eigenvector. -/
theorem exists_common_eigenvector (T : Finset (PL n))
    (hT : ∀ p ∈ T, ∀ q ∈ T, symp p q = 0) :
    ∃ ψ : Idx n → ℂ, ψ ≠ 0 ∧ ∀ s ∈ T, ∃ μ : ℂ, pauli s *ᵥ ψ = μ • ψ := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 1, fun h => ?_, by simp⟩
    have := congrFun h 0
    simp at this
  | insert s T hs ih =>
    obtain ⟨ψ, hψ, hev⟩ := ih fun p hp q hq =>
      hT p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq)
    obtain ⟨μ, hμ⟩ := exists_mul_self_eq_sgn (bdot s.2 s.1)
    by_cases h0 : pauli s *ᵥ ψ + μ • ψ = 0
    · -- `ψ` is already an eigenvector of `pauli s`, with eigenvalue `-μ`
      refine ⟨ψ, hψ, fun s' hs' => ?_⟩
      rcases Finset.mem_insert.1 hs' with rfl | hs'
      · exact ⟨-μ, by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h0⟩
      · exact hev s' hs'
    · -- otherwise `(pauli s + μ) ψ` is an eigenvector of `pauli s`, with eigenvalue `μ`
      refine ⟨pauli s *ᵥ ψ + μ • ψ, h0, fun s' hs' => ?_⟩
      rcases Finset.mem_insert.1 hs' with rfl | hs'
      · refine ⟨μ, ?_⟩
        rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, pauli_mul_self, Matrix.smul_mulVec,
          Matrix.one_mulVec, Matrix.mulVec_smul, smul_add, smul_smul, hμ, add_comm]
      · obtain ⟨μ', hμ'⟩ := hev s' hs'
        refine ⟨μ', ?_⟩
        have hc : pauli s' * pauli s = pauli s * pauli s' := by
          rw [pauli_comm, hT s' (Finset.mem_insert_of_mem hs') s (Finset.mem_insert_self _ _),
            sgn_zero, one_smul]
        rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec,
          Matrix.mulVec_smul, hμ', Matrix.mulVec_smul, smul_add, smul_comm μ' μ ψ]

/-- If `ψ` is a common eigenvector of the Paulis in `S` and `S` has covering radius at most
`R`, then every `pauli v ψ` lies in the span of the `pauli p ψ` with `wt p ≤ R`. -/
theorem pauli_mulVec_mem (S : Submodule (ZMod 2) (PL n)) {R : ℕ} (hcov : CoversWithin S R)
    {ψ : Idx n → ℂ} (hev : ∀ s ∈ S, ∃ μ : ℂ, pauli s *ᵥ ψ = μ • ψ) (v : PL n) :
    pauli v *ᵥ ψ ∈ Submodule.span ℂ {w | ∃ p : PL n, wt p ≤ R ∧ w = pauli p *ᵥ ψ} := by
  obtain ⟨s, hs, hw⟩ := hcov v
  obtain ⟨μ, hμ⟩ := hev s hs
  have h1 : sgn (bdot (v + s).2 s.1) • (pauli (v + s) * pauli s) = pauli v := by
    rw [pauli_mul, add_assoc, pl_add_self, add_zero, smul_smul, sgn_mul_self, one_smul]
  have h2 : pauli v *ᵥ ψ = (sgn (bdot (v + s).2 s.1) * μ) • (pauli (v + s) *ᵥ ψ) := by
    rw [← h1, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hμ, Matrix.mulVec_smul, smul_smul]
  rw [h2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v + s, hw, rfl⟩)

theorem bits_add_eq_zero {a b : Fin n → ZMod 2} (h : a + b = 0) : b = a := by
  calc b = (a + a) + b := by rw [bits_add_self, zero_add]
    _ = a + (a + b) := by abel
    _ = a := by rw [h, add_zero]

/-- Fourier inversion: `∑_z (-1)^(z·c) X^(a+c) Z^z ψ = 2^n ψ(c) |a⟩`. -/
theorem sum_pauli_mulVec (ψ : Idx n → ℂ) (a c : Idx n) :
    ∑ z : Fin n → ZMod 2, sgn (bdot z c) • (pauli ((a + c, z) : PL n) *ᵥ ψ) =
      ((2 : ℂ) ^ n * ψ c) • (Pi.single a 1 : Idx n → ℂ) := by
  funext b
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pauli_mulVec_apply, Pi.single_apply]
  have e : c + (b + (a + c)) = a + b := by
    calc c + (b + (a + c)) = (a + b) + (c + c) := by abel
      _ = a + b := by rw [bits_add_self, add_zero]
  have h1 : ∀ z : Fin n → ZMod 2,
      sgn (bdot z c) * (sgn (bdot z (b + (a + c))) * ψ (b + (a + c))) =
        ψ (b + (a + c)) * sgn (bdot (a + b) z) := by
    intro z
    rw [← mul_assoc, ← sgn_add, ← bdot_add_right, e, bdot_comm, mul_comm]
  rw [Finset.sum_congr rfl fun z _ => h1 z, ← Finset.mul_sum, sum_sgn_bdot]
  by_cases hab : b = a
  · subst hab
    have e2 : b + (b + c) = c := by
      calc b + (b + c) = (b + b) + c := by abel
        _ = c := by rw [bits_add_self, zero_add]
    rw [e2, bits_add_self]
    simp [mul_comm]
  · have hne : a + b ≠ 0 := fun h => hab (bits_add_eq_zero h)
    simp [hne, hab]

/-- For `ψ ≠ 0`, a subspace containing all `pauli v ψ` is everything. -/
theorem eq_top_of_pauli_mulVec_mem {ψ : Idx n → ℂ} (hψ : ψ ≠ 0)
    (W : Submodule ℂ (Idx n → ℂ)) (hW : ∀ v : PL n, pauli v *ᵥ ψ ∈ W) : W = ⊤ := by
  obtain ⟨c, hc⟩ : ∃ c, ψ c ≠ 0 := by
    by_contra h
    exact hψ (funext fun c => not_not.1 fun hc => h ⟨c, hc⟩)
  have hsingle : ∀ a : Idx n, (Pi.single a 1 : Idx n → ℂ) ∈ W := by
    intro a
    have hmem : ((2 : ℂ) ^ n * ψ c) • (Pi.single a 1 : Idx n → ℂ) ∈ W := by
      rw [← sum_pauli_mulVec ψ a c]
      exact Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _ (hW _)
    have hne : (2 : ℂ) ^ n * ψ c ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) hc
    have h := Submodule.smul_mem W ((2 : ℂ) ^ n * ψ c)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h
  rw [eq_top_iff]
  intro f _
  have hf : f = ∑ a, f a • (Pi.single a 1 : Idx n → ℂ) := by
    funext b
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hf]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hsingle a)

end Stab

/-- **A state satisfying the spanning condition.** If `S` is a Lagrangian subspace of Pauli
labels every coset of which contains a label of weight at most `R`, then a stabilizer state
`ψ` of `S` satisfies `SpanC n R ψ`: the vectors `P ψ`, `P` a Pauli of weight at most `R`,
span the whole space. -/
theorem exists_spanC_of_lagrangian {n R : ℕ} (S : Submodule (ZMod 2) (PL n))
    (hS : IsLagrangian S) (hcov : CoversWithin S R) : ∃ ψ : Idx n → ℂ, SpanC n R ψ := by
  classical
  obtain ⟨ψ, hψ, hev⟩ := Stab.exists_common_eigenvector (Finset.univ.filter fun s => s ∈ S)
    fun p hp q hq => hS.1 p (Finset.mem_filter.1 hp).2 q (Finset.mem_filter.1 hq).2
  refine ⟨ψ, ?_⟩
  unfold SpanC
  exact Stab.eq_top_of_pauli_mulVec_mem hψ _
    (Stab.pauli_mulVec_mem S hcov fun s hs => hev s (Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩))

end UDA

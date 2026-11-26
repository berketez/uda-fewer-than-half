import UDA.Statement2
import UDA.Marginal

/-!
# Simple top eigenvectors of real local Hamiltonians are UDA

If `ψ` is a unit vector and the simple top eigenvector of a real `K`-local Hamiltonian `H`
(`IsGappedTop H ψ`), then `ψ` is `K`-UDA (`UDA.propTopStatement`).

Proof. A density matrix `ρ` with the same `K`-marginals as `|ψ⟩⟨ψ|` has the same expectation of
every Hermitian Pauli string of weight at most `K`, hence `tr (ρ H) = ⟨ψ, H ψ⟩ = E`. Write
`ρ = ∑ᵢ |wᵢ⟩⟨wᵢ|`. Every vector `u` satisfies `⟨u, H u⟩ ≤ E ⟨u, u⟩`, with equality only for
multiples of `ψ` (`UDA.Top.gap_all`: split `u = a ψ + v` with `v ⊥ ψ`; the cross terms vanish
because `ψ` is an eigenvector of the Hermitian matrix `H`). Summing over `i` forces equality in
every term, so each `wᵢ` is a multiple of `ψ` and `ρ = |ψ⟩⟨ψ|`.

The file also provides the basic facts about `hpauli` and `realLocalOps` used in
`UDA/LemmaA.lean`.
-/

open Matrix
open scoped ComplexOrder

namespace UDA

namespace Top

variable {n : ℕ}

/-! ### Hermitian Pauli strings -/

/-- The sign of a natural number modulo two. -/
theorem sgn_natCast (k : ℕ) : sgn (k : ZMod 2) = (-1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, sgn_add, ih, sgn_one, pow_succ]

/-- `x · z` is the parity of the number of `Y` factors. -/
theorem bdot_eq_ycount (p : PL n) : bdot p.1 p.2 = (ycount p : ZMod 2) := by
  unfold bdot ycount
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : p.1 j = 0
  · simp [h1]
  · by_cases h2 : p.2 j = 0
    · simp [h2]
    · simp [zmod2_eq_one_of_ne_zero h1, zmod2_eq_one_of_ne_zero h2]

/-- The Pauli strings `hpauli p` are Hermitian. -/
theorem hpauli_isHermitian (p : PL n) : (hpauli p).IsHermitian := by
  unfold Matrix.IsHermitian hpauli
  rw [Matrix.conjTranspose_smul, pauli_conjTranspose, bdot_eq_ycount, sgn_natCast, smul_smul]
  congr 1
  rw [star_pow, Complex.star_def, Complex.conj_I, ← mul_pow]
  norm_num

/-- The Pauli string with trivial label is the identity. -/
theorem hpauli_zero : hpauli (0 : PL n) = 1 := by
  simp [hpauli, ycount]

/-- The identity is a real `K`-local Hamiltonian. -/
theorem one_mem_realLocalOps (K : ℕ) : (1 : Matrix (Idx n) (Idx n) ℂ) ∈ realLocalOps n K :=
  Submodule.subset_span ⟨0, by simp, hpauli_zero.symm⟩

/-- Real local Hamiltonians are Hermitian. -/
theorem isHermitian_of_mem_realLocalOps {K : ℕ} {H : Matrix (Idx n) (Idx n) ℂ}
    (hH : H ∈ realLocalOps n K) : H.IsHermitian := by
  unfold realLocalOps at hH
  induction hH using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, -, rfl⟩ := hx
    exact hpauli_isHermitian p
  | zero => exact Matrix.isHermitian_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx =>
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, star_trivial, hx.eq]

/-- Expectations of real `K`-local Hamiltonians are determined by the Pauli expectations up to
weight `K`. -/
theorem trace_mul_eq_of_mem_realLocalOps {K : ℕ} {ρ σ : Matrix (Idx n) (Idx n) ℂ}
    (h : ∀ p : PL n, wt p ≤ K → (ρ * pauli p).trace = (σ * pauli p).trace)
    {H : Matrix (Idx n) (Idx n) ℂ} (hH : H ∈ realLocalOps n K) :
    (ρ * H).trace = (σ * H).trace := by
  unfold realLocalOps at hH
  induction hH using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    unfold hpauli
    rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, h p hp]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add, hx, hy]
  | smul c x _ hx =>
    rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, hx]

/-! ### Quadratic forms -/

/-- The quadratic form of a Hermitian matrix is real. -/
theorem star_quad_of_isHermitian {M : Matrix (Idx n) (Idx n) ℂ} (hM : M.IsHermitian)
    (v : Idx n → ℂ) : star (star v ⬝ᵥ (M *ᵥ v)) = star v ⬝ᵥ (M *ᵥ v) := by
  rw [← star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hM.eq]

/-- An eigenvector of a Hermitian matrix (for a real eigenvalue) is also a left eigenvector. -/
theorem star_dotProduct_mulVec_of_eig {H : Matrix (Idx n) (Idx n) ℂ} (hH : H.IsHermitian)
    {ψ : Idx n → ℂ} {E : ℝ} (hEig : H *ᵥ ψ = (E : ℂ) • ψ) (v : Idx n → ℂ) :
    star ψ ⬝ᵥ (H *ᵥ v) = E * (star ψ ⬝ᵥ v) := by
  have h1 : star ψ ᵥ* H = (E : ℂ) • star ψ := by
    have h2 := Matrix.star_mulVec H ψ
    rw [hEig, hH.eq, star_smul] at h2
    rw [← h2]
    simp
  rw [Matrix.dotProduct_mulVec, h1, smul_dotProduct, smul_eq_mul]

/-- `tr (|v⟩⟨v| M) = ⟨v, M v⟩`. -/
theorem trace_vecMulVec_mul (v : Idx n → ℂ) (M : Matrix (Idx n) (Idx n) ℂ) :
    (vecMulVec v (star v) * M).trace = star v ⬝ᵥ (M *ᵥ v) := by
  rw [Matrix.trace_mul_comm, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

/-- **Variational characterisation.** If `ψ` is the simple top eigenvector of the Hermitian
matrix `H`, with eigenvalue `E`, then `⟨u, H u⟩ ≤ E ⟨u, u⟩` for every vector `u`, with equality
only for the multiples of `ψ`. -/
theorem gap_all {H : Matrix (Idx n) (Idx n) ℂ} (hH : H.IsHermitian) {ψ : Idx n → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) {E : ℝ} (hEig : H *ᵥ ψ = (E : ℂ) • ψ)
    (hgap : ∀ v : Idx n → ℂ, v ≠ 0 → star v ⬝ᵥ ψ = 0 →
      (star v ⬝ᵥ (H *ᵥ v)).re < E * (star v ⬝ᵥ v).re) (u : Idx n → ℂ) :
    (star u ⬝ᵥ (H *ᵥ u)).re ≤ E * (star u ⬝ᵥ u).re ∧
      ((star u ⬝ᵥ (H *ᵥ u)).re = E * (star u ⬝ᵥ u).re → u = (star ψ ⬝ᵥ u) • ψ) := by
  obtain ⟨a, v, rfl, h1⟩ : ∃ (a : ℂ) (v : Idx n → ℂ), u = a • ψ + v ∧ star ψ ⬝ᵥ v = 0 := by
    refine ⟨star ψ ⬝ᵥ u, u - (star ψ ⬝ᵥ u) • ψ, by simp, ?_⟩
    rw [dotProduct_sub, dotProduct_smul, hψ, smul_eq_mul, mul_one, sub_self]
  have ha : star ψ ⬝ᵥ (a • ψ + v) = a := by
    rw [dotProduct_add, dotProduct_smul, hψ, h1, smul_eq_mul, mul_one, add_zero]
  have h2 : star v ⬝ᵥ ψ = 0 := by rw [star_dotProduct, h1, star_zero]
  have h3 : star ψ ⬝ᵥ (H *ᵥ v) = 0 := by
    rw [star_dotProduct_mulVec_of_eig hH hEig, h1, mul_zero]
  have hq : star (a • ψ + v) ⬝ᵥ (H *ᵥ (a • ψ + v)) =
      (E : ℂ) * (star a * a) + star v ⬝ᵥ (H *ᵥ v) := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hEig, star_add, star_smul, add_dotProduct,
      dotProduct_add, smul_dotProduct, dotProduct_smul, hψ, h2, h3, smul_eq_mul]
    ring
  have hn : star (a • ψ + v) ⬝ᵥ (a • ψ + v) = star a * a + star v ⬝ᵥ v := by
    simp only [star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, hψ, h1, h2, smul_eq_mul]
    ring
  have hsa : star a * a = (Complex.normSq a : ℂ) := (Complex.normSq_eq_conj_mul_self).symm
  rw [ha, hq, hn, hsa, ← Complex.ofReal_mul, Complex.add_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_re, mul_add]
  by_cases hv0 : v = 0
  · subst hv0
    simp
  · have hlt := hgap v hv0 h2
    exact ⟨by linarith, fun heq => absurd heq (by linarith)⟩

end Top

/-- **Proposition (simple top eigenvector is UDA).** A unit vector that is the simple top
eigenvector of a real `K`-local Hamiltonian is determined, among all states, by its `K`-body
marginals. -/
theorem propTopStatement : PropTopStatement := by
  intro n K H ψ hK hH hψ hgt ρ hρ hmarg
  obtain ⟨E, hEig, hgap⟩ := hgt
  have hHerm := Top.isHermitian_of_mem_realLocalOps hH
  -- equal marginals give equal Pauli expectations, hence equal energies
  have hexp : ∀ p : PL n, wt p ≤ K → (ρ * pauli p).trace = (proj ψ * pauli p).trace := by
    intro p hp
    obtain ⟨A, hAcard, hA⟩ := Mg.exists_card_eq_of_wt_le hK hp
    exact Mg.trace_mul_pauli_eq_of_marginal hA (hmarg A hAcard)
  have htr : (ρ * H).trace = E := by
    rw [Top.trace_mul_eq_of_mem_realLocalOps hexp hH, proj, Top.trace_vecMulVec_mul, hEig,
      dotProduct_smul, hψ, smul_eq_mul, mul_one]
  -- decompose `ρ` into rank-one terms
  obtain ⟨m, w, hw⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hρ.1
  have hterm : ∀ i, (star (w i) ⬝ᵥ (H *ᵥ w i)).re ≤ E * (star (w i) ⬝ᵥ w i).re :=
    fun i => (Top.gap_all hHerm hψ hEig hgap (w i)).1
  have hsumH : ∑ i, (star (w i) ⬝ᵥ (H *ᵥ w i)).re = E := by
    have h0 := congrArg Complex.re htr
    rw [hw, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum, Complex.ofReal_re] at h0
    simpa only [Top.trace_vecMulVec_mul] using h0
  have hsum1 : ∑ i, (star (w i) ⬝ᵥ w i).re = 1 := by
    have h0 := congrArg Complex.re hρ.2
    rw [hw, Matrix.trace_sum, Complex.re_sum, Complex.one_re] at h0
    simpa only [Matrix.trace_vecMulVec, dotProduct_comm] using h0
  have heq : ∀ i, (star (w i) ⬝ᵥ (H *ᵥ w i)).re = E * (star (w i) ⬝ᵥ w i).re := by
    have h0 : ∑ i, (E * (star (w i) ⬝ᵥ w i).re - (star (w i) ⬝ᵥ (H *ᵥ w i)).re) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum1, hsumH]
      ring
    intro i
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sub_nonneg.mpr (hterm i))).mp h0 i (Finset.mem_univ i)
    linarith
  have hwi : ∀ i, w i = (star ψ ⬝ᵥ w i) • ψ :=
    fun i => (Top.gap_all hHerm hψ hEig hgap (w i)).2 (heq i)
  -- hence `ρ` is a multiple of `|ψ⟩⟨ψ|`, and the trace fixes the factor
  have hρeq : ρ = (∑ i, (star ψ ⬝ᵥ w i) * star (star ψ ⬝ᵥ w i)) • proj ψ := by
    rw [hw, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [hwi i]
    rw [star_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul, proj]
  have hs : (∑ i, (star ψ ⬝ᵥ w i) * star (star ψ ⬝ᵥ w i)) = 1 := by
    have h0 := hρ.2
    rw [hρeq, Matrix.trace_smul, proj, Matrix.trace_vecMulVec, dotProduct_comm, hψ, smul_eq_mul,
      mul_one] at h0
    exact h0
  rw [hρeq, hs, one_smul]

end UDA

import UDA.TopEig
import UDA.Generic

/-!
# Lemma A: from one certificate to an open set of certificates

If the certificate condition `S(n, K)` holds at `(H, ψ₀)` (`UDA.CertS`), then it holds at every
state of a nonempty open subset of the unit sphere (`UDA.lemmaAStatement`).

Proof. Let `𝒜` be the real span of the Hermitian Pauli strings of weight at most `K` and of
`i·1` (`UDA.LA.opsR`). The real spanning condition `R(K)` at `ψ` says that `A ↦ A ψ` maps `𝒜`
onto the whole space (`UDA.LA.spanR_iff`). Fix a real basis `b` of the state space and choose
`C_j ∈ 𝒜` with `C_j ψ₀ = b_j`. The real square matrix `M(ψ)` of the vectors `C_j ψ` in the basis
`b` is the identity at `ψ₀`, so its determinant is nonzero near `ψ₀`. For such `ψ` every vector
`y` can be written as `C ψ` with `C ∈ 𝒜` (`UDA.LA.solOp_mulVec`): this is `R(K)` at `ψ`. The
eigenvalue equation is *linear* in the Hamiltonian, so the same solution formula, applied to
`y = (H - E) ψ`, gives `C(ψ) ∈ 𝒜`, continuous at `ψ₀` with `C(ψ₀) = 0`, such that
`(H - E - C(ψ)) ψ = 0`. Write `C(ψ) = G + i t` with `G` real `K`-local; then
`H' = H - E - G` is a real `K`-local Hamiltonian with `H' ψ = i t ψ`, and hermiticity forces
`t = 0`. Finally, the strict inequality `⟨v, (H - E) v⟩ < 0` on `ψ₀^⊥` is an open condition
in `(ψ, v)`; by compactness of the unit sphere in `v` it persists for all `ψ` near `ψ₀`
(`IsCompact.eventually_forall_of_forall_eventually`), which gives the gap of `H'` at `ψ`.
No implicit function theorem is needed.
-/

open Matrix Filter Topology
open scoped ComplexOrder

namespace UDA

namespace LA

variable {n : ℕ}

/-- The real span of the Hermitian Pauli strings of weight at most `K` and of `i·1`. -/
noncomputable def opsR (n K : ℕ) : Submodule ℝ (Matrix (Idx n) (Idx n) ℂ) :=
  Submodule.span ℝ ({M | ∃ p : PL n, wt p ≤ K ∧ M = hpauli p} ∪
    {Complex.I • (1 : Matrix (Idx n) (Idx n) ℂ)})

/-- Evaluation `A ↦ A ψ`, as a real linear map. -/
noncomputable def evalAt (ψ : Idx n → ℂ) : Matrix (Idx n) (Idx n) ℂ →ₗ[ℝ] (Idx n → ℂ) where
  toFun M := M *ᵥ ψ
  map_add' M N := Matrix.add_mulVec M N ψ
  map_smul' c M := Matrix.smul_mulVec c M ψ

/-- The real spanning condition `R(K)` at `ψ` says that every vector is of the form `C ψ` with
`C` in the real span of the Hermitian Pauli strings of weight at most `K` and of `i·1`. -/
theorem spanR_iff (K : ℕ) (ψ : Idx n → ℂ) :
    SpanR n K ψ ↔ ∀ y : Idx n → ℂ, ∃ C ∈ opsR n K, C *ᵥ ψ = y := by
  have himg : (evalAt ψ) '' ({M | ∃ p : PL n, wt p ≤ K ∧ M = hpauli p} ∪
      {Complex.I • (1 : Matrix (Idx n) (Idx n) ℂ)}) =
      {v | ∃ p : PL n, wt p ≤ K ∧ v = hpauli p *ᵥ ψ} ∪ {Complex.I • ψ} := by
    rw [Set.image_union, Set.image_singleton]
    congr 1
    · ext v
      constructor
      · rintro ⟨M, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨p, hp, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨hpauli p, ⟨p, hp, rfl⟩, rfl⟩
    · change {(Complex.I • (1 : Matrix (Idx n) (Idx n) ℂ)) *ᵥ ψ} = {Complex.I • ψ}
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  unfold SpanR opsR
  rw [← himg, ← Submodule.map_span]
  constructor
  · intro h y
    have hy : y ∈ Submodule.map (evalAt ψ) (Submodule.span ℝ
        ({M | ∃ p : PL n, wt p ≤ K ∧ M = hpauli p} ∪
          {Complex.I • (1 : Matrix (Idx n) (Idx n) ℂ)})) := by
      rw [h]
      exact Submodule.mem_top
    obtain ⟨C, hC, rfl⟩ := hy
    exact ⟨C, hC, rfl⟩
  · intro h
    rw [eq_top_iff]
    intro y _
    obtain ⟨C, hC, rfl⟩ := h y
    exact ⟨C, hC, rfl⟩

/-- Every element of `opsR n K` is a real `K`-local Hamiltonian plus a real multiple of
`i·1`. -/
theorem exists_decomp {K : ℕ} {C : Matrix (Idx n) (Idx n) ℂ} (hC : C ∈ opsR n K) :
    ∃ G ∈ realLocalOps n K, ∃ t : ℝ,
      C = G + ((t : ℂ) * Complex.I) • (1 : Matrix (Idx n) (Idx n) ℂ) := by
  unfold opsR at hC
  rw [Submodule.span_union, Submodule.mem_sup] at hC
  obtain ⟨G, hG, D, hD, rfl⟩ := hC
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hD
  refine ⟨G, hG, t, ?_⟩
  congr 1
  ext a b
  simp [Matrix.smul_apply, mul_assoc]

/-- A nonzero vector is a positive multiple of a vector of norm one. -/
theorem exists_unit_smul {v : Idx n → ℂ} (hv : v ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ u : Idx n → ℂ, u ∈ Metric.sphere (0 : Idx n → ℂ) 1 ∧
      v = (c : ℂ) • u := by
  have hc : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hc' : ((‖v‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨‖v‖, hc, ((‖v‖ : ℝ) : ℂ)⁻¹ • v, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hc.le, inv_mul_cancel₀ hc.ne']
  · rw [smul_smul, mul_inv_cancel₀ hc', one_smul]

/-- The quadratic form `(A, v) ↦ ⟨v, A v⟩` is jointly continuous. -/
theorem continuous_quad :
    Continuous fun p : Matrix (Idx n) (Idx n) ℂ × (Idx n → ℂ) => star p.2 ⬝ᵥ (p.1 *ᵥ p.2) :=
  (continuous_star.comp continuous_snd).dotProduct
    (continuous_fst.matrix_mulVec continuous_snd)

/-! ### Solving `C ψ = y` by Cramer's rule -/

section Solve

variable {ι : Type} [Fintype ι] [DecidableEq ι] (B : Module.Basis ι ℝ (Idx n → ℂ))
  (Cb : ι → Matrix (Idx n) (Idx n) ℂ)

/-- The real coordinate matrix, in the basis `B`, of the vectors `Cb j ψ`. -/
noncomputable def coordMat (ψ : Idx n → ℂ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => B.repr (Cb j *ᵥ ψ) i

/-- The coefficients given by Cramer's rule. -/
noncomputable def coeffs (ψ y : Idx n → ℂ) : ι → ℝ :=
  (coordMat B Cb ψ).det⁻¹ • ((coordMat B Cb ψ).adjugate *ᵥ B.equivFun y)

/-- The real combination of the `Cb j` that sends `ψ` to `y` (when the determinant of the
coordinate matrix is nonzero). -/
noncomputable def solOp (ψ y : Idx n → ℂ) : Matrix (Idx n) (Idx n) ℂ :=
  ∑ j, coeffs B Cb ψ y j • Cb j

omit [Fintype ι] [DecidableEq ι] in
/-- The coordinate matrix depends continuously (in fact linearly) on `ψ`. -/
theorem continuous_coordMat : Continuous (coordMat B Cb) := by
  refine continuous_matrix fun i j => ?_
  exact (B.coord i).continuous_of_finiteDimensional.comp
    (Continuous.matrix_mulVec continuous_const continuous_id)

omit [Fintype ι] in
/-- If `Cb j ψ₀ = B j` for all `j`, the coordinate matrix at `ψ₀` is the identity. -/
theorem coordMat_eq_one {ψ₀ : Idx n → ℂ} (h : ∀ j, Cb j *ᵥ ψ₀ = B j) :
    coordMat B Cb ψ₀ = 1 := by
  ext i j
  simp only [coordMat, Matrix.of_apply, h, Module.Basis.repr_self_apply, Matrix.one_apply]
  exact if_congr eq_comm rfl rfl

/-- **Solving linear equations near a spanning point.** If the vectors `Cb j ψ` have a real
coordinate matrix with nonzero determinant, then every vector `y` equals `C ψ` for an explicit
real combination `C` of the `Cb j`. -/
theorem solOp_mulVec {ψ : Idx n → ℂ} (hd : (coordMat B Cb ψ).det ≠ 0) (y : Idx n → ℂ) :
    solOp B Cb ψ y *ᵥ ψ = y := by
  have hMz : coordMat B Cb ψ *ᵥ coeffs B Cb ψ y = B.equivFun y := by
    rw [coeffs, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ hd, one_smul]
  apply B.equivFun.injective
  funext i
  rw [← hMz, solOp, Matrix.sum_mulVec, map_sum]
  simp only [Matrix.smul_mulVec, map_smul, Finset.sum_apply, Pi.smul_apply,
    Module.Basis.equivFun_apply, smul_eq_mul, Matrix.mulVec, dotProduct, coordMat,
    Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The solution operator is a real combination of the `Cb j`. -/
theorem solOp_mem {K : ℕ} (hCb : ∀ j, Cb j ∈ opsR n K) (ψ y : Idx n → ℂ) :
    solOp B Cb ψ y ∈ opsR n K :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hCb j)

/-- The solution operator for the target `0` vanishes. -/
theorem solOp_zero (ψ : Idx n → ℂ) : solOp B Cb ψ 0 = 0 := by
  simp [solOp, coeffs]

/-- The solution operator depends continuously on `ψ` where the determinant is nonzero. -/
theorem continuousAt_solOp {f : (Idx n → ℂ) → (Idx n → ℂ)} (hf : Continuous f)
    {ψ₀ : Idx n → ℂ} (hd : (coordMat B Cb ψ₀).det ≠ 0) :
    ContinuousAt (fun ψ => solOp B Cb ψ (f ψ)) ψ₀ := by
  have hM := continuous_coordMat B Cb
  have hz : ContinuousAt (fun ψ => coeffs B Cb ψ (f ψ)) ψ₀ := by
    refine ContinuousAt.smul (hM.matrix_det.continuousAt.inv₀ hd) ?_
    exact (Continuous.matrix_mulVec hM.matrix_adjugate
      (B.equivFun.toLinearMap.continuous_of_finiteDimensional.comp hf)).continuousAt
  unfold solOp
  refine tendsto_finsetSum _ fun j _ => ?_
  exact ((continuous_apply j).continuousAt.comp hz).smul continuousAt_const

end Solve

/-! ### Persistence of the gap -/

/-- **The gap is an open condition.** If `N` is continuous at `ψ₀` and the quadratic form of
`N ψ₀` is negative on the nonzero vectors orthogonal to `ψ₀`, then for all `ψ` near `ψ₀` the
quadratic form of `N ψ` is negative on the nonzero vectors orthogonal to `ψ`. -/
theorem gap_persist {N : (Idx n → ℂ) → Matrix (Idx n) (Idx n) ℂ} {ψ₀ : Idx n → ℂ}
    (hN : ContinuousAt N ψ₀)
    (h0 : ∀ v : Idx n → ℂ, v ≠ 0 → star v ⬝ᵥ ψ₀ = 0 → (star v ⬝ᵥ (N ψ₀ *ᵥ v)).re < 0) :
    ∀ᶠ ψ in 𝓝 ψ₀, ∀ v : Idx n → ℂ, v ≠ 0 → star v ⬝ᵥ ψ = 0 →
      (star v ⬝ᵥ (N ψ *ᵥ v)).re < 0 := by
  have hsph : ∀ᶠ ψ in 𝓝 ψ₀, ∀ v ∈ Metric.sphere (0 : Idx n → ℂ) 1,
      star v ⬝ᵥ ψ ≠ 0 ∨ (star v ⬝ᵥ (N ψ *ᵥ v)).re < 0 := by
    refine (isCompact_sphere (0 : Idx n → ℂ) 1).eventually_forall_of_forall_eventually ?_
    intro v hv
    by_cases hvψ : star v ⬝ᵥ ψ₀ = 0
    · have h1 : ContinuousAt (fun p : (Idx n → ℂ) × (Idx n → ℂ) => (N p.1, p.2)) (ψ₀, v) :=
        hN.fst'.prodMk continuousAt_snd
      have h2 : ContinuousAt
          (fun p : (Idx n → ℂ) × (Idx n → ℂ) => star p.2 ⬝ᵥ (N p.1 *ᵥ p.2)) (ψ₀, v) :=
        ContinuousAt.comp
          (g := fun q : Matrix (Idx n) (Idx n) ℂ × (Idx n → ℂ) => star q.2 ⬝ᵥ (q.1 *ᵥ q.2))
          (f := fun p : (Idx n → ℂ) × (Idx n → ℂ) => (N p.1, p.2))
          continuous_quad.continuousAt h1
      have hq : ContinuousAt
          (fun p : (Idx n → ℂ) × (Idx n → ℂ) => (star p.2 ⬝ᵥ (N p.1 *ᵥ p.2)).re) (ψ₀, v) :=
        ContinuousAt.comp (g := Complex.re)
          (f := fun p : (Idx n → ℂ) × (Idx n → ℂ) => star p.2 ⬝ᵥ (N p.1 *ᵥ p.2))
          Complex.continuous_re.continuousAt h2
      have hv0 : v ≠ 0 := by
        intro h0
        rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hv
        exact zero_ne_one hv
      exact (hq.eventually (eventually_lt_nhds (h0 v hv0 hvψ))).mono fun p hp => Or.inr hp
    · have hc : ContinuousAt
          (fun p : (Idx n → ℂ) × (Idx n → ℂ) => star p.2 ⬝ᵥ p.1) (ψ₀, v) :=
        ((continuous_star.comp continuous_snd).dotProduct continuous_fst).continuousAt
      exact (hc.eventually_ne hvψ).mono fun p hp => Or.inl hp
  filter_upwards [hsph] with ψ hP v hv hvψ
  obtain ⟨c, hc, u, hu, rfl⟩ := exists_unit_smul hv
  have huψ : star u ⬝ᵥ ψ = 0 := by
    rw [star_smul, smul_dotProduct, smul_eq_mul] at hvψ
    rcases mul_eq_zero.mp hvψ with h | h
    · exact absurd h (by simpa using hc.ne')
    · exact h
  rcases hP u hu with h | h
  · exact absurd huψ h
  · have hscale : star ((c : ℂ) • u) ⬝ᵥ (N ψ *ᵥ ((c : ℂ) • u)) =
        ((c * c : ℝ) : ℂ) * (star u ⬝ᵥ (N ψ *ᵥ u)) := by
      rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring
    rw [hscale, Complex.re_ofReal_mul]
    exact mul_neg_of_pos_of_neg (mul_pos hc hc) h

/-! ### The local statement -/

/-- **Local form of Lemma A.** Near `ψ₀`, every unit vector carries a certificate. -/
theorem eventually_certS {K : ℕ} {H : Matrix (Idx n) (Idx n) ℂ} {ψ₀ : Idx n → ℂ}
    (hcert : CertS n K H ψ₀) :
    ∀ᶠ ψ in 𝓝 ψ₀, star ψ ⬝ᵥ ψ = 1 → ∃ H' : Matrix (Idx n) (Idx n) ℂ, CertS n K H' ψ := by
  classical
  obtain ⟨hH, ⟨E, hEig, hgap⟩, hspan⟩ := hcert
  -- a real basis of the state space and operators `Cb j ∈ opsR n K` with `Cb j ψ₀ = B j`
  let B := Module.finBasis ℝ (Idx n → ℂ)
  choose Cb hCb hCbψ using fun j => (spanR_iff K ψ₀).mp hspan (B j)
  have hdet0 : (coordMat B Cb ψ₀).det ≠ 0 := by
    rw [coordMat_eq_one B Cb hCbψ, Matrix.det_one]
    exact one_ne_zero
  have hdet : ∀ᶠ ψ in 𝓝 ψ₀, (coordMat B Cb ψ).det ≠ 0 :=
    ((continuous_coordMat B Cb).matrix_det.continuousAt).eventually_ne hdet0
  -- the shifted Hamiltonian `N ψ = H - E - C(ψ)`, where `C(ψ) ψ = (H - E) ψ`
  have hrcont : Continuous fun ψ : Idx n → ℂ =>
      (H - E • (1 : Matrix (Idx n) (Idx n) ℂ)) *ᵥ ψ :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have hr0 : (H - E • (1 : Matrix (Idx n) (Idx n) ℂ)) *ᵥ ψ₀ = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hEig]
    ext a
    simp
  have hNcont : ContinuousAt (fun ψ : Idx n → ℂ => H - E • (1 : Matrix (Idx n) (Idx n) ℂ) -
      solOp B Cb ψ ((H - E • (1 : Matrix (Idx n) (Idx n) ℂ)) *ᵥ ψ)) ψ₀ :=
    continuousAt_const.sub (continuousAt_solOp B Cb hrcont hdet0)
  have hgapev := gap_persist hNcont (fun v hv hvψ => by
    have h2 := hgap v hv hvψ
    rw [hr0, solOp_zero, sub_zero, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_smul, Complex.sub_re, Complex.real_smul,
      Complex.re_ofReal_mul]
    linarith)
  -- conclusion
  filter_upwards [hdet, hgapev] with ψ hd hP hψ
  set C := solOp B Cb ψ ((H - E • (1 : Matrix (Idx n) (Idx n) ℂ)) *ᵥ ψ) with hC
  have hCψ : C *ᵥ ψ = (H - E • (1 : Matrix (Idx n) (Idx n) ℂ)) *ᵥ ψ := solOp_mulVec B Cb hd _
  obtain ⟨G, hG, t, hdec⟩ := exists_decomp (solOp_mem B Cb hCb ψ
    ((H - E • (1 : Matrix (Idx n) (Idx n) ℂ)) *ᵥ ψ))
  rw [← hC] at hdec
  have hH'mem : H - E • (1 : Matrix (Idx n) (Idx n) ℂ) - G ∈ realLocalOps n K :=
    Submodule.sub_mem _ (Submodule.sub_mem _ hH
      (Submodule.smul_mem _ E (Top.one_mem_realLocalOps K))) hG
  have hNψ : (H - E • (1 : Matrix (Idx n) (Idx n) ℂ) - C) *ᵥ ψ = 0 := by
    rw [Matrix.sub_mulVec, hCψ, sub_self]
  have hH'N : H - E • (1 : Matrix (Idx n) (Idx n) ℂ) - G =
      (H - E • (1 : Matrix (Idx n) (Idx n) ℂ) - C) +
        ((t : ℂ) * Complex.I) • (1 : Matrix (Idx n) (Idx n) ℂ) := by
    rw [hdec]
    abel
  have hH'ψ : (H - E • (1 : Matrix (Idx n) (Idx n) ℂ) - G) *ᵥ ψ =
      ((t : ℂ) * Complex.I) • ψ := by
    rw [hH'N, Matrix.add_mulVec, hNψ, zero_add, Matrix.smul_mulVec, Matrix.one_mulVec]
  -- hermiticity kills the imaginary shift
  have ht : t = 0 := by
    have h1 := Top.star_quad_of_isHermitian (Top.isHermitian_of_mem_realLocalOps hH'mem) ψ
    rw [hH'ψ, dotProduct_smul, hψ, smul_eq_mul, mul_one] at h1
    have h2 := congrArg Complex.im h1
    simp at h2
    linarith
  have hH'eq : H - E • (1 : Matrix (Idx n) (Idx n) ℂ) - G =
      H - E • (1 : Matrix (Idx n) (Idx n) ℂ) - C := by
    rw [hH'N, ht]
    simp
  refine ⟨H - E • (1 : Matrix (Idx n) (Idx n) ℂ) - C, hH'eq ▸ hH'mem, ⟨0, ?_, ?_⟩, ?_⟩
  · rw [hNψ]
    simp
  · intro v hv hvψ
    rw [zero_mul]
    exact hP v hv hvψ
  · exact (spanR_iff K ψ).mpr fun y => ⟨_, solOp_mem B Cb hCb ψ y, solOp_mulVec B Cb hd y⟩

/-- A unit vector of `ℂ^(2^n)`, viewed in the Euclidean state space, lies on the unit
sphere. -/
theorem norm_toLp_eq_one {ψ : Idx n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    ‖(WithLp.toLp 2 ψ : StateSpace n)‖ = 1 := by
  have h1 : ∑ a, ‖ψ a‖ ^ 2 = 1 := by
    have h0 := congrArg Complex.re hψ
    simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.one_re] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [EuclideanSpace.norm_eq]
  change √(∑ a, ‖ψ a‖ ^ 2) = 1
  rw [h1, Real.sqrt_one]

end LA

/-- **Lemma A (certificate to open set).** If `S(n, K)` holds at `(H, ψ₀)`, then `S(n, K)` holds
at every state of a nonempty open subset of the unit sphere. -/
theorem lemmaAStatement : LemmaAStatement := by
  intro n K H ψ₀ _ hψ₀ hcert
  obtain ⟨O, hOsub, hOopen, hOmem⟩ := mem_nhds_iff.mp (LA.eventually_certS hcert)
  refine ⟨{φ | (φ : StateSpace n).ofLp ∈ O}, ?_, ?_, ?_⟩
  · exact hOopen.preimage ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val)
  · exact ⟨⟨WithLp.toLp 2 ψ₀, by
      rw [mem_sphere_zero_iff_norm]
      exact LA.norm_toLp_eq_one hψ₀⟩, hOmem⟩
  · intro φ hφ
    exact hOsub hφ (star_dotProduct_self_of_sphere φ)

/-- **Corollary of Lemma A and of the top-eigenvector proposition.** A certificate at one unit
vector yields a nonempty open set of `K`-UDA states. -/
theorem LA.exists_open_isUDA_of_certS {n K : ℕ} {H : Matrix (Idx n) (Idx n) ℂ}
    {ψ₀ : Idx n → ℂ} (hK : K ≤ n) (hψ₀ : star ψ₀ ⬝ᵥ ψ₀ = 1) (hcert : CertS n K H ψ₀) :
    ∃ U : Set (Metric.sphere (0 : StateSpace n) 1), IsOpen U ∧ U.Nonempty ∧
      ∀ ψ ∈ U, IsUDA n K (ψ : StateSpace n).ofLp := by
  obtain ⟨U, hUo, hUne, hU⟩ := lemmaAStatement n K H ψ₀ hK hψ₀ hcert
  refine ⟨U, hUo, hUne, fun ψ hψ => ?_⟩
  obtain ⟨H', hH', hgt, -⟩ := hU ψ hψ
  exact propTopStatement n K H' _ hK hH' (star_dotProduct_self_of_sphere ψ) hgt

end UDA

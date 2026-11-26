import UDA.Defs

/-!
# Genericity of the spanning condition

If the complex spanning condition `C(c)` (`UDA.SpanC n c`) holds at one vector, it holds for
Haar-almost every pure state (`UDA.ae_spanC`).

Proof: `C(c)` holds at `ψ` as soon as the determinant of a fixed `2ⁿ × 2ⁿ` matrix whose columns
are `P_i ψ` is nonzero. This determinant is a polynomial in the coordinates of `ψ`, nonzero at the
witness, and the zero set of a nonzero complex polynomial is Lebesgue-null
(`UDA.Gen.volume_zeroSet_pi`). Its intersection with the unit sphere is then null for the
sphere measure `(volume).toSphere`, because the determinant is homogeneous.
-/

open MeasureTheory Matrix Set
open scoped ComplexOrder

namespace UDA
namespace Gen

/-! ## Zero sets of nonzero complex polynomials are null -/

/-- Zero set of a nonzero polynomial in `k` complex variables is Lebesgue-null. -/
theorem volume_zeroSet_fin :
    ∀ (k : ℕ) (P : MvPolynomial (Fin k) ℂ), P ≠ 0 →
      volume {x : Fin k → ℂ | MvPolynomial.eval x P = 0} = 0 := by
  intro k
  induction k with
  | zero =>
    intro P hP
    have hc : P.coeff 0 ≠ 0 := by
      intro h0
      apply hP
      rw [MvPolynomial.eq_C_of_isEmpty P, h0, map_zero]
    have : {x : Fin 0 → ℂ | MvPolynomial.eval x P = 0} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rw [MvPolynomial.eq_C_of_isEmpty P, MvPolynomial.eval_C]
      exact hc
    rw [this, measure_empty]
  | succ k ih =>
    intro P hP
    set Q := MvPolynomial.finSuccEquiv ℂ k P with hQdef
    have hQ : Q ≠ 0 := by
      intro h
      apply hP
      exact (MvPolynomial.finSuccEquiv ℂ k).injective (by rw [← hQdef, h, map_zero])
    -- a nonzero coefficient of `Q`
    set c := Q.leadingCoeff with hcdef
    have hc : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hQ
    have hnull : volume {s : Fin k → ℂ | MvPolynomial.eval s c = 0} = 0 := ih c hc
    -- the zero set in product coordinates `(y, s) ↦ Fin.cons y s`
    set Z : Set (ℂ × (Fin k → ℂ)) :=
      {p | Polynomial.eval p.1 (Polynomial.map (MvPolynomial.eval p.2) Q) = 0} with hZ
    have hcontP : Continuous fun x : Fin (k + 1) → ℂ => MvPolynomial.eval x P :=
      MvPolynomial.continuous_eval P
    have hpfsa : ∀ x : Fin (k + 1) → ℂ,
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) 0 x = (x 0, Fin.tail x) := by
      intro x
      ext j
      · rfl
      · simp [MeasurableEquiv.piFinSuccAbove, Fin.tail]
    have hpre : {x : Fin (k + 1) → ℂ | MvPolynomial.eval x P = 0} =
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) 0) ⁻¹' Z := by
      ext x
      rw [mem_preimage, hpfsa x, hZ, mem_ofPred_eq, mem_ofPred_eq, hQdef,
        ← MvPolynomial.eval_eq_eval_mv_eval', Fin.cons_self_tail]
    have hZm : MeasurableSet Z := by
      have hcl : IsClosed {x : Fin (k + 1) → ℂ | MvPolynomial.eval x P = 0} :=
        isClosed_eq hcontP continuous_const
      have hm := hcl.measurableSet
      rw [hpre] at hm
      have := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) 0).symm.measurable hm
      rwa [← preimage_comp, MeasurableEquiv.self_comp_symm, preimage_id] at this
    have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) 0
    rw [hpre, hmp.measure_preimage hZm.nullMeasurableSet]
    -- slice by the second coordinate
    change (volume.prod volume) Z = 0
    rw [Measure.prod_apply_symm hZm]
    apply lintegral_eq_zero_of_ae_eq_zero
    have hae : ∀ᵐ s ∂(volume : Measure (Fin k → ℂ)), MvPolynomial.eval s c ≠ 0 := by
      rw [ae_iff]; simpa using hnull
    filter_upwards [hae] with s hs
    have hq : Polynomial.map (MvPolynomial.eval s) Q ≠ 0 := by
      intro h0
      apply hs
      have h1 : (Polynomial.map (MvPolynomial.eval s) Q).coeff Q.natDegree =
          MvPolynomial.eval s c := by
        rw [Polynomial.coeff_map]; rfl
      rw [← h1, h0, Polynomial.coeff_zero]
    have hsub : (fun y : ℂ => (y, s)) ⁻¹' Z ⊆
        ((Polynomial.map (MvPolynomial.eval s) Q).roots.toFinset : Set ℂ) := by
      intro y hy
      simp only [mem_preimage, hZ, mem_ofPred_eq] at hy
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_roots hq).2 hy
    exact measure_mono_null hsub (Finset.measure_zero _ _)

/-- Zero set of a nonzero polynomial in finitely many complex variables is Lebesgue-null. -/
theorem volume_zeroSet_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial ι ℂ) (hP : P ≠ 0) :
    volume {x : ι → ℂ | MvPolynomial.eval x P = 0} = 0 := by
  set k := Fintype.card ι
  let e : ι ≃ Fin k := Fintype.equivFin ι
  set P' := MvPolynomial.rename e P with hP'
  have hP'0 : P' ≠ 0 := by
    intro h
    apply hP
    exact MvPolynomial.rename_injective _ e.injective (by rw [← hP', h, map_zero])
  have h0 := volume_zeroSet_fin k P' hP'0
  -- transport along the measure-preserving reindexing `(Fin k → ℂ) ≃ (ι → ℂ)`
  let φ := MeasurableEquiv.piCongrLeft (fun _ : ι => ℂ) e.symm
  have hφ : MeasurePreserving φ volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : ι => ℂ) e.symm
  have hφx : ∀ (y : Fin k → ℂ) (i : ι), φ y i = y (e i) := by
    intro y i
    have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => ℂ) e.symm y (e i)
    simpa using this
  have hset : φ ⁻¹' {x : ι → ℂ | MvPolynomial.eval x P = 0} =
      {y : Fin k → ℂ | MvPolynomial.eval y P' = 0} := by
    ext y
    rw [mem_preimage, mem_ofPred_eq, mem_ofPred_eq, hP', MvPolynomial.eval_rename]
    have : (φ y : ι → ℂ) = y ∘ e := funext fun i => hφx y i
    rw [this]
  have hmeas : MeasurableSet {x : ι → ℂ | MvPolynomial.eval x P = 0} :=
    (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).measurableSet
  rw [← hφ.measure_preimage hmeas.nullMeasurableSet, hset, h0]

/-! ## Determinant of the columns `P_i v` -/

variable {n : ℕ}

/-- The matrix whose `i`-th column is `pauli (f i) *ᵥ v`. -/
def colMat (f : Idx n → PL n) (v : Idx n → ℂ) : Matrix (Idx n) (Idx n) ℂ :=
  Matrix.of fun a i => (pauli (f i) *ᵥ v) a

/-- The determinant of `colMat f v` as a polynomial in the coordinates of `v`. -/
noncomputable def colPoly (f : Idx n → PL n) : MvPolynomial (Idx n) ℂ :=
  (Matrix.of fun a i => ∑ b, MvPolynomial.C (pauli (f i) a b) * MvPolynomial.X b).det

theorem eval_colPoly (f : Idx n → PL n) (v : Idx n → ℂ) :
    MvPolynomial.eval v (colPoly f) = (colMat f v).det := by
  rw [colPoly, RingHom.map_det]
  congr 1
  ext a i
  simp [colMat, Matrix.mulVec, dotProduct]

/-- A nonzero column determinant gives the spanning condition. -/
theorem spanC_of_det_ne_zero {c : ℕ} (f : Idx n → PL n) (hf : ∀ i, wt (f i) ≤ c)
    (v : Idx n → ℂ) (hdet : (colMat f v).det ≠ 0) : SpanC n c v := by
  have hunit : IsUnit (colMat f v) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have hli : LinearIndependent ℂ (fun i => (colMat f v)ᵀ i) :=
    Matrix.linearIndependent_col_iff_isUnit.2 hunit
  have hcols : (fun i => (colMat f v)ᵀ i) = fun i => pauli (f i) *ᵥ v := by
    funext i; ext a; simp [colMat]
  rw [hcols] at hli
  have htop : Submodule.span ℂ (Set.range fun i => pauli (f i) *ᵥ v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  apply eq_top_iff.2
  rw [← htop]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨f i, hf i, rfl⟩

/-- A witness of `C(c)` yields labels whose column determinant is nonzero at the witness. -/
theorem exists_det_ne_zero {c : ℕ} {ψ₀ : Idx n → ℂ} (h : SpanC n c ψ₀) :
    ∃ f : Idx n → PL n, (∀ i, wt (f i) ≤ c) ∧ (colMat f ψ₀).det ≠ 0 := by
  set S : Set (Idx n → ℂ) := {v | ∃ p : PL n, wt p ≤ c ∧ v = pauli p *ᵥ ψ₀} with hS
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℂ S
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → (Idx n → ℂ))) := by
    rw [Subtype.range_coe, hspan]
    exact le_of_eq h.symm
  let B : Module.Basis b ℂ (Idx n → ℂ) := Module.Basis.mk hli hsp
  let _ : Fintype b := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card b = Fintype.card (Idx n) := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fintype_fun_eq_card]
  let e : Idx n ≃ b := Fintype.equivOfCardEq hcard.symm
  have hmem : ∀ i, ∃ p : PL n, wt p ≤ c ∧ ((e i : b) : Idx n → ℂ) = pauli p *ᵥ ψ₀ :=
    fun i => hbS (e i).2
  choose f hf hfe using hmem
  refine ⟨f, hf, ?_⟩
  have hli' : LinearIndependent ℂ (fun i => ((e i : b) : Idx n → ℂ)) :=
    hli.comp e e.injective
  have hcols : (fun i => (colMat f ψ₀)ᵀ i) = fun i => ((e i : b) : Idx n → ℂ) := by
    funext i; ext a; simp [colMat, hfe i]
  have hli'' : LinearIndependent ℂ (fun i => (colMat f ψ₀)ᵀ i) := by rw [hcols]; exact hli'
  have hu := Matrix.linearIndependent_col_iff_isUnit.1 hli''
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

/-- Null sets of coordinate space pull back to null sets of the Euclidean state space. -/
theorem volume_ofLp_preimage_null {Z : Set (Idx n → ℂ)} (hZ : MeasurableSet Z)
    (h0 : volume Z = 0) :
    volume ((fun v : StateSpace n => (v.ofLp : Idx n → ℂ)) ⁻¹' Z) = 0 := by
  let L : StateSpace n ≃L[ℝ] (Idx n → ℂ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Idx n => ℂ)
  have hmeas : Measurable (L : StateSpace n → (Idx n → ℂ)) := L.continuous.measurable
  have : (Measure.map L (volume : Measure (StateSpace n))).IsAddHaarMeasure :=
    L.isAddHaarMeasure_map _
  have hac : Measure.map L (volume : Measure (StateSpace n)) ≪ (volume : Measure (Idx n → ℂ)) :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have h1 := hac h0
  rw [Measure.map_apply hmeas hZ] at h1
  have hL : (L : StateSpace n → (Idx n → ℂ)) = fun v : StateSpace n => (v.ofLp : Idx n → ℂ) := by
    funext v; rfl
  rw [hL] at h1
  exact h1

end Gen

/-- **Genericity.** If `C(c)` holds at some vector, then it holds for Haar-almost every pure
state, i.e. for almost every point of the unit sphere of `ℂ^(2^n)` with respect to the uniform
sphere measure `(volume).toSphere`. -/
theorem ae_spanC {n c : ℕ} (h : ∃ ψ₀ : Idx n → ℂ, SpanC n c ψ₀) :
    ∀ᵐ (ψ : Metric.sphere (0 : StateSpace n) 1) ∂(volume : Measure (StateSpace n)).toSphere,
      SpanC n c (ψ : StateSpace n).ofLp := by
  obtain ⟨ψ₀, hψ₀⟩ := h
  obtain ⟨f, hf, hdet⟩ := Gen.exists_det_ne_zero hψ₀
  set g : StateSpace n → ℂ := fun v => (Gen.colMat f v.ofLp).det with hgdef
  have hg : ∀ v, g v = MvPolynomial.eval v.ofLp (Gen.colPoly f) :=
    fun v => (Gen.eval_colPoly f _).symm
  have hPne : Gen.colPoly f ≠ 0 := by
    intro h0; apply hdet; rw [← Gen.eval_colPoly, h0, map_zero]
  have hZ : MeasurableSet {x : Idx n → ℂ | MvPolynomial.eval x (Gen.colPoly f) = 0} :=
    (isClosed_eq (MvPolynomial.continuous_eval _) continuous_const).measurableSet
  have hnull : volume {v : StateSpace n | g v = 0} = 0 := by
    have h1 := Gen.volume_ofLp_preimage_null hZ (Gen.volume_zeroSet_pi _ hPne)
    have hset : {v : StateSpace n | g v = 0} =
        (fun v : StateSpace n => (v.ofLp : Idx n → ℂ)) ⁻¹'
          {x : Idx n → ℂ | MvPolynomial.eval x (Gen.colPoly f) = 0} := by
      ext v; simp [hg]
    rw [hset]; exact h1
  have hcont : Continuous g := by
    have : g = fun v : StateSpace n => MvPolynomial.eval v.ofLp (Gen.colPoly f) := funext hg
    rw [this]
    exact (MvPolynomial.continuous_eval _).comp (PiLp.continuous_ofLp 2 _)
  set s₀ : Set (Metric.sphere (0 : StateSpace n) 1) := {ψ | g ψ = 0} with hs₀def
  have hs₀ : MeasurableSet s₀ :=
    (isClosed_eq (hcont.comp continuous_subtype_val) continuous_const).measurableSet
  rw [ae_iff]
  apply measure_mono_null (t := s₀)
  · intro ψ hψ
    by_contra hne
    exact hψ (Gen.spanC_of_det_ne_zero f hf _ hne)
  · rw [Measure.toSphere_apply' _ hs₀]
    apply mul_eq_zero_of_right
    apply measure_mono_null _ hnull
    rintro _ ⟨r, -, w, ⟨ψ, hψ, rfl⟩, rfl⟩
    simp only [mem_ofPred_eq, hs₀def] at hψ ⊢
    have hsmul : ((r • (ψ : StateSpace n)).ofLp : Idx n → ℂ) = (r : ℂ) • (ψ : StateSpace n).ofLp := by
      funext a; simp [Complex.real_smul]
    have hcol : Gen.colMat f ((r : ℂ) • (ψ : StateSpace n).ofLp) =
        (r : ℂ) • Gen.colMat f (ψ : StateSpace n).ofLp := by
      ext a i; simp [Gen.colMat, Matrix.mulVec_smul]
    rw [hgdef] at hψ ⊢
    simp only at hψ ⊢
    rw [hsmul, hcol, Matrix.det_smul, hψ, mul_zero]

/-- Points of the unit sphere are normalized: `⟨ψ, ψ⟩ = 1`. -/
theorem star_dotProduct_self_of_sphere {n : ℕ} (ψ : Metric.sphere (0 : StateSpace n) 1) :
    star (ψ : StateSpace n).ofLp ⬝ᵥ (ψ : StateSpace n).ofLp = 1 := by
  have hn : ‖(ψ : StateSpace n)‖ = 1 := by simp
  have h := EuclideanSpace.inner_eq_star_dotProduct (ψ : StateSpace n) (ψ : StateSpace n)
  rw [inner_self_eq_norm_sq_to_K, hn] at h
  rw [dotProduct_comm]
  simpa using h.symm

end UDA

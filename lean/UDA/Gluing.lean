import UDA.LemmaA

/-!
# Gluing: product with `|0⟩` and the generic upgrade

A *datum* `(K_H, r, c)` at a unit vector `ψ` (`UDA.GL.Datum`) records that `ψ` is the simple top
eigenvector of a real `K_H`-local Hamiltonian, that the real spanning condition `R(r)` holds at
`ψ`, and that the complex spanning condition `C(c)` holds at `ψ`. A datum with `K_H, r ≤ K` is a
certificate `S(n, K)` (`UDA.GL.Datum.certS`).

Two rules produce new data.

* **Product with `|0⟩`** (`UDA.GL.datum_tens`, the case `ψ₂ = |0⟩` of Lemma B). If `ψ` has datum
  `(K_H, r, c)`, then `|0⟩ ⊗ ψ` has datum `(max K_H 1, max r (c+1), c+1)`, with Hamiltonian
  `1 ⊗ H + Z ⊗ 1`. Indeed `(X^s Z^t ⊗ P)(|0⟩ ⊗ ψ) = |s⟩ ⊗ P ψ`, so the Paulis `1 ⊗ P` give
  `|0⟩ ⊗ ℂ^(2^n)` from `R(r)` at `ψ`, and the Paulis `X ⊗ P`, `Y ⊗ P` give the complex span of
  the `|1⟩ ⊗ P ψ`, which is `|1⟩ ⊗ ℂ^(2^n)` by `C(c)` at `ψ`. The spectrum of `1 ⊗ H + Z ⊗ 1` on
  `|e⟩ ⊗ ℂ^(2^n)` is that of `H ± 1`, so the top eigenvalue `E + 1` is simple.
* **Generic upgrade** (`UDA.GL.datum_upgrade`). If a datum `(K_H, r, c)` exists and `C(c')` holds
  at some vector, then a datum `(max K_H r, r, min c c')` exists: by Lemma A the certificate
  persists on a neighbourhood of the state, `R(r)` is an open condition, and `C(c)`, `C(c')` hold
  at almost every point of the sphere, hence at some point of every nonempty open subset.

The new qubit is put in front (index `0`); vectors on `n + 1` qubits are handled through their
two slices `v(0, ·)` and `v(1, ·)`.
-/

open Matrix MeasureTheory Filter Topology
open scoped ComplexOrder

namespace UDA.GL

variable {n : ℕ}

/-! ### Monotonicity -/

/-- Real `K`-local Hamiltonians are real `K'`-local for `K ≤ K'`. -/
theorem realLocalOps_mono {K K' : ℕ} (h : K ≤ K') : realLocalOps n K ≤ realLocalOps n K' :=
  Submodule.span_mono fun _ ⟨p, hp, hM⟩ => ⟨p, hp.trans h, hM⟩

/-- `R(r)` implies `R(r')` for `r ≤ r'`. -/
theorem spanR_mono {r r' : ℕ} (h : r ≤ r') {ψ : Idx n → ℂ} (hR : SpanR n r ψ) :
    SpanR n r' ψ := by
  unfold SpanR at hR ⊢
  rw [eq_top_iff, ← hR]
  refine Submodule.span_mono (Set.union_subset_union_left _ ?_)
  exact fun _ ⟨p, hp, hv⟩ => ⟨p, hp.trans h, hv⟩

/-- `C(c)` implies `C(c')` for `c ≤ c'`. -/
theorem spanC_mono {c c' : ℕ} (h : c ≤ c') {ψ : Idx n → ℂ} (hC : SpanC n c ψ) :
    SpanC n c' ψ := by
  unfold SpanC at hC ⊢
  rw [eq_top_iff, ← hC]
  exact Submodule.span_mono fun _ ⟨p, hp, hv⟩ => ⟨p, hp.trans h, hv⟩

/-! ### Slices and the product `|e⟩ ⊗ ψ` -/

/-- A bit is `0` or `1`. -/
theorem zmod2_cases (e : ZMod 2) : e = 0 ∨ e = 1 := by
  revert e
  decide

/-- The component of `v` on which the first qubit is in the state `|e⟩`. -/
def slice (e : ZMod 2) (v : Idx (n + 1) → ℂ) : Idx n → ℂ := fun a => v (Fin.cons e a)

/-- The product vector `|e⟩ ⊗ ψ` (the new qubit has index `0`). -/
def tens (e : ZMod 2) (ψ : Idx n → ℂ) : Idx (n + 1) → ℂ :=
  fun b => if b 0 = e then ψ (Fin.tail b) else 0

/-- The label of `X^s Z^t ⊗ P`. -/
def lab (s t : ZMod 2) (p : PL n) : PL (n + 1) := (Fin.cons s p.1, Fin.cons t p.2)

/-- Slices are additive. -/
theorem slice_add (e : ZMod 2) (v w : Idx (n + 1) → ℂ) :
    slice e (v + w) = slice e v + slice e w := rfl

/-- Slices commute with scalar multiplication. -/
theorem slice_smul {R : Type*} [SMul R ℂ] (e : ZMod 2) (c : R) (v : Idx (n + 1) → ℂ) :
    slice e (c • v) = c • slice e v := rfl

/-- The slices of the zero vector vanish. -/
theorem slice_zero (e : ZMod 2) : slice e (0 : Idx (n + 1) → ℂ) = 0 := rfl

/-- The slices of `|e'⟩ ⊗ ψ`: `ψ` for `e = e'` and `0` otherwise. -/
theorem slice_tens (e e' : ZMod 2) (ψ : Idx n → ℂ) :
    slice e (tens e' ψ) = if e = e' then ψ else 0 := by
  funext a
  simp only [slice, tens, Fin.cons_zero, Fin.tail_cons]
  split_ifs <;> rfl

/-- A vector on `n + 1` qubits is determined by its two slices. -/
theorem eq_of_slice_eq {v w : Idx (n + 1) → ℂ} (h : ∀ e, slice e v = slice e w) : v = w := by
  funext b
  have hb := congrFun (h (b 0)) (Fin.tail b)
  simp only [slice] at hb
  rwa [Fin.cons_self_tail] at hb

/-- A vector on `n + 1` qubits is `|0⟩ ⊗ v₀ + |1⟩ ⊗ v₁`. -/
theorem tens_slice_add (v : Idx (n + 1) → ℂ) :
    tens 0 (slice 0 v) + tens 1 (slice 1 v) = v := by
  refine eq_of_slice_eq fun e => ?_
  rw [slice_add, slice_tens, slice_tens]
  rcases zmod2_cases e with rfl | rfl <;> simp

/-- `ψ ↦ |e⟩ ⊗ ψ` is additive. -/
theorem tens_add (e : ZMod 2) (u w : Idx n → ℂ) : tens e (u + w) = tens e u + tens e w := by
  funext b
  simp only [tens, Pi.add_apply]
  split_ifs <;> simp

/-- `ψ ↦ |e⟩ ⊗ ψ` is homogeneous. -/
theorem tens_smul (e : ZMod 2) (c : ℂ) (u : Idx n → ℂ) : tens e (c • u) = c • tens e u := by
  funext b
  simp only [tens, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- `|e⟩ ⊗ 0 = 0`. -/
theorem tens_zero (e : ZMod 2) : tens e (0 : Idx n → ℂ) = 0 := by
  funext b
  simp [tens]

/-- `ψ ↦ |e⟩ ⊗ ψ` as a linear map. -/
def tensL (e : ZMod 2) : (Idx n → ℂ) →ₗ[ℂ] (Idx (n + 1) → ℂ) where
  toFun := tens e
  map_add' := tens_add e
  map_smul' := tens_smul e

/-- Sums over bit strings of length `n + 1` split according to the first bit. -/
theorem sum_idx_succ {M : Type*} [AddCommMonoid M] (f : Idx (n + 1) → M) :
    ∑ b, f b = ∑ a : Idx n, f (Fin.cons 0 a) + ∑ a : Idx n, f (Fin.cons 1 a) := by
  rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ZMod 2).sum_comp, Fintype.sum_prod_type]
  exact Fin.sum_univ_two _

/-- Inner products split into the two slices. -/
theorem dot_split (v w : Idx (n + 1) → ℂ) :
    star v ⬝ᵥ w = star (slice 0 v) ⬝ᵥ slice 0 w + star (slice 1 v) ⬝ᵥ slice 1 w := by
  simp only [dotProduct]
  exact sum_idx_succ _

/-! ### Paulis on `n + 1` qubits -/

/-- Addition of bit strings with a prepended bit. -/
theorem cons_add_cons (e s : ZMod 2) (a x : Fin n → ZMod 2) :
    (Fin.cons e a + Fin.cons s x : Fin (n + 1) → ZMod 2) = Fin.cons (e + s) (a + x) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> simp

/-- Dot product of bit strings with a prepended bit. -/
theorem bdot_cons (t u : ZMod 2) (z b : Fin n → ZMod 2) :
    bdot (Fin.cons t z : Fin (n + 1) → ZMod 2) (Fin.cons u b) = t * u + bdot z b := by
  simp [bdot, Fin.sum_univ_succ]

/-- The weight of `X^s Z^t ⊗ P`. -/
theorem wt_lab (s t : ZMod 2) (p : PL n) :
    wt (lab s t p) = wt p + if s ≠ 0 ∨ t ≠ 0 then 1 else 0 := by
  unfold wt lab
  rw [Finset.card_filter, Fin.sum_univ_succ, Finset.card_filter]
  simp only [Fin.cons_zero, Fin.cons_succ]
  exact add_comm _ _

/-- The number of `Y` factors of `X^s Z^t ⊗ P`. -/
theorem ycount_lab (s t : ZMod 2) (p : PL n) :
    ycount (lab s t p) = ycount p + if s ≠ 0 ∧ t ≠ 0 then 1 else 0 := by
  unfold ycount lab
  rw [Finset.card_filter, Fin.sum_univ_succ, Finset.card_filter]
  simp only [Fin.cons_zero, Fin.cons_succ]
  exact add_comm _ _

/-- **Action of `X^s Z^t ⊗ P` on slices.** -/
theorem slice_pauli_lab_mulVec (s t e : ZMod 2) (p : PL n) (v : Idx (n + 1) → ℂ) :
    slice e (pauli (lab s t p) *ᵥ v) = sgn (t * (e + s)) • (pauli p *ᵥ slice (e + s) v) := by
  funext a
  simp only [slice, Pi.smul_apply, smul_eq_mul, pauli_mulVec_apply, lab, cons_add_cons,
    bdot_cons, sgn_add]
  ring

/-- `(X^s Z^t ⊗ P)(|0⟩ ⊗ ψ) = |s⟩ ⊗ P ψ`. -/
theorem pauli_lab_mulVec_tens (s t : ZMod 2) (p : PL n) (ψ : Idx n → ℂ) :
    pauli (lab s t p) *ᵥ tens 0 ψ = tens s (pauli p *ᵥ ψ) := by
  have key : ∀ e s : ZMod 2, e + s = 0 ↔ e = s := by decide
  refine eq_of_slice_eq fun e => ?_
  rw [slice_pauli_lab_mulVec, slice_tens, slice_tens]
  by_cases h : e = s
  · rw [ite_eq_left h, ite_eq_left ((key e s).2 h), (key e s).2 h, mul_zero, sgn_zero, one_smul]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((key e s).1 h')), Matrix.mulVec_zero, smul_zero]

/-- The Hermitian Pauli string `X^s Z^t ⊗ P` on `|0⟩ ⊗ ψ`. -/
theorem hpauli_lab_mulVec_tens (s t : ZMod 2) (p : PL n) (ψ : Idx n → ℂ) :
    hpauli (lab s t p) *ᵥ tens 0 ψ =
      Complex.I ^ ycount (lab s t p) • tens s (pauli p *ᵥ ψ) := by
  rw [hpauli, Matrix.smul_mulVec, pauli_lab_mulVec_tens]

/-- `(1 ⊗ P)(|0⟩ ⊗ ψ) = |0⟩ ⊗ P ψ` for Hermitian Pauli strings. -/
theorem hpauli_lab_zero_mulVec_tens (p : PL n) (ψ : Idx n → ℂ) :
    hpauli (lab 0 0 p) *ᵥ tens 0 ψ = tens 0 (hpauli p *ᵥ ψ) := by
  rw [hpauli_lab_mulVec_tens, ycount_lab, hpauli, Matrix.smul_mulVec, tens_smul]
  simp

/-! ### The spanning conditions at `|0⟩ ⊗ ψ` -/

/-- **`C` is additive.** `C(c)` at `ψ` implies `C(c + 1)` at `|0⟩ ⊗ ψ`. -/
theorem spanC_tens {c : ℕ} {ψ : Idx n → ℂ} (h : SpanC n c ψ) :
    SpanC (n + 1) (c + 1) (tens 0 ψ) := by
  unfold SpanC at h ⊢
  have key : ∀ (e : ZMod 2) (w : Idx n → ℂ), tens e w ∈
      Submodule.span ℂ {v | ∃ p : PL (n + 1), wt p ≤ c + 1 ∧ v = pauli p *ᵥ tens 0 ψ} := by
    intro e w
    have hle : Submodule.span ℂ {v | ∃ p : PL n, wt p ≤ c ∧ v = pauli p *ᵥ ψ} ≤
        (Submodule.span ℂ {v | ∃ p : PL (n + 1), wt p ≤ c + 1 ∧
          v = pauli p *ᵥ tens 0 ψ}).comap (tensL e) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨p, hp, rfl⟩
      refine Submodule.mem_comap.2 (Submodule.subset_span
        ⟨lab e 0 p, ?_, (pauli_lab_mulVec_tens e 0 p ψ).symm⟩)
      rw [wt_lab]
      split_ifs <;> omega
    rw [h] at hle
    exact hle Submodule.mem_top
  rw [eq_top_iff]
  intro v _
  rw [← tens_slice_add v]
  exact Submodule.add_mem _ (key 0 _) (key 1 _)

/-- A real subspace containing `g` and `i g` contains the complex line through `g`. -/
theorem smul_mem_of_I_smul_mem {m : ℕ} (V : Submodule ℝ (Idx m → ℂ)) {g : Idx m → ℂ}
    (h1 : g ∈ V) (h2 : Complex.I • g ∈ V) (z : ℂ) : z • g ∈ V := by
  have hz : z • g = z.re • g + z.im • (Complex.I • g) := by
    funext b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im z]
    ring
  rw [hz]
  exact V.add_mem (V.smul_mem _ h1) (V.smul_mem _ h2)

/-- **`R` at a product with `|0⟩`.** `R(r)` and `C(c)` at `ψ` imply `R(max r (c + 1))` at
`|0⟩ ⊗ ψ`. -/
theorem spanR_tens {r c : ℕ} {ψ : Idx n → ℂ} (hR : SpanR n r ψ) (hC : SpanC n c ψ) :
    SpanR (n + 1) (max r (c + 1)) (tens 0 ψ) := by
  unfold SpanR at hR ⊢
  unfold SpanC at hC
  set V := Submodule.span ℝ ({v | ∃ p : PL (n + 1), wt p ≤ max r (c + 1) ∧
    v = hpauli p *ᵥ tens 0 ψ} ∪ {Complex.I • tens 0 ψ}) with hV
  have hgen : ∀ P : PL (n + 1), wt P ≤ max r (c + 1) → hpauli P *ᵥ tens 0 ψ ∈ V :=
    fun P hP => Submodule.subset_span (Or.inl ⟨P, hP, rfl⟩)
  -- the Paulis `1 ⊗ P` and `i` give `|0⟩ ⊗ w` for every `w`
  have key0 : ∀ w : Idx n → ℂ, tens 0 w ∈ V := by
    intro w
    have hle : Submodule.span ℝ ({v | ∃ p : PL n, wt p ≤ r ∧ v = hpauli p *ᵥ ψ} ∪
        {Complex.I • ψ}) ≤ V.comap ((tensL 0).restrictScalars ℝ) := by
      refine Submodule.span_le.2 ?_
      rintro _ (⟨p, hp, rfl⟩ | rfl)
      · change tens 0 (hpauli p *ᵥ ψ) ∈ V
        rw [← hpauli_lab_zero_mulVec_tens]
        refine hgen _ ?_
        rw [wt_lab]
        simp only [ne_eq, not_true_eq_false, or_self, ite_false, add_zero]
        exact hp.trans (le_max_left _ _)
      · change tens 0 (Complex.I • ψ) ∈ V
        rw [tens_smul]
        exact Submodule.subset_span (Or.inr rfl)
    rw [hR] at hle
    exact hle Submodule.mem_top
  -- the Paulis `X ⊗ P` and `Y ⊗ P` give the complex span of the `|1⟩ ⊗ P ψ`
  have key1 : ∀ w : Idx n → ℂ, ∀ z : ℂ, z • tens 1 w ∈ V := by
    intro w
    have hw : w ∈ Submodule.span ℂ {v | ∃ p : PL n, wt p ≤ c ∧ v = pauli p *ᵥ ψ} := by
      rw [hC]
      exact Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, hp, rfl⟩ := hx
      intro z
      have hwt : ∀ t : ZMod 2, wt (lab 1 t p) ≤ max r (c + 1) := by
        intro t
        rw [wt_lab, ite_eq_left (Or.inl one_ne_zero)]
        exact (Nat.add_le_add_right hp 1).trans (le_max_right _ _)
      have h1 := hgen (lab 1 0 p) (hwt 0)
      have h2 := hgen (lab 1 1 p) (hwt 1)
      rw [hpauli_lab_mulVec_tens, ycount_lab] at h1 h2
      rw [ite_eq_right (fun h => h.2 rfl), add_zero] at h1
      rw [ite_eq_left ⟨one_ne_zero, one_ne_zero⟩, pow_succ', ← smul_smul] at h2
      have h3 := smul_mem_of_I_smul_mem V h1 h2 (z * (Complex.I ^ ycount p)⁻¹)
      rwa [smul_smul, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ Complex.I_ne_zero),
        mul_one] at h3
    | zero =>
      intro z
      rw [tens_zero, smul_zero]
      exact V.zero_mem
    | add x y _ _ hx hy =>
      intro z
      rw [tens_add, smul_add]
      exact V.add_mem (hx z) (hy z)
    | smul a x _ hx =>
      intro z
      rw [tens_smul, smul_smul]
      exact hx (z * a)
  rw [eq_top_iff]
  intro v _
  rw [← tens_slice_add v]
  refine V.add_mem (key0 _) ?_
  have h := key1 (slice 1 v) 1
  rwa [one_smul] at h

/-! ### The Hamiltonian `1 ⊗ H + Z ⊗ 1` -/

/-- `M'` acts on `n + 1` qubits as `1 ⊗ M`. -/
def Lifts (M : Matrix (Idx n) (Idx n) ℂ) (M' : Matrix (Idx (n + 1)) (Idx (n + 1)) ℂ) : Prop :=
  ∀ (e : ZMod 2) (v : Idx (n + 1) → ℂ), slice e (M' *ᵥ v) = M *ᵥ slice e v

/-- A real `K`-local Hamiltonian `H` on `n` qubits has a real `K`-local lift `1 ⊗ H`. -/
theorem exists_lifts {K : ℕ} {H : Matrix (Idx n) (Idx n) ℂ} (hH : H ∈ realLocalOps n K) :
    ∃ H' ∈ realLocalOps (n + 1) K, Lifts H H' := by
  unfold realLocalOps at hH
  induction hH using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    refine ⟨hpauli (lab 0 0 p), Submodule.subset_span ⟨lab 0 0 p, ?_, rfl⟩, fun e v => ?_⟩
    · rw [wt_lab]
      simpa using hp
    · rw [hpauli, hpauli, Matrix.smul_mulVec, Matrix.smul_mulVec, slice_smul,
        slice_pauli_lab_mulVec, ycount_lab]
      simp
  | zero =>
    exact ⟨0, Submodule.zero_mem _, fun e v => by
      rw [Matrix.zero_mulVec, Matrix.zero_mulVec, slice_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', hxl⟩ := hx
    obtain ⟨y', hy', hyl⟩ := hy
    exact ⟨x' + y', Submodule.add_mem _ hx' hy', fun e v => by
      rw [Matrix.add_mulVec, Matrix.add_mulVec, slice_add, hxl, hyl]⟩
  | smul a x _ hx =>
    obtain ⟨x', hx', hxl⟩ := hx
    exact ⟨a • x', Submodule.smul_mem _ a hx', fun e v => by
      rw [Matrix.smul_mulVec, Matrix.smul_mulVec, slice_smul, hxl]⟩

/-- `Z ⊗ 1` multiplies the slice `e` by `(-1)^e`. -/
theorem slice_Z_mulVec (e : ZMod 2) (v : Idx (n + 1) → ℂ) :
    slice e (hpauli (lab 0 1 (0 : PL n)) *ᵥ v) = sgn e • slice e v := by
  rw [hpauli, Matrix.smul_mulVec, slice_smul, slice_pauli_lab_mulVec, ycount_lab]
  simp [ycount]

/-- **The top eigenvector of `1 ⊗ H + Z ⊗ 1`.** If `ψ` is the simple top eigenvector of the
Hermitian matrix `H`, then `|0⟩ ⊗ ψ` is the simple top eigenvector of `1 ⊗ H + Z ⊗ 1`. -/
theorem isGappedTop_tens {H : Matrix (Idx n) (Idx n) ℂ}
    {H' : Matrix (Idx (n + 1)) (Idx (n + 1)) ℂ} (hH : H.IsHermitian) (hL : Lifts H H')
    {ψ : Idx n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (hgt : IsGappedTop H ψ) :
    IsGappedTop (H' + hpauli (lab 0 1 (0 : PL n))) (tens 0 ψ) := by
  obtain ⟨E, hEig, hgap⟩ := hgt
  refine ⟨E + 1, ?_, ?_⟩
  · refine eq_of_slice_eq fun e => ?_
    rw [Matrix.add_mulVec, slice_add, hL, slice_Z_mulVec, slice_smul, slice_tens]
    rcases zmod2_cases e with rfl | rfl
    · rw [ite_eq_left rfl, hEig, sgn_zero, one_smul, Complex.ofReal_add, Complex.ofReal_one,
        add_smul, one_smul]
    · rw [ite_eq_right one_ne_zero, Matrix.mulVec_zero, smul_zero, smul_zero, add_zero]
  · intro v hv hvψ
    have h0 : star (slice 0 v) ⬝ᵥ ψ = 0 := by
      rw [dot_split, slice_tens, slice_tens, ite_eq_left rfl, ite_eq_right one_ne_zero,
        dotProduct_zero, add_zero] at hvψ
      exact hvψ
    have hq : star v ⬝ᵥ ((H' + hpauli (lab 0 1 (0 : PL n))) *ᵥ v) =
        star (slice 0 v) ⬝ᵥ (H *ᵥ slice 0 v) + star (slice 0 v) ⬝ᵥ slice 0 v +
          (star (slice 1 v) ⬝ᵥ (H *ᵥ slice 1 v) - star (slice 1 v) ⬝ᵥ slice 1 v) := by
      rw [dot_split, Matrix.add_mulVec, slice_add, slice_add, hL, hL, slice_Z_mulVec,
        slice_Z_mulVec, sgn_zero, sgn_one, one_smul, neg_one_smul, dotProduct_add,
        dotProduct_add, dotProduct_neg, sub_eq_add_neg]
    have hle0 := (Top.gap_all hH hψ hEig hgap (slice 0 v)).1
    have hle1 := (Top.gap_all hH hψ hEig hgap (slice 1 v)).1
    rw [hq, dot_split v v]
    simp only [Complex.add_re, Complex.sub_re]
    by_cases h1 : slice 1 v = 0
    · have hv0 : slice 0 v ≠ 0 := by
        intro h0'
        refine hv (eq_of_slice_eq fun e => ?_)
        rcases zmod2_cases e with rfl | rfl
        · rw [h0', slice_zero]
        · rw [h1, slice_zero]
      have hlt := hgap (slice 0 v) hv0 h0
      rw [h1] at hle1 ⊢
      simp only [Matrix.mulVec_zero, dotProduct_zero, Complex.zero_re, sub_zero, add_zero]
      linarith
    · have hpos : 0 < (star (slice 1 v) ⬝ᵥ slice 1 v).re :=
        (Complex.pos_iff.mp (dotProduct_star_self_pos_iff.mpr h1)).1
      linarith

/-! ### Data and the two rules -/

/-- A datum `(K_H, r, c)` at `ψ`: `ψ` is a unit vector and the simple top eigenvector of a real
`K_H`-local Hamiltonian, `R(r)` holds at `ψ`, and `C(c)` holds at `ψ`. -/
def Datum (n KH r c : ℕ) (ψ : Idx n → ℂ) : Prop :=
  star ψ ⬝ᵥ ψ = 1 ∧ (∃ H ∈ realLocalOps n KH, IsGappedTop H ψ) ∧ SpanR n r ψ ∧ SpanC n c ψ

/-- Data are monotone in all three parameters. -/
theorem Datum.mono {KH r c KH' r' c' : ℕ} {ψ : Idx n → ℂ} (h : Datum n KH r c ψ)
    (h1 : KH ≤ KH') (h2 : r ≤ r') (h3 : c ≤ c') : Datum n KH' r' c' ψ := by
  obtain ⟨hψ, ⟨H, hH, hgt⟩, hR, hC⟩ := h
  exact ⟨hψ, ⟨H, realLocalOps_mono h1 hH, hgt⟩, spanR_mono h2 hR, spanC_mono h3 hC⟩

/-- A datum `(K_H, r, c)` with `K_H, r ≤ K` is a certificate `S(n, K)`. -/
theorem Datum.certS {KH r c K : ℕ} {ψ : Idx n → ℂ} (h : Datum n KH r c ψ) (h1 : KH ≤ K)
    (h2 : r ≤ K) : ∃ H : Matrix (Idx n) (Idx n) ℂ, CertS n K H ψ := by
  obtain ⟨-, ⟨H, hH, hgt⟩, hR, -⟩ := h
  exact ⟨H, realLocalOps_mono h1 hH, hgt, spanR_mono h2 hR⟩

/-- The datum `(0, 0, 0)` of the unique state on zero qubits. -/
theorem datum_zero : Datum 0 0 0 0 (fun _ => 1) := by
  have hy : ∀ y : Idx 0 → ℂ, y = y 0 • (fun _ => 1 : Idx 0 → ℂ) := by
    intro y
    funext a
    rw [Subsingleton.elim a 0]
    simp
  refine ⟨by simp [dotProduct], ⟨0, Submodule.zero_mem _, 0, by simp, ?_⟩, ?_, ?_⟩
  · intro v hv hvψ
    refine absurd ?_ hv
    rw [hy v]
    simp only [dotProduct, Fintype.sum_unique, Pi.star_apply, mul_one, star_eq_zero] at hvψ
    rw [(congrArg v (Subsingleton.elim _ _)).trans hvψ, zero_smul]
  · unfold SpanR
    rw [eq_top_iff]
    intro y _
    have h1 : (fun _ => 1 : Idx 0 → ℂ) ∈ Submodule.span ℝ
        ({v | ∃ p : PL 0, wt p ≤ 0 ∧ v = hpauli p *ᵥ (fun _ => 1 : Idx 0 → ℂ)} ∪
          {Complex.I • (fun _ => 1 : Idx 0 → ℂ)}) :=
      Submodule.subset_span (Or.inl ⟨0, by simp, by rw [Top.hpauli_zero, Matrix.one_mulVec]⟩)
    have h2 : Complex.I • (fun _ => 1 : Idx 0 → ℂ) ∈ Submodule.span ℝ
        ({v | ∃ p : PL 0, wt p ≤ 0 ∧ v = hpauli p *ᵥ (fun _ => 1 : Idx 0 → ℂ)} ∪
          {Complex.I • (fun _ => 1 : Idx 0 → ℂ)}) :=
      Submodule.subset_span (Or.inr rfl)
    rw [hy y]
    exact smul_mem_of_I_smul_mem _ h1 h2 _
  · unfold SpanC
    rw [eq_top_iff]
    intro y _
    rw [hy y]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨0, by simp, by rw [pauli_zero, Matrix.one_mulVec]⟩)

/-- **Product with `|0⟩`.** If `ψ` has datum `(K_H, r, c)`, then `|0⟩ ⊗ ψ` has datum
`(max K_H 1, max r (c + 1), c + 1)`. -/
theorem datum_tens {KH r c : ℕ} {ψ : Idx n → ℂ} (h : Datum n KH r c ψ) :
    Datum (n + 1) (max KH 1) (max r (c + 1)) (c + 1) (tens 0 ψ) := by
  obtain ⟨hψ, ⟨H, hH, hgt⟩, hR, hC⟩ := h
  obtain ⟨H', hH', hL⟩ := exists_lifts hH
  refine ⟨?_, ⟨H' + hpauli (lab 0 1 (0 : PL n)), ?_,
    isGappedTop_tens (Top.isHermitian_of_mem_realLocalOps hH) hL hψ hgt⟩,
    spanR_tens hR hC, spanC_tens hC⟩
  · rw [dot_split, slice_tens, slice_tens, ite_eq_left rfl, ite_eq_right one_ne_zero, dotProduct_zero,
      add_zero]
    exact hψ
  · refine Submodule.add_mem _ (realLocalOps_mono (le_max_left _ _) hH')
      (Submodule.subset_span ⟨lab 0 1 0, ?_, rfl⟩)
    rw [wt_lab, ite_eq_left (Or.inr one_ne_zero), wt_zero]
    exact le_max_right _ _

/-- **`R(r)` is an open condition.** -/
theorem eventually_spanR {r : ℕ} {ψ₀ : Idx n → ℂ} (h : SpanR n r ψ₀) :
    ∀ᶠ ψ in 𝓝 ψ₀, SpanR n r ψ := by
  classical
  let B := Module.finBasis ℝ (Idx n → ℂ)
  choose Cb hCb hCbψ using fun j => (LA.spanR_iff r ψ₀).mp h (B j)
  have hdet0 : (LA.coordMat B Cb ψ₀).det ≠ 0 := by
    rw [LA.coordMat_eq_one B Cb hCbψ, Matrix.det_one]
    exact one_ne_zero
  have hdet : ∀ᶠ ψ in 𝓝 ψ₀, (LA.coordMat B Cb ψ).det ≠ 0 :=
    ((LA.continuous_coordMat B Cb).matrix_det.continuousAt).eventually_ne hdet0
  filter_upwards [hdet] with ψ hd
  exact (LA.spanR_iff r ψ).mpr fun y =>
    ⟨_, LA.solOp_mem B Cb hCb ψ y, LA.solOp_mulVec B Cb hd y⟩

/-- **Generic upgrade.** If a datum `(K_H, r, c)` exists on `n` qubits and `C(c')` holds at some
`n`-qubit vector, then a datum `(max K_H r, r, min c c')` exists. -/
theorem datum_upgrade {KH r c c' : ℕ} {ψ₀ : Idx n → ℂ} (h : Datum n KH r c ψ₀)
    (hw : ∃ φ : Idx n → ℂ, SpanC n c' φ) :
    ∃ ψ : Idx n → ℂ, Datum n (max KH r) r (min c c') ψ := by
  obtain ⟨hψ₀, ⟨H, hH, hgt⟩, hR, hC⟩ := h
  have hcert : CertS n (max KH r) H ψ₀ :=
    ⟨realLocalOps_mono (le_max_left _ _) hH, hgt, spanR_mono (le_max_right _ _) hR⟩
  obtain ⟨O, hOsub, hOopen, hOmem⟩ :=
    mem_nhds_iff.mp ((LA.eventually_certS hcert).and (eventually_spanR hR))
  -- the corresponding open subset of the sphere has positive measure
  set U : Set (Metric.sphere (0 : StateSpace n) 1) := {φ | (φ : StateSpace n).ofLp ∈ O} with hU
  have hUo : IsOpen U :=
    hOopen.preimage ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val)
  have hUne : U.Nonempty := ⟨⟨WithLp.toLp 2 ψ₀, by
    rw [mem_sphere_zero_iff_norm]
    exact LA.norm_toLp_eq_one hψ₀⟩, hOmem⟩
  have hpos : 0 < (volume : Measure (StateSpace n)).toSphere U := hUo.measure_pos _ hUne
  -- almost every point satisfies `C(c)` and `C(c')`
  have hae : ∀ᵐ (φ : Metric.sphere (0 : StateSpace n) 1)
      ∂(volume : Measure (StateSpace n)).toSphere,
      SpanC n c (φ : StateSpace n).ofLp ∧ SpanC n c' (φ : StateSpace n).ofLp :=
    (ae_spanC ⟨ψ₀, hC⟩).and (ae_spanC hw)
  obtain ⟨φ, hφU, hφc, hφc'⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne' (ae_restrict_of_ae hae)
  obtain ⟨hcertφ, hRφ⟩ := hOsub hφU
  obtain ⟨H', hH', hgt', -⟩ := hcertφ (star_dotProduct_self_of_sphere φ)
  refine ⟨(φ : StateSpace n).ofLp, star_dotProduct_self_of_sphere φ, ⟨H', hH', hgt'⟩, hRφ, ?_⟩
  rcases min_choice c c' with hm | hm <;> rw [hm] <;> assumption

end UDA.GL

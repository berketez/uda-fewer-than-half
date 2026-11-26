import UDA.Defs

/-!
# Algebra of the phase-free Pauli operators

Basic identities for the operators `pauli p = X^x Z^z` of `UDA/Defs.lean`:

* bits: `t + t = 0` in `𝔽₂`, the sign map `sgn` is a homomorphism `𝔽₂ → {±1}`;
* `bdot` and `symp` are symmetric and biadditive, `symp p p = 0`;
* the product rule `pauli_mul`, the adjoint `pauli_conjTranspose`, unitarity, the
  commutation rule `pauli_comm` and the trace formula `trace_pauli`;
* the weight is subadditive: `wt_add_le`.
-/

open Matrix
open scoped ComplexOrder

namespace UDA

variable {n : ℕ}

/-! ### Bits -/

/-- In `𝔽₂` every element is its own negative. -/
theorem zmod2_add_self (t : ZMod 2) : t + t = 0 := by
  fin_cases t <;> rfl

/-- A nonzero element of `𝔽₂` is `1`. -/
theorem zmod2_eq_one_of_ne_zero {t : ZMod 2} (h : t ≠ 0) : t = 1 := by
  fin_cases t
  · exact absurd rfl h
  · rfl

/-- Bit strings are their own negatives. -/
theorem bits_add_self (x : Fin n → ZMod 2) : x + x = 0 := by
  funext j
  exact zmod2_add_self (x j)

/-- Pauli labels are their own negatives. -/
theorem pl_add_self (p : PL n) : p + p = 0 :=
  Prod.ext (bits_add_self p.1) (bits_add_self p.2)

/-- `b = a + x ↔ a = b + x` for bit strings. -/
theorem bits_eq_add_comm {a b x : Fin n → ZMod 2} : b = a + x ↔ a = b + x := by
  constructor <;> intro h <;> rw [h, add_assoc, bits_add_self, add_zero]

/-! ### Signs -/

@[simp] theorem sgn_zero : sgn 0 = 1 := by simp [sgn]

@[simp] theorem sgn_one : sgn 1 = -1 := by simp [sgn]

/-- `sgn` is a homomorphism from `(𝔽₂, +)` to `({±1}, ·)`. -/
theorem sgn_add (s t : ZMod 2) : sgn (s + t) = sgn s * sgn t := by
  have key : ∀ s t : ZMod 2, (s + t = 0 ↔ (s = 0 ↔ t = 0)) := by decide
  have h := key s t
  unfold sgn
  by_cases hs : s = 0 <;> by_cases ht : t = 0
  · rw [ite_eq_left (h.mpr (iff_of_true hs ht)), ite_eq_left hs, ite_eq_left ht]
    norm_num
  · rw [ite_eq_right (fun h' => ht ((h.mp h').mp hs)), ite_eq_left hs, ite_eq_right ht]
    norm_num
  · rw [ite_eq_right (fun h' => hs ((h.mp h').mpr ht)), ite_eq_right hs, ite_eq_left ht]
    norm_num
  · rw [ite_eq_left (h.mpr (iff_of_false hs ht)), ite_eq_right hs, ite_eq_right ht]
    norm_num

theorem sgn_mul_self (t : ZMod 2) : sgn t * sgn t = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem sgn_ne_zero (t : ZMod 2) : sgn t ≠ 0 := by
  unfold sgn
  split_ifs <;> norm_num

@[simp] theorem star_sgn (t : ZMod 2) : star (sgn t) = sgn t := by
  unfold sgn
  split_ifs <;> simp

/-! ### Dot product and symplectic form -/

theorem bdot_comm (a b : Fin n → ZMod 2) : bdot a b = bdot b a := by
  unfold bdot
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem bdot_add_left (a a' b : Fin n → ZMod 2) : bdot (a + a') b = bdot a b + bdot a' b := by
  unfold bdot
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp [add_mul]

theorem bdot_add_right (a b b' : Fin n → ZMod 2) : bdot a (b + b') = bdot a b + bdot a b' := by
  rw [bdot_comm, bdot_add_left, bdot_comm b, bdot_comm b']

@[simp] theorem bdot_zero_left (b : Fin n → ZMod 2) : bdot 0 b = 0 := by simp [bdot]

@[simp] theorem bdot_zero_right (a : Fin n → ZMod 2) : bdot a 0 = 0 := by simp [bdot]

/-- The symplectic form in terms of dot products. -/
theorem symp_eq (p q : PL n) : symp p q = bdot p.1 q.2 + bdot p.2 q.1 := by
  unfold symp bdot
  rw [Finset.sum_add_distrib]

theorem symp_comm (p q : PL n) : symp p q = symp q p := by
  rw [symp_eq, symp_eq, bdot_comm p.1, bdot_comm p.2, add_comm]

theorem symp_self (p : PL n) : symp p p = 0 := by
  rw [symp_eq, bdot_comm p.2, zmod2_add_self]

theorem symp_add_left (p p' q : PL n) : symp (p + p') q = symp p q + symp p' q := by
  simp only [symp_eq, Prod.fst_add, Prod.snd_add, bdot_add_left]
  abel

theorem symp_add_right (p q q' : PL n) : symp p (q + q') = symp p q + symp p q' := by
  rw [symp_comm, symp_add_left, symp_comm q, symp_comm q']

@[simp] theorem symp_zero_left (q : PL n) : symp 0 q = 0 := by simp [symp_eq]

@[simp] theorem symp_zero_right (p : PL n) : symp p 0 = 0 := by simp [symp_eq]

/-! ### Weight -/

/-- The weight is the size of the support, i.e. of the set of qubits on which the label acts nontrivially. -/
theorem wt_eq_card (p : PL n) :
    wt p = (Finset.univ.filter fun j => p.1 j ≠ 0 ∨ p.2 j ≠ 0).card := rfl

@[simp] theorem wt_zero : wt (0 : PL n) = 0 := by simp [wt]

theorem wt_add_le (p q : PL n) : wt (p + q) ≤ wt p + wt q := by
  unfold wt
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Prod.fst_add,
    Prod.snd_add, Pi.add_apply] at hj ⊢
  by_contra hc
  push Not at hc
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hc
  rw [h1, h2, h3, h4] at hj
  simp at hj

theorem wt_le (p : PL n) : wt p ≤ n := by
  unfold wt
  exact le_trans (Finset.card_le_univ _) (by simp)

/-! ### Pauli operators -/

theorem pauli_apply (p : PL n) (a b : Idx n) :
    pauli p a b = if a = b + p.1 then sgn (bdot p.2 b) else 0 := rfl

@[simp] theorem pauli_zero : pauli (0 : PL n) = 1 := by
  ext a b
  simp only [pauli, Prod.fst_zero, Prod.snd_zero, add_zero, bdot_zero_left, sgn_zero,
    Matrix.one_apply]

/-- Product rule: `X^x Z^z X^x' Z^z' = (-1)^(z·x') X^(x+x') Z^(z+z')`. -/
theorem pauli_mul (p q : PL n) : pauli p * pauli q = sgn (bdot p.2 q.1) • pauli (p + q) := by
  ext a c
  simp only [Matrix.mul_apply, Matrix.smul_apply, pauli, smul_eq_mul, Prod.fst_add,
    Prod.snd_add]
  rw [Finset.sum_eq_single (c + q.1)]
  · by_cases h : a = c + (p.1 + q.1)
    · have h' : a = c + q.1 + p.1 := by rw [h]; abel
      rw [ite_eq_left h', ite_eq_left rfl, ite_eq_left h, bdot_add_right, bdot_add_left, sgn_add, sgn_add]
      ring
    · have h' : ¬ a = c + q.1 + p.1 := by
        intro h'
        apply h
        rw [h']
        abel
      rw [ite_eq_right h', ite_eq_right h]
      simp
  · intro b _ hb
    rw [ite_eq_right hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Adjoint: `(X^x Z^z)ᴴ = Z^z X^x = (-1)^(x·z) X^x Z^z`. -/
theorem pauli_conjTranspose (p : PL n) : (pauli p)ᴴ = sgn (bdot p.1 p.2) • pauli p := by
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, pauli, smul_eq_mul]
  by_cases h : a = b + p.1
  · have h' : b = a + p.1 := bits_eq_add_comm.mpr h
    rw [ite_eq_left h', ite_eq_left h, star_sgn, h, bdot_add_right, sgn_add, bdot_comm p.1 p.2]
    ring
  · have h' : ¬ b = a + p.1 := fun h' => h (bits_eq_add_comm.mp h')
    rw [ite_eq_right h', ite_eq_right h]
    simp

theorem pauli_conjTranspose_mul_self (p : PL n) : (pauli p)ᴴ * pauli p = 1 := by
  rw [pauli_conjTranspose, Matrix.smul_mul, pauli_mul, smul_smul, pl_add_self, pauli_zero,
    bdot_comm p.2 p.1, sgn_mul_self, one_smul]

theorem pauli_mul_conjTranspose_self (p : PL n) : pauli p * (pauli p)ᴴ = 1 := by
  rw [pauli_conjTranspose, Matrix.mul_smul, pauli_mul, smul_smul, pl_add_self, pauli_zero,
    bdot_comm p.2 p.1, sgn_mul_self, one_smul]

/-- Commutation rule: two Pauli operators commute or anticommute according to `symp`. -/
theorem pauli_comm (p q : PL n) :
    pauli p * pauli q = sgn (symp p q) • (pauli q * pauli p) := by
  rw [pauli_mul, pauli_mul, smul_smul, add_comm q p, symp_eq, sgn_add, bdot_comm p.1 q.2]
  congr 1
  linear_combination (-sgn (bdot p.2 q.1)) * sgn_mul_self (bdot q.2 p.1)

/-- Character sum over `𝔽₂ⁿ`: `∑_a (-1)^(z·a) = 2^n [z = 0]`. -/
theorem sum_sgn_bdot (z : Fin n → ZMod 2) :
    ∑ a : Idx n, sgn (bdot z a) = if z = 0 then (2 : ℂ) ^ n else 0 := by
  split_ifs with hz
  · subst hz
    simp
  · obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (funext h)
    have he : ∀ a : Idx n, sgn (bdot z (a + Pi.single j 1)) = -sgn (bdot z a) := by
      intro a
      have h1 : bdot z (Pi.single j (1 : ZMod 2)) = 1 := by
        simp [bdot, Pi.single_apply, zmod2_eq_one_of_ne_zero hj]
      rw [bdot_add_right, sgn_add, h1, sgn_one, mul_neg_one]
    have hS := Equiv.sum_comp (Equiv.addRight (Pi.single j (1 : ZMod 2) : Idx n))
      (fun a => sgn (bdot z a))
    simp only [Equiv.coe_addRight, he, Finset.sum_neg_distrib] at hS
    linear_combination (-1 / 2 : ℂ) * hS

/-- Trace of a Pauli operator: `2^n` for the identity, `0` otherwise. -/
theorem trace_pauli (p : PL n) : (pauli p).trace = if p = 0 then (2 : ℂ) ^ n else 0 := by
  split_ifs with hp
  · rw [hp, pauli_zero, Matrix.trace_one]
    simp
  · simp only [Matrix.trace, Matrix.diag_apply, pauli]
    by_cases h1 : p.1 = 0
    · have h2 : p.2 ≠ 0 := fun h2 => hp (Prod.ext h1 h2)
      simp only [h1, add_zero, ite_true]
      rw [sum_sgn_bdot, ite_eq_right h2]
    · apply Finset.sum_eq_zero
      intro a _
      rw [ite_eq_right]
      intro h
      exact h1 (left_eq_add.mp h)

/-- Action on vectors: `(pauli p *ᵥ v) a = (-1)^(z·(a+x)) v (a + x)`. -/
theorem pauli_mulVec_apply (p : PL n) (v : Idx n → ℂ) (a : Idx n) :
    (pauli p *ᵥ v) a = sgn (bdot p.2 (a + p.1)) * v (a + p.1) := by
  simp only [Matrix.mulVec, dotProduct, pauli]
  rw [Finset.sum_eq_single (a + p.1)]
  · rw [ite_eq_left (bits_eq_add_comm.mp rfl)]
  · intro b _ hb
    rw [ite_eq_right (fun h => hb (bits_eq_add_comm.mpr h)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end UDA

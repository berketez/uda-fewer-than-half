import UDA.Stabilizer
import UDA.Covering

/-!
# Witnesses of the complex spanning condition on few qubits

For `(n, R) = (2, 1), (3, 1), (5, 2), (6, 2), (7, 2)` (and `(4, 2)`) we exhibit a symmetric
matrix `A` over `𝔽₂` whose graph `S_A = {(x, A x)}` is a Lagrangian subspace of covering radius
at most `R`. By `UDA.exists_spanC_of_lagrangian`, a stabilizer state of `S_A` (a graph state)
then satisfies the complex spanning condition `C(R)` (`UDA.SpanC n R`).

The covering radius is checked by the kernel on a bit-mask encoding: a bit string of length `n`
is a natural number below `2^n`, a matrix is the list of the masks of its columns, and the test
`UDA.Wit.covers` asks that for every syndrome `s` there be a mask `a` such that the label
`(a, s + A a)` has weight at most `R`. The lemma `UDA.Wit.coversWithin_of_covers` connects the
Boolean test with `UDA.CoversWithin`: a label `v = (v₁, v₂)` has syndrome `s = v₂ + A v₁`, and
`v + (x, A x) = (a, s + A a)` for `x = v₁ + a`.
-/

open Matrix

namespace UDA

namespace Wit

/-! ### Bit masks -/

/-- Bit `j` of the mask `m`, as an element of `𝔽₂`. -/
def bit (m j : ℕ) : ZMod 2 := if m.testBit j then 1 else 0

/-- The bit string of length `n` with mask `m`. -/
def vec (n m : ℕ) : Fin n → ZMod 2 := fun j => bit m j

/-- The `n × n` matrix over `𝔽₂` whose `i`-th column has mask `rows i`. -/
def adj (n : ℕ) (rows : ℕ → ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun j i => bit (rows i) j

/-- The number of set bits of `m` among the first `n` bits. -/
def cnt : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, m => cnt n m + if m.testBit n then 1 else 0

/-- The mask of `A a`: the sum (xor) of the columns selected by the first `k` bits of `a`. -/
def mulMask (rows : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, a => mulMask rows k a ^^^ if a.testBit k then rows k else 0

/-- Bounded universal quantifier, as a Boolean. -/
def allLt : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | k + 1, f => f k && allLt k f

/-- Bounded existential quantifier, as a Boolean. -/
def anyLt : ℕ → (ℕ → Bool) → Bool
  | 0, _ => false
  | k + 1, f => f k || anyLt k f

/-- The Boolean covering test: for every syndrome `s` there is `a` such that the label
`(a, s + A a)` has weight at most `R`. -/
def covers (n R : ℕ) (rows : ℕ → ℕ) : Bool :=
  allLt (2 ^ n) fun s => anyLt (2 ^ n) fun a =>
    Nat.ble (cnt n (a ||| (s ^^^ mulMask rows n a))) R

/-- The Boolean symmetry test for the matrix with column masks `rows`. -/
def symmetric (n : ℕ) (rows : ℕ → ℕ) : Bool :=
  allLt n fun i => allLt n fun j => (rows i).testBit j == (rows j).testBit i

/-- The column masks given by a list. -/
def rowsOf (l : List ℕ) : ℕ → ℕ := fun i => l.getD i 0

/-- `allLt` is the bounded universal quantifier. -/
theorem allLt_iff (k : ℕ) (f : ℕ → Bool) : allLt k f = true ↔ ∀ i < k, f i = true := by
  induction k with
  | zero => simp [allLt]
  | succ k ih => rw [allLt, Bool.and_eq_true, ih, Nat.forall_lt_succ_right, and_comm]

/-- `anyLt` is the bounded existential quantifier. -/
theorem anyLt_iff (k : ℕ) (f : ℕ → Bool) : anyLt k f = true ↔ ∃ i < k, f i = true := by
  induction k with
  | zero => simp [anyLt]
  | succ k ih => rw [anyLt, Bool.or_eq_true, ih, Nat.exists_lt_succ_right, or_comm]

/-- A bit is nonzero iff it is set in the mask. -/
theorem bit_ne_zero_iff (m j : ℕ) : bit m j ≠ 0 ↔ m.testBit j = true := by
  unfold bit
  split_ifs with h <;> simp [h]

/-- Xor of masks is addition of bits in `𝔽₂`. -/
theorem bit_xor (x y j : ℕ) : bit (x ^^^ y) j = bit x j + bit y j := by
  unfold bit
  rw [Nat.testBit_xor]
  cases x.testBit j <;> cases y.testBit j <;> decide

/-- Xor of masks is addition of bit strings. -/
theorem vec_xor (n x y : ℕ) : vec n (x ^^^ y) = vec n x + vec n y :=
  funext fun j => bit_xor x y j

/-- The bits of `mulMask`, as sums over the selected columns. -/
theorem bit_mulMask (rows : ℕ → ℕ) (k a j : ℕ) :
    bit (mulMask rows k a) j = ∑ i ∈ Finset.range k, bit (rows i) j * bit a i := by
  induction k with
  | zero => simp [mulMask, bit]
  | succ k ih =>
    rw [mulMask, bit_xor, ih, Finset.sum_range_succ]
    congr 1
    by_cases h : a.testBit k = true <;> simp [bit, h]

/-- The mask of `A a` represents the matrix-vector product. -/
theorem vec_mulMask (n : ℕ) (rows : ℕ → ℕ) (a : ℕ) :
    vec n (mulMask rows n a) = adj n rows *ᵥ vec n a := by
  funext j
  simp only [vec, adj, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [bit_mulMask, Fin.sum_univ_eq_sum_range (fun i => bit (rows i) j * bit a i) n]

/-- `cnt` counts the set bits among the first `n`. -/
theorem cnt_eq_card (n m : ℕ) :
    cnt n m = (Finset.univ.filter fun j : Fin n => m.testBit j = true).card := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    rw [cnt, ih, Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
    simp

/-- The weight of a label given by two masks. -/
theorem wt_vec (n a b : ℕ) : wt ((vec n a, vec n b) : PL n) = cnt n (a ||| b) := by
  rw [cnt_eq_card]
  unfold wt
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, vec, bit_ne_zero_iff, Nat.testBit_or,
    Bool.or_eq_true]

/-- Every bit string of length `n` has a mask below `2^n`. -/
theorem exists_vec_eq (n : ℕ) (σ : Fin n → ZMod 2) : ∃ s < 2 ^ n, vec n s = σ := by
  refine ⟨Nat.ofBits fun j => decide (σ j ≠ 0), Nat.ofBits_lt_two_pow _, ?_⟩
  funext j
  simp only [vec, bit, Nat.testBit_ofBits_lt _ _ j.isLt]
  by_cases h : σ j = 0
  · simp [h]
  · simp [zmod2_eq_one_of_ne_zero h]

/-! ### Graph Lagrangians -/

variable {n : ℕ}

/-- The graph `x ↦ (x, A x)` of a matrix over `𝔽₂`, as a linear map. -/
def grLin (A : Matrix (Fin n) (Fin n) (ZMod 2)) : (Fin n → ZMod 2) →ₗ[ZMod 2] PL n :=
  LinearMap.prod LinearMap.id (Matrix.mulVecLin A)

/-- `grLin A` is the graph map `Cov.gr A`. -/
theorem grLin_apply (A : Matrix (Fin n) (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    grLin A x = Cov.gr A x := rfl

/-- The graph map is injective. -/
theorem grLin_injective (A : Matrix (Fin n) (Fin n) (ZMod 2)) : Function.Injective (grLin A) :=
  fun _ _ h => congrArg Prod.fst h

/-- The graph of a symmetric matrix is a Lagrangian subspace. -/
theorem isLagrangian_range {A : Matrix (Fin n) (Fin n) (ZMod 2)} (hA : Aᵀ = A) :
    IsLagrangian (LinearMap.range (grLin A)) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact Cov.symp_gr hA x y
  · rw [Nat.card_congr (LinearEquiv.ofInjective _ (grLin_injective A)).symm.toEquiv,
      Nat.card_eq_fintype_card, Cov.card_bits]

/-- The Boolean symmetry test implies that the matrix is symmetric. -/
theorem adj_transpose {n : ℕ} {rows : ℕ → ℕ} (h : symmetric n rows = true) :
    (adj n rows)ᵀ = adj n rows := by
  rw [symmetric, allLt_iff] at h
  ext i j
  have h1 := (allLt_iff _ _).1 (h i i.isLt) j j.isLt
  simp only [Matrix.transpose_apply, adj, Matrix.of_apply, bit]
  rw [beq_iff_eq] at h1
  rw [h1]

/-- **The Boolean covering test is sound.** -/
theorem coversWithin_of_covers (n R : ℕ) (rows : ℕ → ℕ) (h : covers n R rows = true) :
    CoversWithin (LinearMap.range (grLin (adj n rows))) R := by
  intro v
  obtain ⟨s, hs, hsv⟩ := exists_vec_eq n (v.2 + adj n rows *ᵥ v.1)
  rw [covers, allLt_iff] at h
  obtain ⟨a, -, hle⟩ := (anyLt_iff _ _).1 (h s hs)
  refine ⟨grLin (adj n rows) (v.1 + vec n a), LinearMap.mem_range_self _ _, ?_⟩
  have hv : v + grLin (adj n rows) (v.1 + vec n a) =
      (vec n a, vec n (s ^^^ mulMask rows n a)) := by
    rw [vec_xor, vec_mulMask, hsv, grLin_apply, Cov.gr]
    refine Prod.ext ?_ ?_
    · change v.1 + (v.1 + vec n a) = vec n a
      rw [← add_assoc, bits_add_self, zero_add]
    · change v.2 + adj n rows *ᵥ (v.1 + vec n a) = v.2 + adj n rows *ᵥ v.1 + adj n rows *ᵥ vec n a
      rw [Matrix.mulVec_add, add_assoc]
  rw [hv, wt_vec]
  exact Nat.le_of_ble_eq_true hle

/-- A symmetric matrix passing the covering test with radius `R` yields a state satisfying the
complex spanning condition `C(R)`. -/
theorem exists_spanC (n R : ℕ) (rows : ℕ → ℕ) (hs : symmetric n rows = true)
    (hc : covers n R rows = true) : ∃ ψ : Idx n → ℂ, SpanC n R ψ :=
  exists_spanC_of_lagrangian _ (isLagrangian_range (adj_transpose hs))
    (coversWithin_of_covers n R rows hc)

/-! ### The witnesses -/

/-- `C(1)` holds at some two-qubit vector. -/
theorem spanC_2_1 : ∃ ψ : Idx 2 → ℂ, SpanC 2 1 ψ :=
  exists_spanC 2 1 (rowsOf [2, 1]) (by decide +kernel) (by decide +kernel)

/-- `C(1)` holds at some three-qubit vector. -/
theorem spanC_3_1 : ∃ ψ : Idx 3 → ℂ, SpanC 3 1 ψ :=
  exists_spanC 3 1 (rowsOf [2, 5, 2]) (by decide +kernel) (by decide +kernel)

/-- `C(2)` holds at some four-qubit vector. -/
theorem spanC_4_2 : ∃ ψ : Idx 4 → ℂ, SpanC 4 2 ψ :=
  exists_spanC 4 2 (rowsOf [12, 8, 9, 7]) (by decide +kernel) (by decide +kernel)

/-- `C(2)` holds at some five-qubit vector. -/
theorem spanC_5_2 : ∃ ψ : Idx 5 → ℂ, SpanC 5 2 ψ :=
  exists_spanC 5 2 (rowsOf [14, 13, 3, 19, 8]) (by decide +kernel) (by decide +kernel)

/-- `C(2)` holds at some six-qubit vector. -/
theorem spanC_6_2 : ∃ ψ : Idx 6 → ℂ, SpanC 6 2 ψ :=
  exists_spanC 6 2 (rowsOf [52, 44, 35, 34, 33, 31]) (by decide +kernel) (by decide +kernel)

/-- `C(2)` holds at some seven-qubit vector. -/
theorem spanC_7_2 : ∃ ψ : Idx 7 → ℂ, SpanC 7 2 ψ :=
  exists_spanC 7 2 (rowsOf [44, 100, 27, 69, 4, 67, 42]) (by decide +kernel) (by decide +kernel)

end Wit

end UDA

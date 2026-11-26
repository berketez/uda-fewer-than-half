import UDA.Ball

/-!
# A Lagrangian subspace with small covering radius

We prove `UDA.exists_lagrangian_covering`: if
`2 ^ (m * (2 ^ t + 2)) < (2 ^ m + ballCard m L) ^ (2 ^ t)` then there is a Lagrangian subspace
of `𝔽₂^(2 (m + t))` all of whose cosets contain a label of weight at most `L + t`.

The proof is an elementary counting argument.

1. *Graph Lagrangians.* For a symmetric matrix `A` over `𝔽₂` the graph `{(x, A x)}` is
   isotropic.
2. *Second moment.* Averaging over all symmetric matrices `A` and using the Cauchy–Schwarz
   inequality, some `A` has few "bad" labels `v` (those with `v + (x, A x)` outside the ball
   `B` of radius `L` for every `x`): `#bad * (2 ^ m + #B) ≤ (2 ^ m) ^ 3`.
3. *Squaring.* Adding a suitable extra vector `u` to the generating set replaces the bad set
   `U` by `U ∩ (U + u)`, whose density is at most the square of the density of `U`.
   After `t` steps the bad set is empty.
4. *Ancillas.* The `t` extra vectors destroy isotropy; it is restored by `t` ancilla qubits.
   The weight grows by at most `t`.
-/

open Finset Matrix

namespace UDA

namespace Cov

/-! ### Double counting in a finite abelian group -/

section Counting

theorem card_filter_eq_sum {V : Type*} [Fintype V] [DecidableEq V] (B : Finset V)
    (P : V → Prop) [DecidablePred P] :
    (B.filter P).card = ∑ p : V, (if p ∈ B then 1 else 0) * (if P p then 1 else 0) := by
  rw [Finset.card_filter, ← Finset.sum_subset (Finset.subset_univ B)]
  · exact Finset.sum_congr rfl fun p hp => by simp [hp]
  · intro p _ hp; simp [hp]

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- `∑_u #(U ∩ (U - u)) = (#U)²`. -/
theorem sum_card_filter_add (U : Finset V) :
    ∑ u : V, (U.filter fun v => v + u ∈ U).card = U.card ^ 2 := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have h : ∀ v ∈ U, (∑ u : V, if v + u ∈ U then 1 else 0) = U.card := by
    intro v _
    have h := Equiv.sum_comp (Equiv.addLeft v) (fun w => if w ∈ U then (1 : ℕ) else 0)
    exact h.trans (by simp)
  rw [Finset.sum_congr rfl h]
  simp [sq]

variable {X : Type*} [Fintype X]

/-- The number of `x` with `v + g x ∈ B`. -/
def cnt (g : X → V) (B : Finset V) (v : V) : ℕ := (univ.filter fun x => v + g x ∈ B).card

omit [Fintype V] in
theorem cnt_eq_zero_iff (g : X → V) (B : Finset V) (v : V) :
    cnt g B v = 0 ↔ ∀ x, v + g x ∉ B := by
  simp [cnt, Finset.filter_eq_empty_iff]

/-- First moment. -/
theorem sum_cnt (g : X → V) (B : Finset V) : ∑ v, cnt g B v = Fintype.card X * B.card := by
  unfold cnt
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have h : ∀ x : X, (∑ v : V, if v + g x ∈ B then 1 else 0) = B.card := by
    intro x
    have h := Equiv.sum_comp (Equiv.addRight (g x)) (fun w => if w ∈ B then (1 : ℕ) else 0)
    exact h.trans (by simp)
  simp [h]

/-- Second moment, for an additive map `g`. -/
theorem sum_cnt_sq [AddCommGroup X] (g : X → V) (hg : ∀ x a, g (x + a) = g x + g a) (B : Finset V) :
    ∑ v, cnt g B v ^ 2 =
      Fintype.card X * ∑ a : X, (B.filter fun p => p + g a ∈ B).card := by
  have hx : ∀ x : X,
      (∑ v : V, ∑ x' : X, (if v + g x ∈ B then 1 else 0) * (if v + g x' ∈ B then 1 else 0)) =
        ∑ p : V, ∑ a : X, (if p ∈ B then 1 else 0) * (if p + g a ∈ B then 1 else 0) := by
    intro x
    have h1 := Equiv.sum_comp (Equiv.addRight (g x))
      (fun p => ∑ a : X, (if p ∈ B then 1 else 0) * (if p + g a ∈ B then (1 : ℕ) else 0))
    refine Eq.trans ?_ h1
    refine Finset.sum_congr rfl fun v _ => ?_
    have h2 := Equiv.sum_comp (Equiv.addLeft x)
      (fun x' => (if v + g x ∈ B then 1 else 0) * (if v + g x' ∈ B then (1 : ℕ) else 0))
    refine h2.symm.trans ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Equiv.coe_addLeft, Equiv.coe_addRight, hg, add_assoc]
    split_ifs <;> simp_all
  calc ∑ v, cnt g B v ^ 2
      = ∑ v : V, ∑ x : X, ∑ x' : X,
          (if v + g x ∈ B then 1 else 0) * (if v + g x' ∈ B then 1 else 0) := by
        simp only [cnt, Finset.card_filter, sq, Finset.sum_mul_sum]
    _ = ∑ x : X, ∑ v : V, ∑ x' : X,
          (if v + g x ∈ B then 1 else 0) * (if v + g x' ∈ B then 1 else 0) := Finset.sum_comm
    _ = ∑ _x : X, ∑ p : V, ∑ a : X,
          (if p ∈ B then 1 else 0) * (if p + g a ∈ B then 1 else 0) :=
        Finset.sum_congr rfl fun x _ => hx x
    _ = Fintype.card X * ∑ a : X, (B.filter fun p => p + g a ∈ B).card := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.sum_comm]
        simp only [card_filter_eq_sum]

/-- Cauchy–Schwarz on the support of `cnt`. -/
theorem sq_sum_cnt_le (g : X → V) (B : Finset V) :
    (∑ v, cnt g B v) ^ 2 ≤ (univ.filter fun v => 0 < cnt g B v).card * ∑ v, cnt g B v ^ 2 := by
  have h1 : ∑ v ∈ univ.filter (fun v => 0 < cnt g B v), cnt g B v = ∑ v, cnt g B v :=
    Finset.sum_filter_of_ne fun v _ hv => Nat.pos_of_ne_zero hv
  have h2 : ∑ v ∈ univ.filter (fun v => 0 < cnt g B v), cnt g B v ^ 2 ≤ ∑ v, cnt g B v ^ 2 :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  calc (∑ v, cnt g B v) ^ 2
      = (∑ v ∈ univ.filter (fun v => 0 < cnt g B v), cnt g B v) ^ 2 := by rw [h1]
    _ ≤ (univ.filter fun v => 0 < cnt g B v).card *
          ∑ v ∈ univ.filter (fun v => 0 < cnt g B v), cnt g B v ^ 2 := by
        exact_mod_cast sq_sum_le_card_mul_sum_sq (s := univ.filter fun v => 0 < cnt g B v)
          (f := fun v => cnt g B v)
    _ ≤ _ := Nat.mul_le_mul_left _ h2

theorem card_pos_add_card_zero (g : X → V) (B : Finset V) :
    (univ.filter fun v => 0 < cnt g B v).card + (univ.filter fun v => cnt g B v = 0).card =
      Fintype.card V := by
  rw [← Finset.card_univ, ← Finset.card_union_of_disjoint]
  · congr 1
    ext v
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact (Nat.eq_zero_or_pos _).symm
  · rw [Finset.disjoint_filter]
    intro v _ h1 h2
    omega

end Counting

/-! ### Pure arithmetic -/

theorem arith1 {d b P Z M : ℕ} (hd : 0 < d) (hb : 0 < b) (hPZ : P + Z = d ^ 2)
    (hcs : (d * b) ^ 2 ≤ P * (d * M)) (hZ : d ^ 3 < Z * (d + b)) : b * (d + b) < d * M := by
  have e : (P + Z) * (d + b) = d ^ 2 * (d + b) := by rw [hPZ]
  have h1 : P * (d + b) < d ^ 2 * b := by nlinarith
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    have : 0 < (d * b) ^ 2 := by positivity
    simp at hcs
    omega
  · have h2 : P * (d + b) * (d * M) < d ^ 2 * b * (d * M) :=
      Nat.mul_lt_mul_of_pos_right h1 (by positivity)
    have h3 : (d * b) ^ 2 * (d + b) ≤ P * (d * M) * (d + b) := Nat.mul_le_mul_right _ hcs
    have h4 : d ^ 2 * b * (b * (d + b)) < d ^ 2 * b * (d * M) := by
      calc d ^ 2 * b * (b * (d + b)) = (d * b) ^ 2 * (d + b) := by ring
        _ ≤ P * (d * M) * (d + b) := h3
        _ = P * (d + b) * (d * M) := by ring
        _ < d ^ 2 * b * (d * M) := h2
    exact Nat.lt_of_mul_lt_mul_left h4

/-! ### Graphs of symmetric matrices -/

section Sym

variable {m : ℕ}

theorem zmod2_eq_one {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  revert c; decide

theorem two_eq_zero : (2 : ZMod 2) = 0 := rfl

theorem card_bits (m : ℕ) : Fintype.card (Fin m → ZMod 2) = 2 ^ m := by
  simp [ZMod.card]

theorem card_PL (m : ℕ) : Fintype.card (PL m) = (2 ^ m) ^ 2 := by
  rw [Fintype.card_prod, card_bits, sq]

/-- The graph `x ↦ (x, A x)` of a matrix. -/
def gr (A : Matrix (Fin m) (Fin m) (ZMod 2)) (x : Fin m → ZMod 2) : PL m := (x, A *ᵥ x)

theorem gr_add (A : Matrix (Fin m) (Fin m) (ZMod 2)) (x a : Fin m → ZMod 2) :
    gr A (x + a) = gr A x + gr A a := by
  simp [gr, Matrix.mulVec_add]

theorem gr_zero (A : Matrix (Fin m) (Fin m) (ZMod 2)) : gr A 0 = 0 := by
  simp [gr]

/-- The finite set of symmetric matrices over `𝔽₂`. -/
def symm (m : ℕ) : Finset (Matrix (Fin m) (Fin m) (ZMod 2)) := univ.filter fun A => Aᵀ = A

theorem mem_symm {A : Matrix (Fin m) (Fin m) (ZMod 2)} : A ∈ symm m ↔ Aᵀ = A := by
  simp [symm]

theorem symm_nonempty : (symm m).Nonempty := ⟨0, by simp [mem_symm]⟩

/-- For `a ≠ 0` the map `A ↦ A a` from symmetric matrices to vectors is surjective. -/
theorem exists_symm_mulVec_eq {a : Fin m → ZMod 2} (ha : a ≠ 0) (w : Fin m → ZMod 2) :
    ∃ A : Matrix (Fin m) (Fin m) (ZMod 2), Aᵀ = A ∧ A *ᵥ a = w := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    exact ha (funext fun i => not_not.1 fun hi => h ⟨i, hi⟩)
  have hi1 : a i = 1 := zmod2_eq_one hi
  refine ⟨Matrix.of fun j k => (if j = i then w k else 0) + (if k = i then w j else 0) +
      (if j = i ∧ k = i then w ⬝ᵥ a else 0), ?_, ?_⟩
  · ext j k
    simp only [Matrix.transpose_apply, Matrix.of_apply, and_comm]
    ring
  · ext j
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
      ite_mul, zero_mul]
    by_cases hj : j = i
    · simp [hj, hi1]
      linear_combination (∑ x, w x * a x) * two_eq_zero
    · simp [hj, hi1]

/-- All fibres of `A ↦ A a` (`a ≠ 0`) on symmetric matrices have the same size. -/
theorem card_fibre {a : Fin m → ZMod 2} (ha : a ≠ 0) (w : Fin m → ZMod 2) :
    2 ^ m * ((symm m).filter fun A => A *ᵥ a = w).card = (symm m).card := by
  have key : ∀ w : Fin m → ZMod 2, ((symm m).filter fun A => A *ᵥ a = w).card =
      ((symm m).filter fun A => A *ᵥ a = 0).card := by
    intro w
    obtain ⟨Aw, hAw, hw⟩ := exists_symm_mulVec_eq ha w
    refine Finset.card_bij' (fun A _ => A - Aw) (fun A _ => A + Aw) ?_ ?_ ?_ ?_
    · intro A hA
      simp only [Finset.mem_filter, mem_symm] at hA ⊢
      exact ⟨by rw [Matrix.transpose_sub, hA.1, hAw], by rw [Matrix.sub_mulVec, hA.2, hw, sub_self]⟩
    · intro A hA
      simp only [Finset.mem_filter, mem_symm] at hA ⊢
      exact ⟨by rw [Matrix.transpose_add, hA.1, hAw], by rw [Matrix.add_mulVec, hA.2, hw, zero_add]⟩
    · intro A _; simp
    · intro A _; simp
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun A : Matrix (Fin m) (Fin m) (ZMod 2) => A *ᵥ a) (s := symm m) (t := univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  rw [h, Finset.sum_congr rfl (fun w _ => key w), Finset.sum_const, Finset.card_univ, key w,
    card_bits, smul_eq_mul]

/-- The off-diagonal part of the second moment, summed over all symmetric matrices. -/
theorem sum_symm_corr (B : Finset (PL m)) :
    2 ^ m * ∑ A ∈ symm m, ∑ a : Fin m → ZMod 2, (B.filter fun p => p + gr A a ∈ B).card ≤
      2 ^ m * (symm m).card * B.card + (symm m).card * B.card ^ 2 := by
  have hper : ∀ a : Fin m → ZMod 2,
      2 ^ m * ∑ A ∈ symm m, (B.filter fun p => p + gr A a ∈ B).card ≤
        (if a = 0 then 2 ^ m * (symm m).card * B.card else 0) +
          (symm m).card * ∑ w : Fin m → ZMod 2, (B.filter fun p => p + (a, w) ∈ B).card := by
    intro a
    by_cases ha : a = 0
    · subst ha
      have h0 : ∀ A : Matrix (Fin m) (Fin m) (ZMod 2),
          (B.filter fun p => p + gr A 0 ∈ B) = B := by
        intro A
        rw [gr_zero]
        simp
      simp only [h0, Finset.sum_const, smul_eq_mul, ite_true]
      rw [mul_assoc]
      exact Nat.le_add_right _ _
    · simp only [ha, ite_false, zero_add]
      have h1 : ∑ A ∈ symm m, (B.filter fun p => p + gr A a ∈ B).card =
          ∑ w : Fin m → ZMod 2, ((symm m).filter fun A => A *ᵥ a = w).card *
            (B.filter fun p => p + (a, w) ∈ B).card := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (g := fun A : Matrix (Fin m) (Fin m) (ZMod 2) => A *ᵥ a) (t := univ)
          (fun _ _ => Finset.mem_univ _)]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← smul_eq_mul, ← Finset.sum_const]
        refine Finset.sum_congr rfl fun A hA => ?_
        rw [Finset.mem_filter] at hA
        simp only [gr, hA.2]
      rw [h1, Finset.mul_sum, Finset.mul_sum]
      refine le_of_eq (Finset.sum_congr rfl fun w _ => ?_)
      rw [← mul_assoc, card_fibre ha w]
  have hq : ∑ a : Fin m → ZMod 2, ∑ w : Fin m → ZMod 2,
      (B.filter fun p => p + (a, w) ∈ B).card = B.card ^ 2 := by
    rw [← sum_card_filter_add B, Fintype.sum_prod_type]
  calc 2 ^ m * ∑ A ∈ symm m, ∑ a : Fin m → ZMod 2, (B.filter fun p => p + gr A a ∈ B).card
      = ∑ a : Fin m → ZMod 2, 2 ^ m * ∑ A ∈ symm m, (B.filter fun p => p + gr A a ∈ B).card := by
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ a : Fin m → ZMod 2, ((if a = 0 then 2 ^ m * (symm m).card * B.card else 0) +
          (symm m).card * ∑ w : Fin m → ZMod 2, (B.filter fun p => p + (a, w) ∈ B).card) :=
        Finset.sum_le_sum fun a _ => hper a
    _ = 2 ^ m * (symm m).card * B.card + (symm m).card * B.card ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hq]
        simp

/-- Some symmetric matrix has few labels that its graph does not move into `B`. -/
theorem exists_symm_small (B : Finset (PL m)) (hB : 0 < B.card) :
    ∃ A : Matrix (Fin m) (Fin m) (ZMod 2), Aᵀ = A ∧
      (univ.filter fun v => cnt (gr A) B v = 0).card * (2 ^ m + B.card) ≤ (2 ^ m) ^ 3 := by
  by_contra hcon
  have hcon' : ∀ A : Matrix (Fin m) (Fin m) (ZMod 2), Aᵀ = A →
      (2 ^ m) ^ 3 < (univ.filter fun v => cnt (gr A) B v = 0).card * (2 ^ m + B.card) :=
    fun A hA => not_le.1 fun hle => hcon ⟨A, hA, hle⟩
  have hlt : ∀ A ∈ symm m, B.card * (2 ^ m + B.card) <
      2 ^ m * ∑ a : Fin m → ZMod 2, (B.filter fun p => p + gr A a ∈ B).card := by
    intro A hA
    have hZ := hcon' A (mem_symm.1 hA)
    have hcs := sq_sum_cnt_le (gr A) B
    rw [sum_cnt, sum_cnt_sq (gr A) (gr_add A) B, card_bits] at hcs
    have hPZ := card_pos_add_card_zero (gr A) B
    rw [card_PL] at hPZ
    exact arith1 (by positivity) hB hPZ hcs hZ
  have h1 := Finset.sum_lt_sum_of_nonempty symm_nonempty hlt
  rw [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at h1
  have h2 := sum_symm_corr B
  nlinarith [h1, h2]

end Sym

/-! ### Squaring the density of the bad set -/

section Squaring

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V]
variable {X : Type*} [Fintype X]

/-- The labels `v` that no element `g x + ∑ i, l i • u i` moves into `B`. -/
def bad (B : Finset V) (g : X → V) {t : ℕ} (u : Fin t → V) : Finset V :=
  univ.filter fun v => ∀ (x : X) (l : Fin t → ZMod 2), v + (g x + ∑ i, l i • u i) ∉ B

theorem mem_bad {B : Finset V} {g : X → V} {t : ℕ} {u : Fin t → V} {v : V} :
    v ∈ bad B g u ↔ ∀ (x : X) (l : Fin t → ZMod 2), v + (g x + ∑ i, l i • u i) ∉ B := by
  simp [bad]

theorem bad_zero (B : Finset V) (g : X → V) (u : Fin 0 → V) :
    bad B g u = univ.filter fun v => cnt g B v = 0 := by
  ext v
  rw [mem_bad, Finset.mem_filter, cnt_eq_zero_iff]
  simp

/-- One more generator squares the density of the bad set. -/
theorem bad_step (B : Finset V) (g : X → V) {t : ℕ} (u : Fin t → V) :
    ∃ u₀ : V, (bad B g (Fin.cons u₀ u : Fin (t + 1) → V)).card * Fintype.card V ≤
      (bad B g u).card ^ 2 := by
  obtain ⟨u₀, -, hu₀⟩ := Finset.exists_le_of_sum_le (s := (univ : Finset V))
    (f := fun u₀ => ((bad B g u).filter fun v => v + u₀ ∈ bad B g u).card * Fintype.card V)
    (g := fun _ => (bad B g u).card ^ 2) Finset.univ_nonempty (by
      rw [← Finset.sum_mul, sum_card_filter_add, Finset.sum_const, Finset.card_univ, smul_eq_mul,
        mul_comm])
  refine ⟨u₀, le_trans (Nat.mul_le_mul_right _ (Finset.card_le_card ?_)) hu₀⟩
  intro v hv
  rw [mem_bad] at hv
  rw [Finset.mem_filter, mem_bad, mem_bad]
  constructor
  · intro x l
    have := hv x (Fin.cons 0 l)
    simpa [Fin.sum_univ_succ] using this
  · intro x l
    have := hv x (Fin.cons 1 l)
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, one_smul] at this
    have e : v + u₀ + (g x + ∑ i, l i • u i) = v + (g x + (u₀ + ∑ i, l i • u i)) := by abel
    rw [e]
    exact this

/-- After `t` steps the density of the bad set has been squared `t` times. -/
theorem exists_bad_iter (B : Finset V) (g : X → V) (t : ℕ) :
    ∃ u : Fin t → V, (bad B g u).card * Fintype.card V ^ (2 ^ t) ≤
      (univ.filter fun v => cnt g B v = 0).card ^ (2 ^ t) * Fintype.card V := by
  induction t with
  | zero => exact ⟨Fin.elim0, by rw [bad_zero]; simp⟩
  | succ t ih =>
    obtain ⟨u, hu⟩ := ih
    obtain ⟨u₀, hu₀⟩ := bad_step B g u
    refine ⟨Fin.cons u₀ u, ?_⟩
    have hc : 0 < Fintype.card V := Fintype.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hc
    calc (bad B g (Fin.cons u₀ u : Fin (t + 1) → V)).card * Fintype.card V ^ 2 ^ (t + 1) *
          Fintype.card V
        = ((bad B g (Fin.cons u₀ u : Fin (t + 1) → V)).card * Fintype.card V) *
          (Fintype.card V ^ 2 ^ t) ^ 2 := by
          rw [pow_succ 2 t, pow_mul]; ring
      _ ≤ (bad B g u).card ^ 2 * (Fintype.card V ^ 2 ^ t) ^ 2 := Nat.mul_le_mul_right _ hu₀
      _ = ((bad B g u).card * Fintype.card V ^ 2 ^ t) ^ 2 := by ring
      _ ≤ ((univ.filter fun v => cnt g B v = 0).card ^ 2 ^ t * Fintype.card V) ^ 2 :=
          Nat.pow_le_pow_left hu 2
      _ = (univ.filter fun v => cnt g B v = 0).card ^ 2 ^ (t + 1) * Fintype.card V *
          Fintype.card V := by
          rw [pow_succ 2 t, pow_mul]; ring

end Squaring

/-! ### Restoring isotropy with ancilla qubits -/

section Ancilla

variable {m t : ℕ}

theorem symp_comm (p q : PL m) : symp p q = symp q p := by
  simp only [symp]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem symp_add_left (p p' q : PL m) : symp (p + p') q = symp p q + symp p' q := by
  simp only [symp, Prod.fst_add, Prod.snd_add, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem symp_add_right (p q q' : PL m) : symp p (q + q') = symp p q + symp p q' := by
  rw [symp_comm, symp_add_left, symp_comm q, symp_comm q']

theorem symp_self (p : PL m) : symp p p = 0 := by
  simp only [symp]
  refine Finset.sum_eq_zero fun j _ => ?_
  linear_combination (p.1 j * p.2 j) * two_eq_zero

theorem symp_smul_left (c : ZMod 2) (p q : PL m) : symp (c • p) q = c * symp p q := by
  simp only [symp, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem symp_smul_right (c : ZMod 2) (p q : PL m) : symp p (c • q) = c * symp p q := by
  rw [symp_comm, symp_smul_left, symp_comm]

theorem symp_zero_left (q : PL m) : symp 0 q = 0 := by
  simp [symp]

theorem symp_sum_left {ι : Type*} (s : Finset ι) (f : ι → PL m) (q : PL m) :
    symp (∑ i ∈ s, f i) q = ∑ i ∈ s, symp (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [symp_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, symp_add_left, ih]

theorem symp_sum_right {ι : Type*} (s : Finset ι) (p : PL m) (f : ι → PL m) :
    symp p (∑ i ∈ s, f i) = ∑ i ∈ s, symp p (f i) := by
  rw [symp_comm, symp_sum_left]
  exact Finset.sum_congr rfl fun i _ => symp_comm _ _

theorem symp_mk (a b c d : Fin t → ZMod 2) :
    symp ((a, b) : PL t) (c, d) = a ⬝ᵥ d + b ⬝ᵥ c := by
  simp [symp, dotProduct, Finset.sum_add_distrib]

theorem symp_app (p p' : PL m) (q q' : PL t) :
    symp (Ball.app p q) (Ball.app p' q') = symp p p' + symp q q' := by
  simp [symp, Ball.app, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem app_add (p p' : PL m) (q q' : PL t) :
    Ball.app (p + p') (q + q') = Ball.app p q + Ball.app p' q' := by
  ext i <;> refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [Ball.app]

theorem wt_le (q : PL t) : wt q ≤ t := by
  unfold wt
  exact (Finset.card_le_univ _).trans (by simp)

/-- The graph of a symmetric matrix is isotropic. -/
theorem symp_gr {A : Matrix (Fin m) (Fin m) (ZMod 2)} (hA : Aᵀ = A) (x y : Fin m → ZMod 2) :
    symp (gr A x) (gr A y) = 0 := by
  have h : x ⬝ᵥ A *ᵥ y = A *ᵥ x ⬝ᵥ y := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hA]
  simp only [gr]
  rw [symp_mk, h]
  linear_combination (A *ᵥ x ⬝ᵥ y) * two_eq_zero

/-- The main (non-ancilla) part of the lifted label. -/
def mainPart (A : Matrix (Fin m) (Fin m) (ZMod 2)) (u : Fin t → PL m)
    (y : (Fin m → ZMod 2) × (Fin t → ZMod 2)) : PL m :=
  gr A y.1 + ∑ i, y.2 i • u i

/-- Symplectic products of a graph vector with the extra generators. -/
def cvec (A : Matrix (Fin m) (Fin m) (ZMod 2)) (u : Fin t → PL m) (x : Fin m → ZMod 2) :
    Fin t → ZMod 2 :=
  fun i => symp (gr A x) (u i)

/-- The Gram matrix of the extra generators. -/
def sigmaMat (u : Fin t → PL m) : Matrix (Fin t) (Fin t) (ZMod 2) :=
  Matrix.of fun i j => symp (u i) (u j)

/-- The strictly lower triangular part of the Gram matrix. -/
def triMat (u : Fin t → PL m) : Matrix (Fin t) (Fin t) (ZMod 2) :=
  Matrix.of fun i j => if j < i then symp (u i) (u j) else 0

theorem sigmaMat_eq (u : Fin t → PL m) : sigmaMat u = triMat u + (triMat u)ᵀ := by
  ext i j
  simp only [sigmaMat, triMat, Matrix.of_apply, Matrix.add_apply, Matrix.transpose_apply]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, not_lt.2 h.le, symp_comm (u j) (u i)]
  · subst h
    simp [symp_self]
  · simp [h, not_lt.2 h.le]

/-- The `Z`-components on the ancilla qubits. -/
def ancZ (A : Matrix (Fin m) (Fin m) (ZMod 2)) (u : Fin t → PL m)
    (y : (Fin m → ZMod 2) × (Fin t → ZMod 2)) : Fin t → ZMod 2 :=
  cvec A u y.1 + triMat u *ᵥ y.2

/-- The lifted label on `m + t` qubits. -/
def Phi (A : Matrix (Fin m) (Fin m) (ZMod 2)) (u : Fin t → PL m)
    (y : (Fin m → ZMod 2) × (Fin t → ZMod 2)) : PL (m + t) :=
  Ball.app (mainPart A u y) (y.2, ancZ A u y)

theorem symp_mainPart {A : Matrix (Fin m) (Fin m) (ZMod 2)} (hA : Aᵀ = A) (u : Fin t → PL m)
    (y y' : (Fin m → ZMod 2) × (Fin t → ZMod 2)) :
    symp (mainPart A u y) (mainPart A u y') =
      cvec A u y.1 ⬝ᵥ y'.2 + y.2 ⬝ᵥ cvec A u y'.1 + y.2 ⬝ᵥ sigmaMat u *ᵥ y'.2 := by
  simp only [mainPart, symp_add_left, symp_add_right, symp_sum_left, symp_sum_right,
    symp_smul_left, symp_smul_right, symp_gr hA, zero_add]
  simp only [dotProduct, cvec, Matrix.mulVec, sigmaMat, Matrix.of_apply, Finset.mul_sum]
  have e1 : ∑ x, y.2 x * symp (u x) (gr A y'.1) = ∑ i, y.2 i * symp (gr A y'.1) (u i) :=
    Finset.sum_congr rfl fun i _ => by rw [symp_comm]
  have e2 : ∑ x, y'.2 x * (symp (gr A y.1) (u x) + ∑ x_1, y.2 x_1 * symp (u x_1) (u x)) =
      ∑ i, symp (gr A y.1) (u i) * y'.2 i +
        ∑ i, ∑ j, y.2 i * (symp (u i) (u j) * y'.2 j) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  ring

/-- The lifted labels are pairwise orthogonal for the symplectic form. -/
theorem symp_Phi {A : Matrix (Fin m) (Fin m) (ZMod 2)} (hA : Aᵀ = A) (u : Fin t → PL m)
    (y y' : (Fin m → ZMod 2) × (Fin t → ZMod 2)) : symp (Phi A u y) (Phi A u y') = 0 := by
  have h : y.2 ⬝ᵥ (triMat u)ᵀ *ᵥ y'.2 = triMat u *ᵥ y.2 ⬝ᵥ y'.2 := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [Phi, Phi, symp_app, symp_mainPart hA, symp_mk, ancZ, ancZ, sigmaMat_eq]
  simp only [Matrix.add_mulVec, dotProduct_add, add_dotProduct]
  rw [h]
  linear_combination (cvec A u y.1 ⬝ᵥ y'.2 + y.2 ⬝ᵥ cvec A u y'.1 + y.2 ⬝ᵥ triMat u *ᵥ y'.2 +
    triMat u *ᵥ y.2 ⬝ᵥ y'.2) * two_eq_zero

theorem mainPart_add (A : Matrix (Fin m) (Fin m) (ZMod 2)) (u : Fin t → PL m)
    (y y' : (Fin m → ZMod 2) × (Fin t → ZMod 2)) :
    mainPart A u (y + y') = mainPart A u y + mainPart A u y' := by
  simp only [mainPart, Prod.fst_add, Prod.snd_add, Pi.add_apply, gr_add, add_smul,
    Finset.sum_add_distrib]
  abel

theorem ancZ_add (A : Matrix (Fin m) (Fin m) (ZMod 2)) (u : Fin t → PL m)
    (y y' : (Fin m → ZMod 2) × (Fin t → ZMod 2)) :
    ancZ A u (y + y') = ancZ A u y + ancZ A u y' := by
  ext i
  simp only [ancZ, cvec, Prod.fst_add, Prod.snd_add, Pi.add_apply, gr_add, symp_add_left,
    Matrix.mulVec_add]
  ring

theorem Phi_add (A : Matrix (Fin m) (Fin m) (ZMod 2)) (u : Fin t → PL m)
    (y y' : (Fin m → ZMod 2) × (Fin t → ZMod 2)) :
    Phi A u (y + y') = Phi A u y + Phi A u y' := by
  rw [Phi, Phi, Phi, ← app_add, mainPart_add, ancZ_add]
  rfl

theorem Phi_eq_zero {A : Matrix (Fin m) (Fin m) (ZMod 2)} {u : Fin t → PL m}
    {y : (Fin m → ZMod 2) × (Fin t → ZMod 2)} (h : Phi A u y = 0) : y = 0 := by
  have h1 := congrArg Prod.fst h
  simp only [Phi, Ball.app, Prod.fst_zero] at h1
  have hl : y.2 = 0 := by
    ext i
    have := congrFun h1 (Fin.natAdd m i)
    simpa [Fin.append_right] using this
  have hx : y.1 = 0 := by
    ext j
    have := congrFun h1 (Fin.castAdd t j)
    simpa [Fin.append_left, mainPart, gr, hl] using this
  exact Prod.ext hx hl

/-- `Phi` as a linear map over `𝔽₂`. -/
def PhiLin (A : Matrix (Fin m) (Fin m) (ZMod 2)) (u : Fin t → PL m) :
    ((Fin m → ZMod 2) × (Fin t → ZMod 2)) →ₗ[ZMod 2] PL (m + t) :=
  (AddMonoidHom.mk' (Phi A u) (Phi_add A u)).toZModLinearMap 2

theorem PhiLin_apply (A : Matrix (Fin m) (Fin m) (ZMod 2)) (u : Fin t → PL m)
    (y : (Fin m → ZMod 2) × (Fin t → ZMod 2)) : PhiLin A u y = Phi A u y := rfl

theorem PhiLin_injective (A : Matrix (Fin m) (Fin m) (ZMod 2)) (u : Fin t → PL m) :
    Function.Injective (PhiLin A u) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  exact Phi_eq_zero hy

end Ancilla

end Cov

/-- **Existence of a Lagrangian subspace with small covering radius.**
If `2 ^ (m (2 ^ t + 2)) < (2 ^ m + ballCard m L) ^ (2 ^ t)` then there is a Lagrangian
subspace of `𝔽₂^(2 (m + t))` every coset of which contains a label of weight at most
`L + t`. -/
theorem exists_lagrangian_covering (m t L : ℕ)
    (h : 2 ^ (m * (2 ^ t + 2)) < (2 ^ m + ballCard m L) ^ (2 ^ t)) :
    ∃ S : Submodule (ZMod 2) (PL (m + t)), IsLagrangian S ∧ CoversWithin S (L + t) := by
  -- the ball of radius `L`
  set B : Finset (PL m) := Finset.univ.filter fun p => wt p ≤ L with hBdef
  have hB : 0 < B.card := Finset.card_pos.2 ⟨0, by simp [hBdef, wt]⟩
  have h' : (2 ^ m) ^ (2 ^ t + 2) < (2 ^ m + B.card) ^ (2 ^ t) := by
    rw [← pow_mul]
    exact h
  -- a symmetric matrix with a small bad set, then `t` squaring steps
  obtain ⟨A, hA, hsmall⟩ := Cov.exists_symm_small B hB
  obtain ⟨u, hu⟩ := Cov.exists_bad_iter B (Cov.gr A) t
  rw [Cov.card_PL] at hu
  have hempty : Cov.bad B (Cov.gr A) u = ∅ := by
    rw [← Finset.card_eq_zero]
    by_contra hne
    have hpos : 1 ≤ (Cov.bad B (Cov.gr A) u).card := Nat.one_le_iff_ne_zero.2 hne
    have h1 : (2 ^ m + B.card) ^ 2 ^ t * ((2 ^ m) ^ 2) ^ 2 ^ t ≤
        (2 ^ m) ^ (2 ^ t + 2) * ((2 ^ m) ^ 2) ^ 2 ^ t := by
      calc (2 ^ m + B.card) ^ 2 ^ t * ((2 ^ m) ^ 2) ^ 2 ^ t
          ≤ (2 ^ m + B.card) ^ 2 ^ t *
              ((Cov.bad B (Cov.gr A) u).card * ((2 ^ m) ^ 2) ^ 2 ^ t) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hpos)
        _ ≤ (2 ^ m + B.card) ^ 2 ^ t *
              ((Finset.univ.filter fun v => Cov.cnt (Cov.gr A) B v = 0).card ^ 2 ^ t *
                (2 ^ m) ^ 2) := Nat.mul_le_mul_left _ hu
        _ = ((Finset.univ.filter fun v => Cov.cnt (Cov.gr A) B v = 0).card *
              (2 ^ m + B.card)) ^ 2 ^ t * (2 ^ m) ^ 2 := by
            rw [mul_pow]; ring
        _ ≤ ((2 ^ m) ^ 3) ^ 2 ^ t * (2 ^ m) ^ 2 :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hsmall _)
        _ = (2 ^ m) ^ (2 ^ t + 2) * ((2 ^ m) ^ 2) ^ 2 ^ t := by ring
    have h2 := Nat.le_of_mul_le_mul_right h1 (by positivity)
    exact absurd h' (not_lt.2 h2)
  have hcov : ∀ v₁ : PL m, ∃ (x : Fin m → ZMod 2) (l : Fin t → ZMod 2),
      wt (v₁ + (Cov.gr A x + ∑ i, l i • u i)) ≤ L := by
    intro v₁
    by_contra hcon
    have hmem : v₁ ∈ Cov.bad B (Cov.gr A) u := by
      rw [Cov.mem_bad]
      intro x l hmem
      exact hcon ⟨x, l, (Finset.mem_filter.1 hmem).2⟩
    rw [hempty] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  -- the lifted subspace
  refine ⟨LinearMap.range (Cov.PhiLin A u), ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩
    exact Cov.symp_Phi hA u y y'
  · rw [Nat.card_congr (LinearEquiv.ofInjective _ (Cov.PhiLin_injective A u)).symm.toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_prod, Cov.card_bits, Cov.card_bits, pow_add]
  · intro v
    obtain ⟨⟨v₁, v₂⟩, rfl⟩ := (Ball.appEquiv m t).surjective v
    obtain ⟨x, l, hw⟩ := hcov v₁
    refine ⟨Cov.PhiLin A u (x, l), LinearMap.mem_range_self _ _, ?_⟩
    show wt (Ball.app v₁ v₂ + Cov.Phi A u (x, l)) ≤ L + t
    rw [Cov.Phi, ← Cov.app_add, Ball.wt_app]
    exact Nat.add_le_add hw (Cov.wt_le _)

end UDA

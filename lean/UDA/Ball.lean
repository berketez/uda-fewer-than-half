import UDA.Defs

/-!
# Counting Pauli labels of bounded weight

The number of Pauli labels of weight at most `L` on `m` qubits is `∑_{j ≤ L} C(m, j) 3^j`.
We also record that the weight is additive under concatenation of labels.
-/

open Finset

namespace UDA

namespace Ball

/-- Concatenation of a Pauli label on `m` qubits with a Pauli label on `t` qubits. -/
def app {m t : ℕ} (p : PL m) (q : PL t) : PL (m + t) :=
  (Fin.append p.1 q.1, Fin.append p.2 q.2)

/-- The weight is additive under concatenation. -/
theorem wt_app {m t : ℕ} (p : PL m) (q : PL t) : wt (app p q) = wt p + wt q := by
  unfold wt app
  rw [Finset.card_filter, Fin.sum_univ_add, Finset.card_filter, Finset.card_filter]
  simp [Fin.append_left, Fin.append_right]

/-- Splitting a label on `m + t` qubits into its first `m` and last `t` qubits. -/
def appEquiv (m t : ℕ) : PL m × PL t ≃ PL (m + t) where
  toFun pq := app pq.1 pq.2
  invFun v := ((fun i => v.1 (Fin.castAdd t i), fun i => v.2 (Fin.castAdd t i)),
    (fun i => v.1 (Fin.natAdd m i), fun i => v.2 (Fin.natAdd m i)))
  left_inv := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    simp [app]
  right_inv := by
    rintro ⟨a, b⟩
    simp [app, Fin.append_castAdd_natAdd]

theorem wt_one (q : PL 1) : wt q = if q = 0 then 0 else 1 := by
  revert q
  decide

theorem sum_PL_one (f : ℕ → ℕ) : ∑ q : PL 1, f (wt q) = f 0 + 3 * f 1 := by
  have h : ∀ q : PL 1, f (wt q) = if q = 0 then f 0 else f 1 := by
    intro q
    rw [wt_one]
    split_ifs <;> rfl
  simp only [h]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  have h0 : (Finset.univ.filter fun q : PL 1 => q = 0).card = 1 := by decide
  have h1 : (Finset.univ.filter fun q : PL 1 => ¬ q = 0).card = 3 := by decide
  rw [h0, h1]
  simp

theorem ballCard_eq_sum (m L : ℕ) : ballCard m L = ∑ p : PL m, if wt p ≤ L then 1 else 0 := by
  unfold ballCard
  rw [Finset.card_filter]

/-- Splitting off the last qubit. -/
theorem ballCard_succ (m L : ℕ) :
    ballCard (m + 1) L = ballCard m L + 3 * ∑ p : PL m, if wt p + 1 ≤ L then 1 else 0 := by
  rw [ballCard_eq_sum, ← Equiv.sum_comp (appEquiv m 1), Fintype.sum_prod_type, Finset.sum_comm]
  have h := sum_PL_one fun k => ∑ p : PL m, if wt p + k ≤ L then 1 else 0
  simp only [appEquiv, Equiv.coe_fn_mk, wt_app]
  rw [h, ballCard_eq_sum]
  simp

theorem ballCard_succ_succ (m L : ℕ) :
    ballCard (m + 1) (L + 1) = ballCard m (L + 1) + 3 * ballCard m L := by
  rw [ballCard_succ, ballCard_eq_sum m L]
  simp

theorem ballCard_succ_zero (m : ℕ) : ballCard (m + 1) 0 = ballCard m 0 := by
  rw [ballCard_succ]
  simp

theorem ballCard_zero (L : ℕ) : ballCard 0 L = 1 := by
  rw [ballCard_eq_sum]
  simp [wt]

theorem ballSum_zero (L : ℕ) : ballSum 0 L = 1 := by
  unfold ballSum
  rw [Finset.sum_range_succ']
  simp

theorem ballSum_succ_zero (m : ℕ) : ballSum (m + 1) 0 = ballSum m 0 := by
  simp [ballSum]

theorem ballSum_succ_succ (m L : ℕ) :
    ballSum (m + 1) (L + 1) = ballSum m (L + 1) + 3 * ballSum m L := by
  unfold ballSum
  rw [Finset.sum_range_succ' _ (L + 1), Finset.sum_range_succ' _ (L + 1)]
  simp only [Nat.choose_succ_succ, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [Nat.choose_zero_right, pow_zero, mul_one]
  have : ∀ j : ℕ, m.choose j * 3 ^ (j + 1) = 3 * (m.choose j * 3 ^ j) := by
    intro j; ring
  simp only [this]
  ring

end Ball

/-- The number of Pauli labels of weight at most `L` on `m` qubits is
`∑_{j ≤ L} C(m, j) 3^j`. -/
theorem ballCard_eq_ballSum (m L : ℕ) : ballCard m L = ballSum m L := by
  induction m generalizing L with
  | zero => rw [Ball.ballCard_zero, Ball.ballSum_zero]
  | succ m ih =>
    cases L with
    | zero => rw [Ball.ballCard_succ_zero, Ball.ballSum_succ_zero, ih]
    | succ L => rw [Ball.ballCard_succ_succ, Ball.ballSum_succ_succ, ih, ih]

end UDA

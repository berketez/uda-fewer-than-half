import UDA.Defs

/-!
# Explicit thresholds

`UDA.half_params`: for every `n ≥ 139` there are `m, t, L` with `m + t = n`,
`2 (L + t) + 1 ≤ ⌈n/2⌉ - 1` (written `(n + 1) / 2 - 1` in `ℕ`) and the covering condition
`2 ^ (m (2^t + 2)) < (2^m + ballSum m L) ^ (2^t)` of `UDA.exists_lagrangian_covering`.

* `139 ≤ n ≤ 268`: explicit parameters from `table`, checked by the kernel (`decide +kernel`).
* `n ≥ 269`: the uniform choice `t = log₂ n + 1`, `m = n - t`, `L = ⌊m/5⌋`, proved from
  the binomial estimate `C(5k, k) 3^k ≥ 2^(5k+6)` for `k ≥ 52` (base case by the kernel,
  induction step from an exact ratio identity and a polynomial inequality).

The value `139` is sharp for this construction: the condition fails at `n = 138`.
-/

namespace UDA
namespace Thr

/-- `m.choose j` through descending factorials (kernel-friendly). -/
def binomFast (m j : ℕ) : ℕ := m.descFactorial j / j.factorial

theorem binomFast_eq (m j : ℕ) : binomFast m j = m.choose j :=
  (Nat.choose_eq_descFactorial_div_factorial m j).symm

/-- Kernel-friendly evaluation of `ballSum`. -/
def ballFast (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | L + 1 => ballFast m L + binomFast m (L + 1) * 3 ^ (L + 1)

theorem ballFast_eq (m L : ℕ) : ballFast m L = ballSum m L := by
  induction L with
  | zero => simp [ballFast, ballSum]
  | succ L ih =>
    rw [ballFast, ih, binomFast_eq, ballSum, ballSum, Finset.sum_range_succ _ (L + 1)]

/-- Parameters `(t, L)` for `n = 139 + i`, `i = 0, …, 129`. -/
def table : List (ℕ × ℕ) := [
    (5, 29), (5, 29), (6, 28), (6, 28), (5, 30), (5, 30), (5, 30), (6, 29),
    (5, 31), (5, 31), (5, 31), (5, 31), (5, 32), (5, 32), (5, 32), (5, 32),
    (5, 33), (5, 33), (5, 33), (5, 33), (5, 34), (5, 34), (5, 34), (5, 34),
    (5, 35), (5, 35), (5, 35), (5, 35), (5, 36), (5, 36), (5, 36), (5, 36),
    (5, 37), (5, 37), (5, 37), (5, 37), (5, 38), (5, 38), (5, 38), (5, 38),
    (5, 39), (5, 39), (5, 39), (5, 39), (5, 40), (5, 40), (5, 40), (5, 40),
    (5, 41), (5, 41), (5, 41), (5, 41), (5, 42), (5, 42), (5, 42), (5, 42),
    (5, 43), (5, 43), (5, 43), (5, 43), (4, 45), (5, 44), (5, 44), (5, 44),
    (4, 46), (5, 45), (5, 45), (5, 45), (4, 47), (4, 47), (5, 46), (5, 46),
    (4, 48), (4, 48), (5, 47), (5, 47), (4, 49), (4, 49), (5, 48), (5, 48),
    (4, 50), (4, 50), (4, 50), (5, 49), (4, 51), (4, 51), (4, 51), (5, 50),
    (4, 52), (4, 52), (4, 52), (4, 52), (4, 53), (4, 53), (4, 53), (4, 53),
    (4, 54), (4, 54), (4, 54), (4, 54), (4, 55), (4, 55), (4, 55), (4, 55),
    (4, 56), (4, 56), (4, 56), (4, 56), (4, 57), (4, 57), (4, 57), (4, 57),
    (4, 58), (4, 58), (4, 58), (4, 58), (4, 59), (4, 59), (4, 59), (4, 59),
    (4, 60), (4, 60), (4, 60), (4, 60), (4, 61), (4, 61), (4, 61), (4, 61),
    (4, 62), (4, 62)]

/-- Kernel check of one row of the table. -/
def rowOK (n : ℕ) (tl : ℕ × ℕ) : Bool :=
  decide (tl.1 ≤ n) && decide (2 * (tl.2 + tl.1) + 1 ≤ (n + 1) / 2 - 1) &&
    decide (2 ^ ((n - tl.1) * (2 ^ tl.1 + 2)) <
      (2 ^ (n - tl.1) + ballFast (n - tl.1) tl.2) ^ (2 ^ tl.1))

theorem table_ok :
    ((List.range 130).all fun i => rowOK (139 + i) (table.getD i (0, 0))) = true := by
  decide +kernel

theorem table_params (n : ℕ) (h1 : 139 ≤ n) (h2 : n ≤ 268) :
    ∃ m t L : ℕ, m + t = n ∧ 2 * (L + t) + 1 ≤ (n + 1) / 2 - 1 ∧
      2 ^ (m * (2 ^ t + 2)) < (2 ^ m + ballSum m L) ^ (2 ^ t) := by
  have hall := table_ok
  rw [List.all_eq_true] at hall
  have hi := hall (n - 139) (List.mem_range.2 (by omega))
  have hn : 139 + (n - 139) = n := by omega
  rw [hn] at hi
  generalize table.getD (n - 139) (0, 0) = tl at hi
  obtain ⟨t, L⟩ := tl
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hi
  obtain ⟨⟨htn, hK⟩, hc⟩ := hi
  exact ⟨n - t, t, L, by omega, hK, by rwa [← ballFast_eq]⟩

/-- `16 (s + 1) + 20 ≤ 2 ^ s` for `s ≥ 8`. -/
theorem lin_le_pow (s : ℕ) (hs : 8 ≤ s) : 16 * (s + 1) + 20 ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s _ ih => rw [pow_succ]; omega

/-- Exact ratio identity for `C(5k, k)`. -/
theorem choose_step (k : ℕ) :
    Nat.choose (5 * k + 5) (k + 1) *
        ((k + 1) * (4 * k + 1) * (4 * k + 2) * (4 * k + 3) * (4 * k + 4)) =
      Nat.choose (5 * k) k *
        ((5 * k + 1) * (5 * k + 2) * (5 * k + 3) * (5 * k + 4) * (5 * k + 5)) := by
  have h1 : (5 * k + 1) * Nat.choose (5 * k) k = Nat.choose (5 * k + 1) (k + 1) * (k + 1) :=
    Nat.add_one_mul_choose_eq (5 * k) k
  have h2 : Nat.choose (5 * k + 1) (k + 1) * (5 * k + 2) =
      Nat.choose (5 * k + 2) (k + 1) * (4 * k + 1) := by
    have := Nat.choose_mul_succ_eq (5 * k + 1) (k + 1)
    rwa [show 5 * k + 1 + 1 - (k + 1) = 4 * k + 1 by omega] at this
  have h3 : Nat.choose (5 * k + 2) (k + 1) * (5 * k + 3) =
      Nat.choose (5 * k + 3) (k + 1) * (4 * k + 2) := by
    have := Nat.choose_mul_succ_eq (5 * k + 2) (k + 1)
    rwa [show 5 * k + 2 + 1 - (k + 1) = 4 * k + 2 by omega] at this
  have h4 : Nat.choose (5 * k + 3) (k + 1) * (5 * k + 4) =
      Nat.choose (5 * k + 4) (k + 1) * (4 * k + 3) := by
    have := Nat.choose_mul_succ_eq (5 * k + 3) (k + 1)
    rwa [show 5 * k + 3 + 1 - (k + 1) = 4 * k + 3 by omega] at this
  have h5 : Nat.choose (5 * k + 4) (k + 1) * (5 * k + 5) =
      Nat.choose (5 * k + 5) (k + 1) * (4 * k + 4) := by
    have := Nat.choose_mul_succ_eq (5 * k + 4) (k + 1)
    rwa [show 5 * k + 4 + 1 - (k + 1) = 4 * k + 4 by omega] at this
  zify at h1 h2 h3 h4 h5 ⊢
  linear_combination
    (-(5 * (k : ℤ) + 2) * (5 * k + 3) * (5 * k + 4) * (5 * k + 5)) * h1
    - ((k : ℤ) + 1) * (5 * k + 3) * (5 * k + 4) * (5 * k + 5) * h2
    - ((k : ℤ) + 1) * (4 * k + 1) * (5 * k + 4) * (5 * k + 5) * h3
    - ((k : ℤ) + 1) * (4 * k + 1) * (4 * k + 2) * (5 * k + 5) * h4
    - ((k : ℤ) + 1) * (4 * k + 1) * (4 * k + 2) * (4 * k + 3) * h5

/-- The ratio estimate `32 C(5k, k) 3^k ≤ C(5k + 5, k + 1) 3^(k+1)` for `k ≥ 4`. -/
theorem ratio (k : ℕ) (hk : 4 ≤ k) :
    32 * (Nat.choose (5 * k) k * 3 ^ k) ≤ Nat.choose (5 * k + 5) (k + 1) * 3 ^ (k + 1) := by
  have hs := choose_step k
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
  set a := Nat.choose (5 * (j + 4)) (j + 4)
  set b := Nat.choose (5 * (j + 4) + 5) (j + 4 + 1)
  set Q := (j + 4 + 1) * (4 * (j + 4) + 1) * (4 * (j + 4) + 2) * (4 * (j + 4) + 3) *
    (4 * (j + 4) + 4) with hQ
  set P := (5 * (j + 4) + 1) * (5 * (j + 4) + 2) * (5 * (j + 4) + 3) * (5 * (j + 4) + 4) *
    (5 * (j + 4) + 5) with hP
  have hpoly : 3 * P = 32 * Q +
      (1183 * j ^ 5 + 23113 * j ^ 4 + 174003 * j ^ 3 + 618863 * j ^ 2 + 998390 * j + 522000) := by
    rw [hP, hQ]; ring
  have hQpos : 0 < Q := by positivity
  have key : 32 * a * Q ≤ 3 * b * Q := by
    calc 32 * a * Q = a * (32 * Q) := by ring
      _ ≤ a * (3 * P) := by rw [hpoly]; exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      _ = 3 * (b * Q) := by rw [hs]; ring
      _ = 3 * b * Q := by ring
  have h32 : 32 * a ≤ 3 * b := Nat.le_of_mul_le_mul_right key hQpos
  calc 32 * (a * 3 ^ (j + 4)) = (32 * a) * 3 ^ (j + 4) := by ring
    _ ≤ (3 * b) * 3 ^ (j + 4) := Nat.mul_le_mul_right _ h32
    _ = b * 3 ^ (j + 4 + 1) := by ring

/-- Kernel check of the base case `2 ^ 266 ≤ C(260, 52) 3^52`. -/
def baseCheck : Bool := decide (2 ^ (5 * 52 + 6) ≤ binomFast (5 * 52) 52 * 3 ^ 52)

theorem baseCheck_eq : baseCheck = true := by decide +kernel

theorem base_bound : 2 ^ (5 * 52 + 6) ≤ Nat.choose (5 * 52) 52 * 3 ^ 52 := by
  have h := of_decide_eq_true baseCheck_eq
  rwa [binomFast_eq] at h

/-- `2 ^ (5k + 6) ≤ C(5k, k) 3^k` for `k ≥ 52`. -/
theorem choose_bound (k : ℕ) (hk : 52 ≤ k) : 2 ^ (5 * k + 6) ≤ Nat.choose (5 * k) k * 3 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => exact base_bound
  | succ k hk ih =>
    have hr := ratio k (by omega)
    have e : 5 * (k + 1) = 5 * k + 5 := by ring
    rw [e]
    calc 2 ^ (5 * k + 5 + 6) = 32 * 2 ^ (5 * k + 6) := by ring
      _ ≤ 32 * (Nat.choose (5 * k) k * 3 ^ k) := Nat.mul_le_mul_left _ ih
      _ ≤ _ := hr

/-- For `m ≥ 260`: `2 ^ (m + 2) ≤ ballSum m ⌊m/5⌋`. -/
theorem ball_bound (m : ℕ) (hm : 260 ≤ m) : 2 ^ (m + 2) ≤ ballSum m (m / 5) := by
  have hk : 52 ≤ m / 5 := by omega
  have h1 := choose_bound (m / 5) hk
  have h2 : Nat.choose (5 * (m / 5)) (m / 5) ≤ Nat.choose m (m / 5) :=
    Nat.choose_le_choose _ (by omega)
  have h3 : 2 ^ (m + 2) ≤ 2 ^ (5 * (m / 5) + 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : Nat.choose m (m / 5) * 3 ^ (m / 5) ≤ ballSum m (m / 5) := by
    unfold ballSum
    exact Finset.single_le_sum (f := fun j => m.choose j * 3 ^ j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_self _))
  calc 2 ^ (m + 2) ≤ 2 ^ (5 * (m / 5) + 6) := h3
    _ ≤ Nat.choose (5 * (m / 5)) (m / 5) * 3 ^ (m / 5) := h1
    _ ≤ Nat.choose m (m / 5) * 3 ^ (m / 5) := Nat.mul_le_mul_right _ h2
    _ ≤ _ := h4

/-- If `m < 2^t` and `2^(m+2) ≤ B`, then `2^(m(2^t+2)) < (2^m + B)^(2^t)`. -/
theorem cond_of_ball {m t B : ℕ} (hmt : m < 2 ^ t) (hB : 2 ^ (m + 2) ≤ B) :
    2 ^ (m * (2 ^ t + 2)) < (2 ^ m + B) ^ (2 ^ t) := by
  have h1 : 2 ^ (m * (2 ^ t + 2)) < 2 ^ ((m + 2) * 2 ^ t) :=
    Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
  have h2 : 2 ^ ((m + 2) * 2 ^ t) = (2 ^ (m + 2)) ^ (2 ^ t) := by rw [pow_mul]
  have h3 : (2 ^ (m + 2)) ^ (2 ^ t) ≤ (2 ^ m + B) ^ (2 ^ t) :=
    Nat.pow_le_pow_left (le_trans hB (Nat.le_add_left _ _)) _
  calc 2 ^ (m * (2 ^ t + 2)) < 2 ^ ((m + 2) * 2 ^ t) := h1
    _ = (2 ^ (m + 2)) ^ (2 ^ t) := h2
    _ ≤ _ := h3

theorem tail_params (n : ℕ) (hn : 269 ≤ n) :
    ∃ m t L : ℕ, m + t = n ∧ 2 * (L + t) + 1 ≤ (n + 1) / 2 - 1 ∧
      2 ^ (m * (2 ^ t + 2)) < (2 ^ m + ballSum m L) ^ (2 ^ t) := by
  have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hle : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h8 : 8 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hlin := lin_le_pow (Nat.log 2 n) h8
  have hm : 260 ≤ n - (Nat.log 2 n + 1) := by
    rcases lt_or_ge n 512 with h | h
    · have : Nat.log 2 n < 9 := Nat.log_lt_of_lt_pow (by omega) (by norm_num; omega)
      omega
    · omega
  refine ⟨n - (Nat.log 2 n + 1), Nat.log 2 n + 1, (n - (Nat.log 2 n + 1)) / 5,
    by omega, by omega, ?_⟩
  exact cond_of_ball (by omega) (ball_bound _ hm)

end Thr

/-- **Explicit parameters for the half threshold.** For every `n ≥ 139` there are `m, t, L`
with `m + t = n`, `2 (L + t) + 1 ≤ ⌈n/2⌉ - 1`, and the covering condition. -/
theorem half_params (n : ℕ) (hn : 139 ≤ n) :
    ∃ m t L : ℕ, m + t = n ∧ 2 * (L + t) + 1 ≤ (n + 1) / 2 - 1 ∧
      2 ^ (m * (2 ^ t + 2)) < (2 ^ m + ballSum m L) ^ (2 ^ t) := by
  rcases le_or_gt n 268 with h | h
  · exact Thr.table_params n hn h
  · exact Thr.tail_params n (by omega)

end UDA

import UDA.Thresholds

/-!
# Explicit parameters for the order `⌈2n/5⌉`, `996 ≤ n ≤ 1330`

For the order `K = ⌈2n/5⌉ = (2n + 4)/5` we use `t` extra qubits, `m = n - t` and the level
`L = ⌊(K - 1)/2⌋ - t`, so that `2 (L + t) + 1 ≤ K`. For every `n` with `996 ≤ n ≤ 1330` one of
the following is checked by the kernel (`decide +kernel`), with `B = C(m, L) 3^L` the top term
of the Hamming ball (`B ≤ ballSum m L`):
* `t = 10` or `t = 11`: `m < 2^t` and `2^(m+2) ≤ B` (then `UDA.Thr.cond_of_ball` applies);
* `t = 9`: the covering condition `2^(m (2^t + 2)) < (2^m + B)^(2^t)` itself.

`n ≥ 1331` is handled analytically in `UDA/Thm1Rest.lean`.
-/

namespace UDA
namespace T1

open Thr

/-- The top term `C(m, L) 3^L` is at most `ballSum m L`. -/
theorem choose_mul_le_ballSum (m L : ℕ) : m.choose L * 3 ^ L ≤ ballSum m L := by
  unfold ballSum
  exact Finset.single_le_sum (f := fun j => m.choose j * 3 ^ j) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 (Nat.lt_succ_self _))

/-- The level used for the order `(2n + 4)/5` with `t` extra qubits. -/
def level (n t : ℕ) : ℕ := ((2 * n + 4) / 5 - 1) / 2 - t

/-- The top term `C(m, L) 3^L` of the Hamming ball, through `binomFast` (kernel-friendly). -/
def topTerm (m L : ℕ) : ℕ := binomFast m L * 3 ^ L

/-- `topTerm m L ≤ ballSum m L`. -/
theorem topTerm_le_ballSum (m L : ℕ) : topTerm m L ≤ ballSum m L := by
  rw [topTerm, binomFast_eq]
  exact choose_mul_le_ballSum m L

/-- Sufficient check: `m < 2^t` and `2^(m+2) ≤ C(m, L) 3^L`. -/
def suffOK (n t : ℕ) : Bool :=
  decide (t + 1 ≤ n) && decide (t ≤ ((2 * n + 4) / 5 - 1) / 2) && decide (n - t < 2 ^ t) &&
    decide (2 ^ (n - t + 2) ≤ topTerm (n - t) (level n t))

/-- Exact covering check with the top term of the ball. -/
def exactOK (n t : ℕ) : Bool :=
  decide (t + 1 ≤ n) && decide (t ≤ ((2 * n + 4) / 5 - 1) / 2) &&
    decide (2 ^ ((n - t) * (2 ^ t + 2)) <
      (2 ^ (n - t) + topTerm (n - t) (level n t)) ^ (2 ^ t))

/-- The check of one value of `n`. -/
def rowOK (n : ℕ) : Bool := suffOK n 10 || suffOK n 11 || exactOK n 9

/-- Kernel check of all `n` with `996 ≤ n ≤ 1330`. -/
theorem table_ok : ((List.range 335).all fun i => rowOK (996 + i)) = true := by
  decide +kernel

/-- The parameters of one passing check. -/
theorem params_of_rowOK {n : ℕ} (h : rowOK n = true) :
    ∃ m t L : ℕ, m + t = n ∧ 2 * (L + t) + 1 ≤ (2 * n + 4) / 5 ∧
      2 ^ (m * (2 ^ t + 2)) < (2 ^ m + ballSum m L) ^ (2 ^ t) := by
  have hsuff : ∀ t, suffOK n t = true → ∃ m t L : ℕ, m + t = n ∧
      2 * (L + t) + 1 ≤ (2 * n + 4) / 5 ∧
      2 ^ (m * (2 ^ t + 2)) < (2 ^ m + ballSum m L) ^ (2 ^ t) := by
    intro t ht
    simp only [suffOK, Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := ht
    refine ⟨n - t, t, level n t, by omega, by unfold level; omega, ?_⟩
    exact cond_of_ball h3 (h4.trans (topTerm_le_ballSum _ _))
  simp only [rowOK, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact hsuff 10 h
  · exact hsuff 11 h
  · simp only [exactOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨n - 9, 9, level n 9, by omega, by unfold level; omega, ?_⟩
    refine lt_of_lt_of_le h3 (Nat.pow_le_pow_left ?_ _)
    exact Nat.add_le_add_left (topTerm_le_ballSum _ _) _

/-- **Explicit parameters for `⌈2n/5⌉`, `996 ≤ n ≤ 1330`.** -/
theorem table_params (n : ℕ) (h1 : 996 ≤ n) (h2 : n ≤ 1330) :
    ∃ m t L : ℕ, m + t = n ∧ 2 * (L + t) + 1 ≤ (2 * n + 4) / 5 ∧
      2 ^ (m * (2 ^ t + 2)) < (2 ^ m + ballSum m L) ^ (2 ^ t) := by
  have hall := table_ok
  rw [List.all_eq_true] at hall
  have hi := hall (n - 996) (List.mem_range.2 (by omega))
  rw [show 996 + (n - 996) = n by omega] at hi
  exact params_of_rowOK hi

end T1
end UDA

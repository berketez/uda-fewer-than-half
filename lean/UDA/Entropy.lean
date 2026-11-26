import UDA.Defs

/-!
# An entropy lower bound for one term of the Hamming ball

For `0 < L` with `4 L ≤ m`, a real `κ ∈ (0, 1)` with `qaryEntropy 4 κ = log 2` (the constant
`κ_c`), and `3 (L - κ m) ≥ ℓ + 3` where `m + 1 ≤ 2^(ℓ+1)`, we prove

  `2 ^ (m + 2) ≤ C(m, L) 3^L`     (`UDA.Ent.two_pow_le_choose_mul`).

Two ingredients:
* `UDA.Ent.pow_le_mode` (pure `ℕ`): `m^m ≤ (m + 1) C(m, k) k^k (m - k)^(m - k)` for `k < m`.
  The terms `C(m, j) k^j (m - k)^(m - j)` of the binomial expansion of `(k + (m - k))^m` are
  largest at `j = k` (the mode of the binomial distribution with parameter `k/m`).
* Gibbs' inequality `κ log (y/κ) + (1 - κ) log ((1 - y)/(1 - κ)) ≤ 0` (from `log x ≤ x - 1`),
  applied with `y = L/m`; together with `qaryEntropy 4 κ = log 2` it gives
  `log (m^m 3^L / (L^L (m - L)^(m - L))) ≥ m log 2 + (L - κ m) log (3 (m - L) / L)`.
-/

namespace UDA
namespace Ent

/-! ## The mode of the binomial expansion -/

/-- The `j`-th term of the binomial expansion of `(k + (m - k)) ^ m`. -/
def bterm (m k j : ℕ) : ℕ := k ^ j * (m - k) ^ (m - j) * m.choose j

/-- Ratio of consecutive terms: `t_{j+1} (j + 1)(m - k) = t_j (m - j) k`. -/
theorem bterm_succ (m k j : ℕ) (hj : j < m) :
    bterm m k (j + 1) * ((j + 1) * (m - k)) = bterm m k j * ((m - j) * k) := by
  unfold bterm
  have h1 := Nat.choose_succ_right_eq m j
  obtain ⟨r, hr⟩ : ∃ r, m - j = r + 1 := ⟨m - j - 1, by omega⟩
  have hr' : m - (j + 1) = r := by omega
  rw [hr'] at *
  rw [hr] at h1 ⊢
  calc k ^ (j + 1) * (m - k) ^ r * m.choose (j + 1) * ((j + 1) * (m - k))
      = k ^ j * k * (m - k) ^ r * (m - k) * (m.choose (j + 1) * (j + 1)) := by ring
    _ = k ^ j * (m - k) ^ (r + 1) * m.choose j * ((r + 1) * k) := by rw [h1]; ring

/-- The terms increase up to `j = k`. -/
theorem bterm_le_succ (m k j : ℕ) (hk : k < m) (hjk : j < k) :
    bterm m k j ≤ bterm m k (j + 1) := by
  have hs := bterm_succ m k j (by omega)
  have hpos : 0 < (j + 1) * (m - k) := Nat.mul_pos (Nat.succ_pos j) (by omega)
  have hineq : (j + 1) * (m - k) ≤ (m - j) * k := by
    have e1 : m - j = (m - k) + (k - j) := by omega
    rw [e1]
    calc (j + 1) * (m - k) ≤ k * (m - k) := Nat.mul_le_mul_right _ hjk
      _ ≤ (m - k) * k + (k - j) * k := by rw [mul_comm]; exact Nat.le_add_right _ _
      _ = ((m - k) + (k - j)) * k := by ring
  have h2 := Nat.mul_le_mul_left (bterm m k j) hineq
  rw [← hs] at h2
  exact Nat.le_of_mul_le_mul_right h2 hpos

/-- The terms decrease from `j = k` on. -/
theorem bterm_succ_le (m k j : ℕ) (hk : k < m) (hkj : k ≤ j) (hjm : j < m) :
    bterm m k (j + 1) ≤ bterm m k j := by
  have hs := bterm_succ m k j hjm
  have hpos : 0 < (j + 1) * (m - k) := Nat.mul_pos (Nat.succ_pos j) (by omega)
  have hineq : (m - j) * k ≤ (j + 1) * (m - k) := by
    calc (m - j) * k ≤ (m - k) * k := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (m - k) * (j + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = (j + 1) * (m - k) := mul_comm _ _
  have h2 := Nat.mul_le_mul_left (bterm m k j) hineq
  rw [← hs] at h2
  exact Nat.le_of_mul_le_mul_right h2 hpos

/-- The term `j = k` is the largest one. -/
theorem bterm_le_mode (m k j : ℕ) (hk : k < m) (hj : j ≤ m) : bterm m k j ≤ bterm m k k := by
  rcases le_or_gt j k with h | h
  · -- going up from `j` to `k`
    have key : ∀ d i, i + d = k → bterm m k i ≤ bterm m k k := by
      intro d
      induction d with
      | zero => intro i hi; rw [← hi]; rfl
      | succ d ih =>
        intro i hi
        exact le_trans (bterm_le_succ m k i hk (by omega)) (ih (i + 1) (by omega))
    exact key (k - j) j (by omega)
  · -- going down from `j` to `k`
    have key : ∀ i, k ≤ i → i ≤ m → bterm m k i ≤ bterm m k k := by
      intro i hki
      induction i, hki using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ i hki ih =>
        intro him
        exact le_trans (bterm_succ_le m k i hk hki (by omega)) (ih (by omega))
    exact key j h.le hj

/-- **Mode bound.** `m^m ≤ (m + 1) C(m, k) k^k (m - k)^(m - k)` for `k < m`. -/
theorem pow_le_mode (m k : ℕ) (hk : k < m) :
    m ^ m ≤ (m + 1) * (m.choose k * k ^ k * (m - k) ^ (m - k)) := by
  have h := add_pow k (m - k) m
  rw [Nat.add_sub_cancel' hk.le] at h
  rw [h]
  calc ∑ j ∈ Finset.range (m + 1), k ^ j * (m - k) ^ (m - j) * m.choose j
      = ∑ j ∈ Finset.range (m + 1), bterm m k j := rfl
    _ ≤ ∑ _j ∈ Finset.range (m + 1), bterm m k k :=
        Finset.sum_le_sum fun j hj => bterm_le_mode m k j hk (by simp at hj; omega)
    _ = (m + 1) * (m.choose k * k ^ k * (m - k) ^ (m - k)) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, bterm]; ring

/-! ## Gibbs' inequality and the lower bound -/

open Real

/-- Gibbs' inequality `κ log (Λ / (κ M)) + (1 - κ) log (D / ((1 - κ) M)) ≤ 0` for
`Λ + D = M`, multiplied out. -/
theorem gibbs {κ Λ D M : ℝ} (h0 : 0 < κ) (h1 : κ < 1) (hΛ : 0 < Λ) (hD : 0 < D)
    (hM : Λ + D = M) :
    κ * M * log Λ + (1 - κ) * M * log D - M * log M ≤
      M * (κ * log κ + (1 - κ) * log (1 - κ)) := by
  have hMpos : 0 < M := by linarith
  have hκM : 0 < κ * M := mul_pos h0 hMpos
  have h1κ : 0 < 1 - κ := by linarith
  have h1κM : 0 < (1 - κ) * M := mul_pos h1κ hMpos
  have g1 := log_le_sub_one_of_pos (div_pos hΛ hκM)
  have g2 := log_le_sub_one_of_pos (div_pos hD h1κM)
  rw [log_div hΛ.ne' hκM.ne', log_mul h0.ne' hMpos.ne'] at g1
  rw [log_div hD.ne' h1κM.ne', log_mul h1κ.ne' hMpos.ne'] at g2
  have e1 : κ * M * (Λ / (κ * M) - 1) = Λ - κ * M := by field_simp
  have e2 : (1 - κ) * M * (D / ((1 - κ) * M) - 1) = D - (1 - κ) * M := by field_simp
  have m1 := mul_le_mul_of_nonneg_left g1 hκM.le
  have m2 := mul_le_mul_of_nonneg_left g2 h1κM.le
  rw [e1] at m1
  rw [e2] at m2
  linarith

/-- `qaryEntropy 4 κ = log 2` written out. -/
theorem qary4_expand (κ : ℝ) :
    qaryEntropy 4 κ = κ * log 3 - κ * log κ - (1 - κ) * log (1 - κ) := by
  unfold qaryEntropy binEntropy
  rw [log_inv, log_inv]
  norm_num
  ring

/-- **Entropy lower bound for one term of the Hamming ball.** If `qaryEntropy 4 κ = log 2`,
`0 < L`, `4 L ≤ m`, `m + 1 ≤ 2^(ℓ+1)` and `ℓ + 3 ≤ 3 (L - κ m)`, then
`2^(m+2) ≤ C(m, L) 3^L`. -/
theorem two_pow_le_choose_mul {κ : ℝ} (h0 : 0 < κ) (h1 : κ < 1)
    (hH : qaryEntropy 4 κ = log 2) {m L ℓ : ℕ} (hL : 0 < L) (hLm : 4 * L ≤ m)
    (hm : m + 1 ≤ 2 ^ (ℓ + 1)) (hgap : (ℓ : ℝ) + 3 ≤ 3 * ((L : ℝ) - κ * m)) :
    2 ^ (m + 2) ≤ m.choose L * 3 ^ L := by
  have hLlt : L < m := by omega
  have hH' := hH
  rw [qary4_expand] at hH'
  have hΛpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hLltR : (L : ℝ) < m := by exact_mod_cast hLlt
  have hD : ((m - L : ℕ) : ℝ) = (m : ℝ) - L := by rw [Nat.cast_sub hLlt.le]
  have hDpos : (0 : ℝ) < (m : ℝ) - L := by linarith
  have hMpos : (0 : ℝ) < m := by linarith
  have hC : (0 : ℝ) < (m.choose L : ℝ) := by exact_mod_cast Nat.choose_pos hLlt.le
  have h2pos : (0 : ℝ) < log 2 := log_pos (by norm_num)
  -- the mode bound, in `ℝ`, and its logarithm
  have hmode : ((m : ℝ)) ^ m ≤
      ((m : ℝ) + 1) * ((m.choose L : ℝ) * (L : ℝ) ^ L * ((m : ℝ) - L) ^ (m - L)) := by
    have := pow_le_mode m L hLlt
    rw [← hD]
    exact_mod_cast this
  have hlog := log_le_log (by positivity) hmode
  rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_pow, log_pow, log_pow, hD] at hlog
  -- Gibbs at `κ`
  have hG := gibbs h0 h1 hΛpos hDpos (by ring : (L : ℝ) + ((m : ℝ) - L) = m)
  have hHM : (m : ℝ) * (κ * log 3 - κ * log κ - (1 - κ) * log (1 - κ)) = m * log 2 := by
    rw [hH']
  -- the slope term
  have hratio : 3 * log 2 ≤ log 3 - log (L : ℝ) + log ((m : ℝ) - L) := by
    have h8 : (8 : ℝ) * L ≤ 3 * ((m : ℝ) - L) := by
      have : (4 : ℝ) * L ≤ m := by exact_mod_cast hLm
      linarith
    have hl := log_le_log (by positivity) h8
    rw [log_mul (by norm_num) hΛpos.ne', log_mul (by norm_num) hDpos.ne',
      show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow] at hl
    push_cast at hl
    linarith
  have hgap0 : 0 ≤ (L : ℝ) - κ * m := by
    have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    linarith
  have hP := mul_le_mul_of_nonneg_left hratio hgap0
  have hQ := mul_le_mul_of_nonneg_right hgap h2pos.le
  have hR : log ((m : ℝ) + 1) ≤ ((ℓ : ℝ) + 1) * log 2 := by
    have hc : (m : ℝ) + 1 ≤ (2 : ℝ) ^ (ℓ + 1) := by exact_mod_cast hm
    have := log_le_log (by positivity) hc
    rw [log_pow] at this
    push_cast at this
    exact this
  -- conclusion
  have hfin : log ((2 : ℝ) ^ (m + 2)) ≤ log ((m.choose L : ℝ) * 3 ^ L) := by
    rw [log_pow, log_mul hC.ne' (by positivity), log_pow]
    push_cast
    nlinarith [hlog, hG, hHM, hP, hQ, hR]
  have hfin' := (log_le_log_iff (by positivity) (by positivity)).1 hfin
  exact_mod_cast hfin'

end Ent
end UDA

import UDA.Statement2
import UDA.Entropy

/-!
# The constant `κ_c`

`UDA.Kap.kappaC_spec : UDA.KappaCStatement`: the equation `qaryEntropy 4 κ = log 2` has exactly
one root `κ_c` in `(0, 1/2)`, and `0.1892896 < κ_c < 0.1892897`.

* Uniqueness: `qaryEntropy 4` is strictly increasing on `[0, 3/4]` (Mathlib).
* Existence: intermediate value theorem on `[0.1892896, 0.1892897]`.
* Bounds: rigorous evaluation of `qaryEntropy 4` at both rationals. Writing
  `x = (3/16)(1 + u)` and `1 - x = (4/5)(1 + w)` with small `u, w`,
  `qaryEntropy 4 x - log 2 = (6x - 3) log 2 + (1 - x) log 5 - x log (1 + u) - (1 - x) log (1 + w)`;
  `log 2`, `log 5` come from Mathlib's ten-digit bounds and `log (1 + u)`, `log (1 + w)` from
  four terms of the Taylor series (`Real.abs_log_sub_add_sum_range_le`).
  The values are about `-6.4 · 10⁻⁸` and `+1.9 · 10⁻⁷`; the error of the bounds is below
  `2 · 10⁻⁹`.
-/

open Real Set

namespace UDA
namespace Kap

/-- `qaryEntropy 4 x - log 2` rewritten around the reference points `3/16` and `4/5`. -/
theorem qary4_sub_log_two {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    qaryEntropy 4 x - log 2 =
      (6 * x - 3) * log 2 + (1 - x) * log 5 - x * log (16 * x / 3)
        - (1 - x) * log (5 * (1 - x) / 4) := by
  have hx1 : 0 < 1 - x := by linarith
  rw [Ent.qary4_expand]
  rw [log_div (by positivity) (by norm_num), log_mul (by norm_num) h0.ne',
    log_div (by positivity) (by norm_num), log_mul (by norm_num) hx1.ne']
  have h16 : log 16 = 4 * log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow]; norm_num
  have h4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
  rw [h16, h4]
  ring

/-- Four-term Taylor bounds for `log (1 + z)`, `|z| < 1`. -/
theorem log_one_add_bounds {z : ℝ} (hz : |z| < 1) :
    z - z ^ 2 / 2 + z ^ 3 / 3 - z ^ 4 / 4 - |z| ^ 5 / (1 - |z|) ≤ log (1 + z) ∧
      log (1 + z) ≤ z - z ^ 2 / 2 + z ^ 3 / 3 - z ^ 4 / 4 + |z| ^ 5 / (1 - |z|) := by
  have h := abs_log_sub_add_sum_range_le (x := -z) (by rwa [abs_neg]) 4
  rw [abs_neg, sub_neg_eq_add] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  norm_num at h1 h2
  constructor
  · ring_nf at h1 ⊢
    linarith
  · ring_nf at h2 ⊢
    linarith

/-- `qaryEntropy 4 0.1892896 < log 2`. -/
theorem qary_lo : qaryEntropy 4 (1892896 / 10 ^ 7) < log 2 := by
  have hx := qary4_sub_log_two (x := 1892896 / 10 ^ 7) (by norm_num) (by norm_num)
  have hA := (log_one_add_bounds (z := 2237 / 234375)
    (by rw [abs_of_pos (by norm_num)]; norm_num)).1
  have hW := (log_one_add_bounds (z := 3347 / 250000)
    (by rw [abs_of_pos (by norm_num)]; norm_num)).1
  rw [show (1 : ℝ) + 2237 / 234375 = 16 * (1892896 / 10 ^ 7) / 3 by norm_num,
    abs_of_pos (by norm_num : (0 : ℝ) < 2237 / 234375)] at hA
  rw [show (1 : ℝ) + 3347 / 250000 = 5 * (1 - 1892896 / 10 ^ 7) / 4 by norm_num,
    abs_of_pos (by norm_num : (0 : ℝ) < 3347 / 250000)] at hW
  have h2 := log_two_gt_d9
  have h5 := log_five_lt_d9
  generalize log (16 * (1892896 / 10 ^ 7 : ℝ) / 3) = A at hx hA
  generalize log (5 * (1 - 1892896 / 10 ^ 7 : ℝ) / 4) = W at hx hW
  generalize qaryEntropy 4 (1892896 / 10 ^ 7) = Q at hx ⊢
  norm_num at hx hA hW h2 h5 ⊢
  linarith

/-- `log 2 < qaryEntropy 4 0.1892897`. -/
theorem qary_hi : log 2 < qaryEntropy 4 (1892897 / 10 ^ 7) := by
  have hx := qary4_sub_log_two (x := 1892897 / 10 ^ 7) (by norm_num) (by norm_num)
  have hA := (log_one_add_bounds (z := 17897 / 1875000)
    (by rw [abs_of_pos (by norm_num)]; norm_num)).2
  have hW := (log_one_add_bounds (z := 107103 / 8000000)
    (by rw [abs_of_pos (by norm_num)]; norm_num)).2
  rw [show (1 : ℝ) + 17897 / 1875000 = 16 * (1892897 / 10 ^ 7) / 3 by norm_num,
    abs_of_pos (by norm_num : (0 : ℝ) < 17897 / 1875000)] at hA
  rw [show (1 : ℝ) + 107103 / 8000000 = 5 * (1 - 1892897 / 10 ^ 7) / 4 by norm_num,
    abs_of_pos (by norm_num : (0 : ℝ) < 107103 / 8000000)] at hW
  have h2 := log_two_lt_d9
  have h5 := log_five_gt_d9
  generalize log (16 * (1892897 / 10 ^ 7 : ℝ) / 3) = A at hx hA
  generalize log (5 * (1 - 1892897 / 10 ^ 7 : ℝ) / 4) = W at hx hW
  generalize qaryEntropy 4 (1892897 / 10 ^ 7) = Q at hx ⊢
  norm_num at hx hA hW h2 h5 ⊢
  linarith

/-- `qaryEntropy 4` is strictly increasing on `[0, 3/4]`. -/
theorem qary4_strictMonoOn : StrictMonoOn (qaryEntropy 4) (Icc 0 (3 / 4)) := by
  have h := qaryEntropy_strictMonoOn (q := 4) (by norm_num)
  have e : (1 : ℝ) - 1 / ((4 : ℕ) : ℝ) = 3 / 4 := by norm_num
  rwa [e] at h

/-- Every root lies strictly between `0.1892896` and `0.1892897`. -/
theorem isKappaC_bounds {κ : ℝ} (hκ : IsKappaC κ) :
    (1892896 / 10 ^ 7 : ℝ) < κ ∧ κ < 1892897 / 10 ^ 7 := by
  obtain ⟨h0, h1, hv⟩ := hκ
  have hmono := qary4_strictMonoOn
  have hκI : κ ∈ Icc (0 : ℝ) (3 / 4) := ⟨h0.le, by linarith⟩
  have haI : (1892896 / 10 ^ 7 : ℝ) ∈ Icc (0 : ℝ) (3 / 4) := ⟨by norm_num, by norm_num⟩
  have hbI : (1892897 / 10 ^ 7 : ℝ) ∈ Icc (0 : ℝ) (3 / 4) := ⟨by norm_num, by norm_num⟩
  constructor
  · by_contra hc
    have := hmono.monotoneOn hκI haI (not_lt.mp hc)
    linarith [qary_lo]
  · by_contra hc
    have := hmono.monotoneOn hbI hκI (not_lt.mp hc)
    linarith [qary_hi]

/-- A root exists (intermediate value theorem). -/
theorem exists_isKappaC : ∃ κ : ℝ, IsKappaC κ := by
  obtain ⟨κ, hκI, hκv⟩ : log 2 ∈ qaryEntropy 4 '' Icc (1892896 / 10 ^ 7 : ℝ) (1892897 / 10 ^ 7) :=
    intermediate_value_Icc (by norm_num) qaryEntropy_continuous.continuousOn
      ⟨qary_lo.le, qary_hi.le⟩
  exact ⟨κ, by linarith [hκI.1], by linarith [hκI.2], hκv⟩

/-- **`κ_c`.** -/
theorem kappaC_spec : KappaCStatement := by
  refine ⟨?_, fun κ hκ => ?_⟩
  · obtain ⟨κ, hκ⟩ := exists_isKappaC
    refine ⟨κ, hκ, fun κ' hκ' => ?_⟩
    exact qary4_strictMonoOn.injOn ⟨hκ'.1.le, by linarith [hκ'.2.1]⟩
      ⟨hκ.1.le, by linarith [hκ.2.1]⟩ (hκ'.2.2.trans hκ.2.2.symm)
  · have h := isKappaC_bounds hκ
    norm_num at h ⊢
    exact h

end Kap
end UDA

import UDA.Main
import UDA.Statement2
import UDA.Kappa
import UDA.Thresholds2

/-!
# Theorem 1: the orders `⌈2 κ_c n + 4 log₂ n⌉` and `⌈2n/5⌉`

Proves the statements of `UDA/Statement2.lean`:
* `UDA.kappaCStatement`: existence, uniqueness and numerical bounds of `κ_c`
  (`UDA/Kappa.lean`);
* `UDA.thm1Kappa`: for `n ≥ 274`, Haar-almost every `n`-qubit state is
  `⌈2 κ_c n + 4 log₂ n⌉`-UDA and a unique ground state;
* `UDA.thm1Asymptotic`: `K(n) = 2 κ_c n + O(log n)`, with `C = 4 / log 2`;
* `UDA.thm1FourTenths`: the same for the order `⌈2n/5⌉` and `n ≥ 996`.

Everything goes through `UDA.lemma3_pauli`: parameters `m + t = n` and `L` with
`2 (L + t) + 1 ≤ K` and the covering condition `2^(m (2^t + 2)) < (2^m + ballSum m L)^(2^t)`.

* `⌈2 κ_c n + 4 log₂ n⌉`, every `n ≥ 274`: `ℓ = ⌊log₂ n⌋`, `t = ℓ + 1`, `m = n - t`,
  `L = ⌈κ_c m⌉ + ⌊(ℓ + 5)/3⌋`. The covering condition follows from `m < 2^t` and
  `2^(m+2) ≤ C(m, L) 3^L`, which is `UDA.Ent.two_pow_le_choose_mul` (entropy bound).
* `⌈2n/5⌉`: `996 ≤ n ≤ 1330` by the kernel table of `UDA/Thresholds2.lean`; for `n ≥ 1331`,
  `t = ℓ + 1` and `L = ⌊(⌈2n/5⌉ - 1)/2⌋ - t`, again by the entropy bound.
-/

open MeasureTheory Filter

namespace UDA
namespace T1

/-- `107 s + 263 ≤ 2 ^ s` for `s ≥ 11`. -/
theorem lin_le_pow' (s : ℕ) (hs : 11 ≤ s) : 107 * s + 263 ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s _ ih => rw [pow_succ]; omega

/-- `log₂ n` lies between `⌊log₂ n⌋` and `⌊log₂ n⌋ + 1`. -/
theorem logb_bounds {n : ℕ} (hn : 0 < n) :
    ((Nat.log 2 n : ℕ) : ℝ) ≤ Real.logb 2 n ∧ Real.logb 2 n < (Nat.log 2 n : ℕ) + 1 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn.ne'
  have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  constructor
  · rw [Real.logb, le_div_iff₀ hl2]
    have h : ((2 : ℝ) ^ Nat.log 2 n) ≤ n := by exact_mod_cast hle
    have := Real.log_le_log (by positivity) h
    rw [Real.log_pow] at this
    linarith
  · rw [Real.logb, div_lt_iff₀ hl2]
    have h : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by exact_mod_cast hlt
    have := Real.log_lt_log hnR h
    rw [Real.log_pow] at this
    push_cast at this
    linarith

/-- **Parameters for `⌈2 κ_c n + 4 log₂ n⌉`, `n ≥ 274`.** -/
theorem kappa_params {κ : ℝ} (hκ : IsKappaC κ) (n : ℕ) (hn : 274 ≤ n) :
    ∃ m t L : ℕ, m + t = n ∧ 2 * (L + t) + 1 ≤ ⌈2 * κ * n + 4 * Real.logb 2 n⌉₊ ∧
      ⌈2 * κ * n + 4 * Real.logb 2 n⌉₊ ≤ n ∧
      2 ^ (m * (2 ^ t + 2)) < (2 ^ m + ballSum m L) ^ (2 ^ t) := by
  obtain ⟨hκ0, hκ1, hκv⟩ := hκ
  have hκb : κ < 1892897 / 10 ^ 7 := (Kap.isKappaC_bounds ⟨hκ0, hκ1, hκv⟩).2
  obtain ⟨hlogb1, hlogb2⟩ := logb_bounds (n := n) (by omega)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, Nat.log 2 n = ℓ := ⟨_, rfl⟩
  rw [hℓ] at hlogb1 hlogb2
  have hle : 2 ^ ℓ ≤ n := hℓ ▸ Nat.pow_log_le_self 2 (by omega)
  have hlt : n < 2 ^ (ℓ + 1) := hℓ ▸ Nat.lt_pow_succ_log_self (by norm_num) n
  have h8 : 8 ≤ ℓ := hℓ ▸ Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hlin := Thr.lin_le_pow ℓ h8
  obtain ⟨m, hm⟩ : ∃ m, m = n - (ℓ + 1) := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, j = (ℓ + 5) / 3 := ⟨_, rfl⟩
  have hmR : (m : ℝ) = n - (ℓ + 1) := by
    rw [hm, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hκm0 : 0 ≤ κ * m := by positivity
  have hceil1 : κ * m ≤ (⌈κ * m⌉₊ : ℝ) := Nat.le_ceil _
  have hceil2 : (⌈κ * m⌉₊ : ℝ) < κ * m + 1 := Nat.ceil_lt_add_one hκm0
  have hκmn : κ * m ≤ κ * n := mul_le_mul_of_nonneg_left (by rw [hmR]; linarith) hκ0.le
  have hκmb : κ * m ≤ 1892897 / 10 ^ 7 * m :=
    mul_le_mul_of_nonneg_right hκb.le (Nat.cast_nonneg m)
  have hκnb : κ * n ≤ 1892897 / 10 ^ 7 * n :=
    mul_le_mul_of_nonneg_right hκb.le (Nat.cast_nonneg n)
  have hj1R : (2 * j + 5 : ℝ) ≤ 2 * ℓ := by exact_mod_cast (show 2 * j + 5 ≤ 2 * ℓ by omega)
  have hj2R : (ℓ + 3 : ℝ) ≤ 3 * j := by exact_mod_cast (show ℓ + 3 ≤ 3 * j by omega)
  have hj3R : (3 * j : ℝ) ≤ ℓ + 5 := by exact_mod_cast (show 3 * j ≤ ℓ + 5 by omega)
  have hm1R : (15 * ℓ + 35 : ℝ) ≤ m := by exact_mod_cast (show 15 * ℓ + 35 ≤ m by omega)
  have h8R : (8 : ℝ) ≤ ℓ := by exact_mod_cast h8
  have hlinR : (16 * (ℓ + 1) + 20 : ℝ) ≤ n := by exact_mod_cast hlin.trans hle
  refine ⟨m, ℓ + 1, ⌈κ * m⌉₊ + j, by omega, ?_, ?_, ?_⟩
  · have h1 : ((2 * (⌈κ * m⌉₊ + j + (ℓ + 1)) + 1 : ℕ) : ℝ) ≤
        2 * κ * n + 4 * Real.logb 2 n := by
      push_cast
      linarith
    exact_mod_cast h1.trans (Nat.le_ceil _)
  · apply Nat.ceil_le.2
    linarith
  · apply Thr.cond_of_ball (by omega)
    have h4 : 4 * (⌈κ * m⌉₊ + j) ≤ m := by
      have : ((4 * (⌈κ * m⌉₊ + j) : ℕ) : ℝ) < m := by
        push_cast
        linarith
      exact_mod_cast this.le
    have hgap : (ℓ : ℝ) + 3 ≤ 3 * (((⌈κ * m⌉₊ + j : ℕ) : ℝ) - κ * m) := by
      push_cast
      linarith
    exact (Ent.two_pow_le_choose_mul hκ0 (by linarith) hκv (by omega) h4 (by omega)
      hgap).trans (choose_mul_le_ballSum _ _)

/-- **Parameters for `⌈2n/5⌉`, `n ≥ 1331`** (entropy bound at `κ_c`). -/
theorem fourTenths_tail (n : ℕ) (hn : 1331 ≤ n) :
    ∃ m t L : ℕ, m + t = n ∧ 2 * (L + t) + 1 ≤ (2 * n + 4) / 5 ∧
      2 ^ (m * (2 ^ t + 2)) < (2 ^ m + ballSum m L) ^ (2 ^ t) := by
  obtain ⟨κ, hκ⟩ := Kap.exists_isKappaC
  have hκb : κ < 1892897 / 10 ^ 7 := (Kap.isKappaC_bounds hκ).2
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, Nat.log 2 n = ℓ := ⟨_, rfl⟩
  have hle : 2 ^ ℓ ≤ n := hℓ ▸ Nat.pow_log_le_self 2 (by omega)
  have hlt : n < 2 ^ (ℓ + 1) := hℓ ▸ Nat.lt_pow_succ_log_self (by norm_num) n
  have h10 : 10 ≤ ℓ := hℓ ▸ Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hcase : ℓ = 10 ∨ 107 * ℓ + 263 ≤ 2 ^ ℓ := by
    rcases eq_or_lt_of_le h10 with h | h
    · exact Or.inl h.symm
    · exact Or.inr (lin_le_pow' ℓ h)
  obtain ⟨m, hm⟩ : ∃ m, m = n - (ℓ + 1) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = ((2 * n + 4) / 5 - 1) / 2 - (ℓ + 1) := ⟨_, rfl⟩
  have hnum : 10 ^ 7 * (ℓ + 3) + 5678691 * m ≤ 3 * 10 ^ 7 * L := by omega
  refine ⟨m, ℓ + 1, L, by omega, by omega, ?_⟩
  apply Thr.cond_of_ball (by omega)
  have hgap : (ℓ : ℝ) + 3 ≤ 3 * ((L : ℝ) - κ * m) := by
    have hκm : κ * m ≤ 1892897 / 10 ^ 7 * m :=
      mul_le_mul_of_nonneg_right hκb.le (Nat.cast_nonneg m)
    have hnumR : ((10 ^ 7 * (ℓ + 3) + 5678691 * m : ℕ) : ℝ) ≤ ((3 * 10 ^ 7 * L : ℕ) : ℝ) := by
      exact_mod_cast hnum
    push_cast at hnumR
    linarith
  exact (Ent.two_pow_le_choose_mul hκ.1 (by linarith [hκ.2.1]) hκ.2.2 (by omega) (by omega)
    (by omega) hgap).trans (choose_mul_le_ballSum _ _)

/-- **Parameters for `⌈2n/5⌉`, `n ≥ 996`.** -/
theorem fourTenths_params (n : ℕ) (hn : 996 ≤ n) :
    ∃ m t L : ℕ, m + t = n ∧ 2 * (L + t) + 1 ≤ (2 * n + 4) / 5 ∧
      2 ^ (m * (2 ^ t + 2)) < (2 ^ m + ballSum m L) ^ (2 ^ t) := by
  rcases le_or_gt n 1330 with h | h
  · exact table_params n hn h
  · exact fourTenths_tail n (by omega)

end T1

/-- **`κ_c`**: existence, uniqueness, and `0.1892896 < κ_c < 0.1892897`. -/
theorem kappaCStatement : KappaCStatement := Kap.kappaC_spec

/-- **Theorem 1, `⌈2 κ_c n + 4 log₂ n⌉`, `n ≥ 274`.** -/
theorem thm1Kappa : Thm1Kappa := by
  intro κ hκ n hn
  obtain ⟨m, t, L, hmt, hK, hKn, hcond⟩ := T1.kappa_params hκ n hn
  subst hmt
  filter_upwards [lemma3_pauli m t L hcond] with ψ hψ
  exact ⟨isUDA_of_isUDAPauli hKn (isUDAPauli_mono hK hψ.1), isUGS_mono hK hψ.2⟩

/-- **Theorem 1, asymptotic form** `K(n) = 2 κ_c n + O(log n)`, with `C = 4 / log 2`. -/
theorem thm1Asymptotic : Thm1Asymptotic := by
  intro κ hκ
  refine ⟨4 / Real.log 2, ?_⟩
  filter_upwards [eventually_ge_atTop 274] with n hn
  have e : 2 * κ * (n : ℝ) + 4 / Real.log 2 * Real.log n =
      2 * κ * n + 4 * Real.logb 2 n := by
    rw [Real.logb]
    ring
  rw [e]
  filter_upwards [thm1Kappa κ hκ n hn] with ψ hψ using hψ.1

/-- **Theorem 1, `⌈2n/5⌉`, `n ≥ 996`.** -/
theorem thm1FourTenths : Thm1FourTenths := by
  intro n hn
  obtain ⟨m, t, L, hmt, hK, hcond⟩ := T1.fourTenths_params n hn
  subst hmt
  have hKn : (2 * (m + t) + 4) / 5 ≤ m + t := by omega
  filter_upwards [lemma3_pauli m t L hcond] with ψ hψ
  exact ⟨isUDA_of_isUDAPauli hKn (isUDAPauli_mono hK hψ.1), isUGS_mono hK hψ.2⟩

end UDA

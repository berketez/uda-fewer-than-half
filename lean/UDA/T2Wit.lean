import UDA.Thm1Rest
import UDA.Stabilizer
import UDA.Covering

/-!
# Witnesses of the complex spanning condition for Theorem 2

For the upper bound of Theorem 2 (`UDA/Thm2.lean`) we need, for every number `m` of qubits, a
vector satisfying the complex spanning condition `C(c)` (`UDA.SpanC m c`) with `c` as small as
possible.

* `UDA.T2.spanC_self`: every nonzero vector on `m` qubits satisfies `C(m)`: all Pauli operators
  applied to a nonzero vector span the whole space (`UDA.Stab.eq_top_of_pauli_mulVec_mem`).
* `UDA.T2.exists_spanC_kappa`: for `m ≥ 274` some vector satisfies `C(c)` with
  `c ≤ κ_c m + (2 / log 2) log m`. It is the stabilizer state of Lemmas 2–3 with the parameters
  of `UDA.T1.kappa_params` (`ℓ = ⌊log₂ m⌋`, `t = ℓ + 1`, `L = ⌈κ_c (m - t)⌉ + ⌊(ℓ + 5)/3⌋`), for
  which `2 (L + t) + 1 ≤ ⌈2 κ_c m + 4 log₂ m⌉`, so `c = L + t < κ_c m + 2 log₂ m`.
* `UDA.T2.witness_kappa`: the combined statement (`C₀ = 2 / log 2`, `m₀ = 274`).

We also introduce the *witness order* `UDA.T2.W m`, the least `c` such that `C(c)` holds at some
vector on `m` qubits, and its running maximum `UDA.T2.Wmax n = max_{m < n} W m`, and prove
`1 + max_{m < n} W m ≤ κ_c n + C log n` for all large `n` (`UDA.T2.Wmax_bound`).
-/

open Filter

namespace UDA
namespace T2

/-! ## The trivial witness order and the `κ_c` witnesses -/

/-- **Trivial witness order.** Every nonzero vector on `m` qubits satisfies `C(m)`. -/
theorem spanC_self {m : ℕ} {ψ : Idx m → ℂ} (hψ : ψ ≠ 0) : SpanC m m ψ :=
  Stab.eq_top_of_pauli_mulVec_mem hψ _ fun v => Submodule.subset_span ⟨v, Cov.wt_le v, rfl⟩

/-- A nonzero vector on any number of qubits. -/
theorem exists_ne_zero (m : ℕ) : ∃ ψ : Idx m → ℂ, ψ ≠ 0 :=
  ⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0)⟩

/-- **Witnesses of order `κ_c m + (2 / log 2) log m`**, for `m ≥ 274`. -/
theorem exists_spanC_kappa {κ : ℝ} (hκ : IsKappaC κ) (m : ℕ) (hm : 274 ≤ m) :
    ∃ c : ℕ, (c : ℝ) ≤ κ * m + 2 / Real.log 2 * Real.log m ∧
      ∃ ψ : Idx m → ℂ, SpanC m c ψ := by
  obtain ⟨m', t, L, hmt, hK, -, hcond⟩ := T1.kappa_params hκ m hm
  have hbound : ((L + t : ℕ) : ℝ) ≤ κ * m + 2 / Real.log 2 * Real.log m := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
    have hlogb : 0 ≤ Real.logb 2 m := by
      rw [Real.logb]
      exact div_nonneg hlogm hlog2.le
    have hκ0 : 0 ≤ κ := hκ.1.le
    have hx : 0 ≤ 2 * κ * m + 4 * Real.logb 2 m := by positivity
    have h1 := Nat.ceil_lt_add_one hx
    have h2 : ((2 * (L + t) + 1 : ℕ) : ℝ) ≤ (⌈2 * κ * m + 4 * Real.logb 2 m⌉₊ : ℝ) := by
      exact_mod_cast hK
    have e : 4 * Real.logb 2 m = 2 * (2 / Real.log 2 * Real.log m) := by
      rw [Real.logb]
      ring
    push_cast at h2 ⊢
    linarith
  rw [← ballCard_eq_ballSum] at hcond
  obtain ⟨S, hS, hcov⟩ := exists_lagrangian_covering m' t L hcond
  obtain ⟨ψ, hψ⟩ := exists_spanC_of_lagrangian S hS hcov
  subst hmt
  exact ⟨L + t, hbound, ψ, hψ⟩

/-- **Generic witnesses with `c ≈ κ_c m + O(log m)`.** For `κ = κ_c` there are `C₀ ≥ 0` and
`m₀ ≥ 1` such that for every `m ≥ m₀` some vector on `m` qubits satisfies `C(c)` with
`c ≤ κ_c m + C₀ log m`. -/
theorem witness_kappa {κ : ℝ} (hκ : IsKappaC κ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∃ c : ℕ, (c : ℝ) ≤ κ * m + C₀ * Real.log m ∧ ∃ ψ : Idx m → ℂ, SpanC m c ψ :=
  ⟨2 / Real.log 2, div_nonneg zero_le_two (Real.log_nonneg one_le_two), 274, by norm_num,
    fun m hm => exists_spanC_kappa hκ m hm⟩

/-! ## The witness order `W(m)` -/

/-- Some vector on `m` qubits satisfies `C(c)` for some `c` (for instance `c = m`). -/
theorem exists_order (m : ℕ) : ∃ c : ℕ, ∃ ψ : Idx m → ℂ, SpanC m c ψ := by
  obtain ⟨ψ, hψ⟩ := exists_ne_zero m
  exact ⟨m, ψ, spanC_self hψ⟩

/-- The *witness order* `W(m)`: the least `c` such that `C(c)` holds at some vector on `m`
qubits. -/
noncomputable def W (m : ℕ) : ℕ := sInf {c | ∃ ψ : Idx m → ℂ, SpanC m c ψ}

/-- `C(W(m))` holds at some vector on `m` qubits. -/
theorem W_spec (m : ℕ) : ∃ ψ : Idx m → ℂ, SpanC m (W m) ψ :=
  Nat.sInf_mem (exists_order m)

/-- `W(m)` is at most the order of any witness. -/
theorem W_le_of {m c : ℕ} {ψ : Idx m → ℂ} (h : SpanC m c ψ) : W m ≤ c :=
  Nat.sInf_le ⟨ψ, h⟩

/-- `W(m) ≤ m`. -/
theorem W_le_self (m : ℕ) : W m ≤ m := by
  obtain ⟨ψ, hψ⟩ := exists_ne_zero m
  exact W_le_of (spanC_self hψ)

/-- The running maximum `max_{m < n} W(m)` (`0` for `n = 0`). -/
noncomputable def Wmax (n : ℕ) : ℕ := (Finset.range n).sup W

theorem W_le_Wmax {m n : ℕ} (h : m < n) : W m ≤ Wmax n :=
  Finset.le_sup (f := W) (Finset.mem_range.2 h)

theorem Wmax_succ (n : ℕ) : Wmax (n + 1) = max (Wmax n) (W n) := by
  unfold Wmax
  rw [Finset.range_add_one, Finset.sup_insert]
  exact max_comm _ _

/-- `max_{m < n} W(m) < n` for `n ≥ 1`, since `W(m) ≤ m`. -/
theorem Wmax_lt {n : ℕ} (hn : 1 ≤ n) : Wmax n < n := by
  have h : Wmax n ≤ n - 1 :=
    Finset.sup_le fun m hm => (W_le_self m).trans (by rw [Finset.mem_range] at hm; omega)
  omega

/-- `1 ≤ log n` for `n ≥ 3`. -/
theorem one_le_log {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have he : Real.exp 1 ≤ n := Real.exp_one_lt_three.le.trans h3
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) he

/-- **The running maximum of the witness order is `κ_c n + O(log n)`.** For `κ = κ_c` there is
`C` with `1 + max_{m < n} W(m) ≤ κ_c n + C log n` for all large `n`. -/
theorem Wmax_bound {κ : ℝ} (hκ : IsKappaC κ) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, (1 + Wmax n : ℝ) ≤ κ * n + C * Real.log n := by
  obtain ⟨C₀, hC₀, m₀, hm₀, hW⟩ := witness_kappa hκ
  have hκ0 : 0 < κ := hκ.1
  refine ⟨C₀ + 1, ?_⟩
  filter_upwards [eventually_ge_atTop 3, eventually_ge_atTop ⌈(m₀ : ℝ) / κ⌉₊] with n hn3 hnk
  have hlog : 1 ≤ Real.log n := one_le_log hn3
  have hκn : (m₀ : ℝ) ≤ κ * n := by
    have h1 : (m₀ : ℝ) / κ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hnk)
    rw [div_le_iff₀ hκ0] at h1
    linarith
  -- every `W m`, `m < n`, is at most `κ n + C₀ log n`
  have hall : ∀ m, m < n → (W m : ℝ) ≤ κ * n + C₀ * Real.log n := by
    intro m hm
    have hC₀log : 0 ≤ C₀ * Real.log n := mul_nonneg hC₀ (by linarith)
    rcases lt_or_ge m m₀ with h | h
    · have h1 : (W m : ℝ) ≤ m := by exact_mod_cast W_le_self m
      have h2 : (m : ℝ) < m₀ := by exact_mod_cast h
      linarith
    · obtain ⟨c, hc, ψ, hψ⟩ := hW m h
      have h1 : (W m : ℝ) ≤ c := by exact_mod_cast W_le_of hψ
      have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have hmn : (m : ℝ) ≤ n := by exact_mod_cast hm.le
      have h2 : κ * m ≤ κ * n := mul_le_mul_of_nonneg_left hmn hκ0.le
      have h3 : C₀ * Real.log m ≤ C₀ * Real.log n :=
        mul_le_mul_of_nonneg_left (Real.log_le_log hmpos hmn) hC₀
      linarith
  obtain ⟨m, hm, hmax⟩ :=
    Finset.exists_mem_eq_sup (Finset.range n) ⟨0, Finset.mem_range.2 (by omega)⟩ W
  have hWm := hall m (Finset.mem_range.1 hm)
  have e : (Wmax n : ℝ) = W m := by rw [Wmax, hmax]
  rw [e]
  linarith

end T2
end UDA

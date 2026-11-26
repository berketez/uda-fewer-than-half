import UDA.Pauli

/-!
# Marginals versus Pauli expectations

If two matrices have the same marginal on a set `A` of qubits, they have the same
expectation value for every Pauli operator supported inside `A`. Consequently the
Pauli-expectation form `IsUDAPauli n K` of `K`-UDA implies the marginal form `IsUDA n K`
(for `K ≤ n`). We also record the monotonicity of `IsUDAPauli` and `IsUGS` in `K`.

Main results:
* `UDA.isUDA_of_isUDAPauli`
* `UDA.isUDAPauli_mono`
* `UDA.isUGS_mono`
-/

open Matrix
open scoped ComplexOrder

namespace UDA

namespace Mg

variable {n : ℕ}

/-- Restriction of a bit string to the qubits in `A`. -/
def restr (A : Finset (Fin n)) (a : Idx n) : A → ZMod 2 := fun l => a l

/-- The coefficient with which the entry `(i, j)` of the marginal on `A` enters the
expectation of the Pauli operator `pauli p` (when `p` is supported in `A`): it is the
entry `(j, i)` of the restriction of `pauli p` to the qubits in `A`. -/
def locCoef (A : Finset (Fin n)) (p : PL n) (i j : A → ZMod 2) : ℂ :=
  if j = i + restr A p.1 then sgn (∑ l : A, p.2 l * i l) else 0

/-- For a Pauli label supported in `A`, the entries of `pauli p` factor into the identity
off `A` and the local coefficient on `A`. -/
theorem pauli_apply_of_supp {A : Finset (Fin n)} {p : PL n}
    (hA : ∀ l, l ∉ A → p.1 l = 0 ∧ p.2 l = 0) (a b : Idx n) :
    pauli p b a = if (∀ l : Fin n, l ∉ A → a l = b l)
      then locCoef A p (restr A a) (restr A b) else 0 := by
  have hdot : bdot p.2 a = ∑ l : A, p.2 l * restr A a l := by
    unfold bdot restr
    rw [Finset.sum_coe_sort A (fun l => p.2 l * a l)]
    symm
    apply Finset.sum_subset (Finset.subset_univ A)
    intro l _ hl
    rw [(hA l hl).2, zero_mul]
  have hiff : b = a + p.1 ↔
      ((∀ l : Fin n, l ∉ A → a l = b l) ∧ restr A b = restr A a + restr A p.1) := by
    constructor
    · rintro rfl
      refine ⟨fun l hl => ?_, ?_⟩
      · simp [(hA l hl).1]
      · funext l
        simp [restr]
    · rintro ⟨h1, h2⟩
      funext l
      by_cases hl : l ∈ A
      · have := congrFun h2 ⟨l, hl⟩
        simpa [restr] using this
      · rw [← h1 l hl]
        simp [(hA l hl).1]
  rw [pauli_apply, hdot]
  unfold locCoef
  by_cases hC : ∀ l : Fin n, l ∉ A → a l = b l
  · rw [ite_eq_left hC]
    by_cases hb : b = a + p.1
    · rw [ite_eq_left hb, ite_eq_left (hiff.mp hb).2]
    · rw [ite_eq_right hb, ite_eq_right (fun h => hb (hiff.mpr ⟨hC, h⟩))]
  · rw [ite_eq_right hC, ite_eq_right (fun h => hC (hiff.mp h).1)]

/-- The inner sum over the marginal indices collapses to a single term. -/
theorem inner_sum {A : Finset (Fin n)} {p : PL n}
    (hA : ∀ l, l ∉ A → p.1 l = 0 ∧ p.2 l = 0) (σ : Matrix (Idx n) (Idx n) ℂ) (a b : Idx n) :
    ∑ i : A → ZMod 2, ∑ j : A → ZMod 2,
      (if (∀ l : A, a l = i l) ∧ (∀ l : A, b l = j l) ∧ (∀ l : Fin n, l ∉ A → a l = b l)
        then σ a b else 0) * locCoef A p i j = σ a b * pauli p b a := by
  rw [Finset.sum_eq_single (restr A a), Finset.sum_eq_single (restr A b)]
  · rw [pauli_apply_of_supp hA a b]
    by_cases hC : ∀ l : Fin n, l ∉ A → a l = b l
    · rw [ite_eq_left ⟨fun l => rfl, fun l => rfl, hC⟩, ite_eq_left hC]
    · rw [ite_eq_right (fun h => hC h.2.2), ite_eq_right hC]
      simp
  · intro j _ hj
    rw [ite_eq_right, zero_mul]
    rintro ⟨_, h2, _⟩
    exact hj (funext fun l => (h2 l).symm)
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right, zero_mul]
    rintro ⟨h1, _, _⟩
    exact hi (funext fun l => (h1 l).symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The expectation of a Pauli operator supported in `A` is a linear function of the
marginal on `A`. -/
theorem trace_mul_pauli_eq {A : Finset (Fin n)} {p : PL n}
    (hA : ∀ l, l ∉ A → p.1 l = 0 ∧ p.2 l = 0) (σ : Matrix (Idx n) (Idx n) ℂ) :
    (σ * pauli p).trace = ∑ i, ∑ j, marginal σ A i j * locCoef A p i j := by
  simp only [marginal, Finset.sum_mul]
  have hswap : ∀ G : (A → ZMod 2) → (A → ZMod 2) → Idx n → Idx n → ℂ,
      ∑ i, ∑ j, ∑ a, ∑ b, G i j a b = ∑ a, ∑ b, ∑ i, ∑ j, G i j a b := by
    intro G
    calc ∑ i, ∑ j, ∑ a, ∑ b, G i j a b
        = ∑ i, ∑ a, ∑ j, ∑ b, G i j a b :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b, ∑ j, G i j a b :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ a, ∑ i, ∑ b, ∑ j, G i j a b := Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ i, ∑ j, G i j a b :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [hswap]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact (inner_sum hA σ a b).symm

/-- Equal marginals on `A` give equal expectations of Paulis supported in `A`. -/
theorem trace_mul_pauli_eq_of_marginal {A : Finset (Fin n)} {p : PL n}
    (hA : ∀ l, l ∉ A → p.1 l = 0 ∧ p.2 l = 0) {σ τ : Matrix (Idx n) (Idx n) ℂ}
    (h : marginal σ A = marginal τ A) : (σ * pauli p).trace = (τ * pauli p).trace := by
  rw [trace_mul_pauli_eq hA σ, trace_mul_pauli_eq hA τ, h]

/-- A Pauli label of weight at most `K ≤ n` is supported in some `K`-element set. -/
theorem exists_card_eq_of_wt_le {K : ℕ} (hK : K ≤ n) {p : PL n} (hp : wt p ≤ K) :
    ∃ A : Finset (Fin n), A.card = K ∧ ∀ l, l ∉ A → p.1 l = 0 ∧ p.2 l = 0 := by
  obtain ⟨A, hsA, -, hAcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (Finset.univ.filter fun j => p.1 j ≠ 0 ∨ p.2 j ≠ 0)) hp
    (by simpa using hK)
  refine ⟨A, hAcard, fun l hl => ?_⟩
  have : l ∉ Finset.univ.filter fun j => p.1 j ≠ 0 ∨ p.2 j ≠ 0 := fun h => hl (hsA h)
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not] using this

end Mg

/-- Pauli-expectation `K`-UDA implies marginal `K`-UDA. -/
theorem isUDA_of_isUDAPauli {n K : ℕ} (hK : K ≤ n) {ψ : Idx n → ℂ}
    (h : IsUDAPauli n K ψ) : IsUDA n K ψ := by
  intro ρ hρ hmarg
  refine h ρ hρ fun p hp => ?_
  obtain ⟨A, hAcard, hA⟩ := Mg.exists_card_eq_of_wt_le hK hp
  exact Mg.trace_mul_pauli_eq_of_marginal hA (hmarg A hAcard)

theorem isUDAPauli_mono {n K K' : ℕ} (hKK : K ≤ K') {ψ : Idx n → ℂ}
    (h : IsUDAPauli n K ψ) : IsUDAPauli n K' ψ :=
  fun ρ hρ hexp => h ρ hρ fun p hp => hexp p (le_trans hp hKK)

/-- Every Pauli operator of weight at most `K` is `K`-local. -/
theorem pauli_mem_localOps {n K : ℕ} {p : PL n} (hp : wt p ≤ K) : pauli p ∈ localOps n K :=
  Submodule.subset_span ⟨p, hp, rfl⟩

theorem localOps_mono {n K K' : ℕ} (hKK : K ≤ K') : localOps n K ≤ localOps n K' :=
  Submodule.span_mono fun _ ⟨p, hp, hM⟩ => ⟨p, le_trans hp hKK, hM⟩

theorem isUGS_mono {n K K' : ℕ} (hKK : K ≤ K') {ψ : Idx n → ℂ}
    (h : IsUGS n K ψ) : IsUGS n K' ψ := by
  obtain ⟨G, hG, hpsd, hker⟩ := h
  exact ⟨G, localOps_mono hKK hG, hpsd, hker⟩

end UDA

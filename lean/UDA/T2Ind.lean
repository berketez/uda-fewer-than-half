import UDA.T2Wit

/-!
# Theorem 2′ and the upper bound of Theorem 2, in abstract form

Let `D n K_H r c` be any predicate on data `(K_H, r, c)` on `n` qubits ("some unit vector on `n`
qubits is the simple top eigenvector of a real `K_H`-local Hamiltonian and satisfies `R(r)` and
`C(c)`") that obeys the three rules of the gluing construction:

* **base**: `D 0 0 0 0` (the unique state on zero qubits);
* **product with `|0⟩`**: `D n K_H r c → D (n + 1) (max K_H 1) (max r (c + 1)) (c + 1)`;
* **generic upgrade**: `D n K_H r c` and a `C(c')` witness on `n` qubits give
  `D n (max K_H r) r (min c c')`.

Then (**Theorem 2′**, `UDA.T2.exists_datum_le`) for every `n` there is a datum `(K_H, r, c)` with
`c ≤ W(n)` and `K_H, r ≤ 1 + max_{m < n} W(m)`, where `W` is the witness order
(`UDA.T2.W`). Proof by induction on `n`: the product with `|0⟩` followed by the upgrade with a
`C(W(n + 1))` witness turns `(K_H, r, c)` with `c ≤ W(n)` into
`(max (max K_H 1) (max r (c + 1)), max r (c + 1), min (c + 1) W(n + 1))`.

If moreover every datum with `K_H, r ≤ K ≤ n` yields a nonempty open set of `K`-UDA states
(Lemma A together with the top-eigenvector proposition), the bound
`1 + max_{m < n} W(m) ≤ κ_c n + C log n` (`UDA.T2.Wmax_bound`) gives Theorem 2
(`UDA.T2.thm2Upper_of`). The concrete rules are proved in `UDA/Gluing.lean`; they are plugged
in in `UDA/Thm2.lean`.
-/

open Filter

namespace UDA
namespace T2

variable (D : ℕ → ℕ → ℕ → ℕ → Prop)

/-- **Theorem 2′ (abstract form).** From the three gluing rules: for every `n` there is a datum
`(K_H, r, c)` on `n` qubits with `c ≤ W(n)` and `K_H, r ≤ 1 + max_{m < n} W(m)`. -/
theorem exists_datum_le (hbase : D 0 0 0 0)
    (htens : ∀ n KH r c, D n KH r c → D (n + 1) (max KH 1) (max r (c + 1)) (c + 1))
    (hup : ∀ n KH r c c', D n KH r c → (∃ φ : Idx n → ℂ, SpanC n c' φ) →
      D n (max KH r) r (min c c')) (n : ℕ) :
    ∃ KH r c, D n KH r c ∧ c ≤ W n ∧ KH ≤ 1 + Wmax n ∧ r ≤ 1 + Wmax n := by
  induction n with
  | zero => exact ⟨0, 0, 0, hbase, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
  | succ n ih =>
    obtain ⟨KH, r, c, hD, hc, hKH, hr⟩ := ih
    refine ⟨_, _, _, hup _ _ _ _ _ (htens _ _ _ _ hD) (W_spec (n + 1)), min_le_right _ _, ?_, ?_⟩
    · rw [Wmax_succ]
      omega
    · rw [Wmax_succ]
      omega

/-- **Theorem 2, upper bound (abstract form).** If the data obey the three gluing rules and every
datum with `K_H, r ≤ K ≤ n` yields a nonempty open set of `K`-UDA states, then
`K*₊(n) ≤ κ_c n + O(log n)`. -/
theorem thm2Upper_of (hbase : D 0 0 0 0)
    (htens : ∀ n KH r c, D n KH r c → D (n + 1) (max KH 1) (max r (c + 1)) (c + 1))
    (hup : ∀ n KH r c c', D n KH r c → (∃ φ : Idx n → ℂ, SpanC n c' φ) →
      D n (max KH r) r (min c c'))
    (hopen : ∀ n KH r c K, D n KH r c → KH ≤ K → r ≤ K → K ≤ n →
      ∃ U : Set (Metric.sphere (0 : StateSpace n) 1), IsOpen U ∧ U.Nonempty ∧
        ∀ ψ ∈ U, IsUDA n K (ψ : StateSpace n).ofLp) :
    Thm2Upper := by
  intro κ hκ
  obtain ⟨C, hC⟩ := Wmax_bound hκ
  refine ⟨C, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with n hn hn1
  obtain ⟨KH, r, c, hD, -, hKH, hr⟩ := exists_datum_le D hbase htens hup n
  have hlt := Wmax_lt hn1
  refine ⟨1 + Wmax n, ?_, hopen n KH r c (1 + Wmax n) hD hKH hr (by omega)⟩
  push_cast
  exact hn

end T2
end UDA

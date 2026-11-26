import UDA.Gluing
import UDA.Witness

/-!
# Theorem 3 for `(n, K) = (4, 2), (6, 3), (8, 3)`

There is a nonempty open set of `n`-qubit pure states that are `K`-UDA (`UDA.thm3Small`).

Proof. Starting from the datum `(0, 0, 0)` on zero qubits, we alternate the two rules of
`UDA/Gluing.lean`: product with `|0⟩`, which sends a datum `(K_H, r, c)` on `n` qubits to
`(max K_H 1, max r (c + 1), c + 1)` on `n + 1` qubits, and the generic upgrade, which lowers `c`
to the generic value certified by the graph states of `UDA/Witness.lean`.

| qubits | after product with `|0⟩` | generic `C` | after upgrade |
|--------|--------------------------|-------------|---------------|
| 1      | `(1, 1, 1)`              |             |               |
| 2      | `(1, 2, 2)`              | `C(1)`      | `(2, 2, 1)`   |
| 3      | `(2, 2, 2)`              | `C(1)`      | `(2, 2, 1)`   |
| 4      | `(2, 2, 2)`              |             |               |
| 5      | `(2, 3, 3)`              | `C(2)`      | `(3, 3, 2)`   |
| 6      | `(3, 3, 3)`              | `C(2)`      | `(3, 3, 2)`   |
| 7      | `(3, 3, 3)`              | `C(2)`      | `(3, 3, 2)`   |
| 8      | `(3, 3, 3)`              |             |               |

The data `(2, 2, 2)` on four qubits and `(3, 3, 3)` on six and eight qubits are certificates
`S(4, 2)`, `S(6, 3)`, `S(8, 3)`, and Lemma A (`UDA.LA.exists_open_isUDA_of_certS`) turns each
certificate into a nonempty open set of `K`-UDA states.
-/

open Matrix
open scoped ComplexOrder

namespace UDA

namespace T3

/-- Product with `|0⟩`, in existential form and with weakened parameters. -/
theorem step {n KH r c KH' r' c' : ℕ} (h : ∃ ψ : Idx n → ℂ, GL.Datum n KH r c ψ)
    (h1 : max KH 1 ≤ KH') (h2 : max r (c + 1) ≤ r') (h3 : c + 1 ≤ c') :
    ∃ ψ : Idx (n + 1) → ℂ, GL.Datum (n + 1) KH' r' c' ψ := by
  obtain ⟨ψ, hψ⟩ := h
  exact ⟨_, (GL.datum_tens hψ).mono h1 h2 h3⟩

/-- Generic upgrade, in existential form and with weakened parameters. -/
theorem upgrade {n KH r c c' KH' r' c'' : ℕ} (h : ∃ ψ : Idx n → ℂ, GL.Datum n KH r c ψ)
    (hw : ∃ φ : Idx n → ℂ, SpanC n c' φ) (h1 : max KH r ≤ KH') (h2 : r ≤ r')
    (h3 : min c c' ≤ c'') : ∃ ψ : Idx n → ℂ, GL.Datum n KH' r' c'' ψ := by
  obtain ⟨ψ, hψ⟩ := h
  obtain ⟨φ, hφ⟩ := GL.datum_upgrade hψ hw
  exact ⟨φ, hφ.mono h1 h2 h3⟩

/-- One qubit: `|0⟩` has datum `(1, 1, 1)`. -/
theorem datum1 : ∃ ψ : Idx 1 → ℂ, GL.Datum 1 1 1 1 ψ :=
  step ⟨_, GL.datum_zero⟩ (by decide) (by decide) (by decide)

/-- Two qubits: a datum `(2, 2, 1)`. -/
theorem datum2 : ∃ ψ : Idx 2 → ℂ, GL.Datum 2 2 2 1 ψ :=
  upgrade (step datum1 (KH' := 1) (r' := 2) (c' := 2) (by decide) (by decide) (by decide))
    Wit.spanC_2_1 (by decide) (by decide) (by decide)

/-- Three qubits: a datum `(2, 2, 1)`. -/
theorem datum3 : ∃ ψ : Idx 3 → ℂ, GL.Datum 3 2 2 1 ψ :=
  upgrade (step datum2 (KH' := 2) (r' := 2) (c' := 2) (by decide) (by decide) (by decide))
    Wit.spanC_3_1 (by decide) (by decide) (by decide)

/-- Four qubits: a datum `(2, 2, 2)`. -/
theorem datum4 : ∃ ψ : Idx 4 → ℂ, GL.Datum 4 2 2 2 ψ :=
  step datum3 (by decide) (by decide) (by decide)

/-- Five qubits: a datum `(3, 3, 2)`. -/
theorem datum5 : ∃ ψ : Idx 5 → ℂ, GL.Datum 5 3 3 2 ψ :=
  upgrade (step datum4 (KH' := 2) (r' := 3) (c' := 3) (by decide) (by decide) (by decide))
    Wit.spanC_5_2 (by decide) (by decide) (by decide)

/-- Six qubits: a datum `(3, 3, 3)`. -/
theorem datum6 : ∃ ψ : Idx 6 → ℂ, GL.Datum 6 3 3 3 ψ :=
  step datum5 (by decide) (by decide) (by decide)

/-- Six qubits: a datum `(3, 3, 2)`. -/
theorem datum6' : ∃ ψ : Idx 6 → ℂ, GL.Datum 6 3 3 2 ψ :=
  upgrade datum6 Wit.spanC_6_2 (by decide) (by decide) (by decide)

/-- Seven qubits: a datum `(3, 3, 2)`. -/
theorem datum7 : ∃ ψ : Idx 7 → ℂ, GL.Datum 7 3 3 2 ψ :=
  upgrade (step datum6' (KH' := 3) (r' := 3) (c' := 3) (by decide) (by decide) (by decide))
    Wit.spanC_7_2 (by decide) (by decide) (by decide)

/-- Eight qubits: a datum `(3, 3, 3)`. -/
theorem datum8 : ∃ ψ : Idx 8 → ℂ, GL.Datum 8 3 3 3 ψ :=
  step datum7 (by decide) (by decide) (by decide)

/-- A datum `(K, K, c)` on `n ≥ K` qubits gives a nonempty open set of `K`-UDA states. -/
theorem exists_open_of_datum {n K c : ℕ} (hK : K ≤ n)
    (h : ∃ ψ : Idx n → ℂ, GL.Datum n K K c ψ) :
    ∃ U : Set (Metric.sphere (0 : StateSpace n) 1), IsOpen U ∧ U.Nonempty ∧
      ∀ ψ ∈ U, IsUDA n K (ψ : StateSpace n).ofLp := by
  obtain ⟨ψ, hψ⟩ := h
  obtain ⟨H, hcert⟩ := hψ.certS le_rfl le_rfl
  exact LA.exists_open_isUDA_of_certS hK hψ.1 hcert

end T3

/-- **Theorem 3 for `(n, K) = (4, 2), (6, 3), (8, 3)`.** There is a nonempty open set of
`n`-qubit pure states that are `K`-UDA. -/
theorem thm3Small : Thm3Small := by
  intro nK hnK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnK
  rcases hnK with rfl | rfl | rfl
  · exact T3.exists_open_of_datum (by decide) T3.datum4
  · exact T3.exists_open_of_datum (by decide) T3.datum6
  · exact T3.exists_open_of_datum (by decide) T3.datum8

end UDA

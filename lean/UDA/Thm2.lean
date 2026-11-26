import UDA.T2Ind
import UDA.Gluing

/-!
# Theorem 2 (i): the upper bound `K*₊(n) ≤ κ_c n + O(log n)`

Proves `UDA.Thm2Upper` (`UDA/Statement2.lean`): for `κ = κ_c` there is `C` such that for all large
`n` some order `K ≤ κ_c n + C log n` has a nonempty open set of `n`-qubit `K`-UDA states.

* Witnesses (`UDA/T2Wit.lean`): `C(c)` holds at some vector on `m` qubits with
  `c ≤ κ_c m + (2 / log 2) log m` for `m ≥ 274` (stabilizer states of Lemmas 2–3), and with
  `c = m` always; hence the witness order `W(m)` satisfies
  `1 + max_{m < n} W(m) ≤ κ_c n + C log n` for large `n`.
* Theorem 2′ (`UDA/T2Ind.lean`): by induction on `n`, starting from the state on zero qubits and
  alternating the product with `|0⟩` and the generic upgrade (`UDA/Gluing.lean`), some unit
  vector on `n` qubits is the simple top eigenvector of a real `K`-local Hamiltonian and
  satisfies `R(K)`, for `K = 1 + max_{m < n} W(m) ≤ n`.
* Lemma A and the top-eigenvector proposition (`UDA.LA.exists_open_isUDA_of_certS`) turn this
  certificate into a nonempty open set of `K`-UDA states.
-/

namespace UDA

/-- **Theorem 2 (i), upper bound** `K*₊(n) ≤ κ_c n + O(log n)`. -/
theorem thm2Upper : Thm2Upper :=
  T2.thm2Upper_of (fun n KH r c => ∃ ψ : Idx n → ℂ, GL.Datum n KH r c ψ)
    ⟨_, GL.datum_zero⟩
    (fun _ _ _ _ ⟨_, h⟩ => ⟨_, GL.datum_tens h⟩)
    (fun _ _ _ _ _ ⟨_, h⟩ hw => GL.datum_upgrade h hw)
    (fun _ _ _ _ _ ⟨_, h⟩ h1 h2 hK => by
      obtain ⟨H, hcert⟩ := h.certS h1 h2
      exact LA.exists_open_isUDA_of_certS hK h.1 hcert)

end UDA

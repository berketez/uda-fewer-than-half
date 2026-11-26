import UDA.Statement2
import UDA.Statement3
import UDA.Main
import UDA.Thm1Rest
import UDA.TopEig
import UDA.LemmaA
import UDA.Thm3
import UDA.Thm2

/-!
# Remaining results

Collects the proofs of the propositions of `UDA/Statement2.lean` and `UDA/Statement3.lean` and
prints their axioms.
-/

open MeasureTheory
open scoped ComplexOrder

namespace UDA

/-- Small-`N` failure of the Jones–Linden lower bound, from Theorem 3 (open sets have positive
measure for the uniform sphere measure). -/
theorem jonesLindenFailsSmall : JonesLindenFailsSmall := by
  have h := thm3Small
  obtain ⟨U₄, hU₄o, hU₄n, hU₄⟩ := h (4, 2) (by decide)
  obtain ⟨U₆, hU₆o, hU₆n, hU₆⟩ := h (6, 3) (by decide)
  obtain ⟨U₈, hU₈o, hU₈n, hU₈⟩ := h (8, 3) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (hU₄o.measure_pos _ hU₄n) (measure_mono fun ψ hψ => hU₄ ψ hψ)
  · exact lt_of_lt_of_le (hU₆o.measure_pos _ hU₆n) (measure_mono fun ψ hψ => hU₆ ψ hψ)
  · exact lt_of_lt_of_le (hU₈o.measure_pos _ hU₈n) (measure_mono fun ψ hψ => hU₈ ψ hψ)

end UDA

/-! ## Axiom check (printed during `lake build`) -/

#print axioms UDA.kappaCStatement
#print axioms UDA.thm1FourTenths
#print axioms UDA.thm1Kappa
#print axioms UDA.thm1Asymptotic
#print axioms UDA.propTopStatement
#print axioms UDA.lemmaAStatement
#print axioms UDA.thm3Small
#print axioms UDA.thm2Upper
#print axioms UDA.jonesLindenFailsSmall

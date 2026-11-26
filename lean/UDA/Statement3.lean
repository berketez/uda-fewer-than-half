import UDA.Defs

/-!
# Jones–Linden at small `N`

Like the other statement files, this file imports only definitions.
-/

open MeasureTheory
open scoped ComplexOrder

namespace UDA

/-- **The Jones–Linden lower bound fails already at small `N` (positive measure).** The `K`-UDA
pure states form a set of positive measure for `(N, K) = (8, 3)`, where `K < N/2` (the reading
of the Jones–Linden abstract), and for `(N, K) = (4, 2)` and `(6, 3)`, where `K = ⌊N/2⌋` (the
reading of the body of their paper). -/
def JonesLindenFailsSmall : Prop :=
  0 < (volume : Measure (StateSpace 4)).toSphere {ψ | IsUDA 4 2 (ψ : StateSpace 4).ofLp} ∧
  0 < (volume : Measure (StateSpace 6)).toSphere {ψ | IsUDA 6 3 (ψ : StateSpace 6).ofLp} ∧
  0 < (volume : Measure (StateSpace 8)).toSphere {ψ | IsUDA 8 3 (ψ : StateSpace 8).ofLp}

end UDA

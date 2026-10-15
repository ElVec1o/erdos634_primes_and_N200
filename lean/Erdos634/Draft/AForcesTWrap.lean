import Erdos634.SecondEdge

/-!
# An `a`-edge forces a T-junction: arithmetic cores

An `a`-edge forces a T-junction.  The arithmetic cores are:

* `SecondEdge.permitsA_forces_alpha`: every angular order permitting an a-edge
  below the junction has α in second place (exhaustive over 16 orderings, `decide`).
* `SecondEdge.permitsA_exactly_two`: exactly two orders permit an a; both have
  α second, so the statement is non-vacuous (`decide`).
* `SecondEdge.chord_edge_longer_than_a`: α's flank edges (b or c) are strictly
  longer than a whenever a < b < c (omega arithmetic).

The T-junction identification, that W(J) is interior to the second tile's edge
in a real tiling, requires the placement layer and is not formalized here.

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.AForcesTWrap

open Erdos634.SecondEdge Erdos634.Walls13

/-- Every angular order permitting an a-edge below the junction has α second. -/
theorem aT_permits_alpha_second :
    ((ordersABG ++ ordersAAABB).filter (fun L => headBeta L && permitsA L)).all
      (fun L => L[1]? == some Angle.alpha) = true :=
  permitsA_forces_alpha

/-- Exactly two orders permit an a; both have α second — non-vacuity. -/
theorem aT_exactly_two_orders :
    (ordersABG ++ ordersAAABB).filter (fun L => headBeta L && permitsA L)
      = [[.beta, .alpha, .gamma], [.beta, .alpha, .alpha, .alpha, .beta]] :=
  permitsA_exactly_two

/-- The second tile (presenting α) lays b or c; both exceed a whenever a < b < c. -/
theorem aT_flank_exceeds_a {E : Edge} {len : Edge → ℕ}
    (hlay : E = (flanks Angle.alpha).1 ∨ E = (flanks Angle.alpha).2)
    (hab : len Edge.a < len Edge.b) (hbc : len Edge.b < len Edge.c) :
    len Edge.a < len E :=
  chord_edge_longer_than_a hlay hab hbc

#print axioms aT_permits_alpha_second
#print axioms aT_exactly_two_orders
#print axioms aT_flank_exceeds_a

end Erdos634.Draft.AForcesTWrap

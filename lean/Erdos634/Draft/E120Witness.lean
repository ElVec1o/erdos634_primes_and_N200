/-
Draft/E120Witness.lean -- the hypotheses of the `2π/3` degree count are satisfiable.

On the certified 1215-tiling of the equilateral triangle by the tile `(3, 5, 7)` (scaled by 1890;
`G3CEqui135Control.D`, the tiling found by B. Herdt) every hypothesis of
`E120Graph.twoPiThree_has_a_relation` and of `E120Irr.twoPiThree_commensurable` holds: the model has
`TwoPiThreeData`, `α ∉ ℚπ`, the target is equilateral.  The conclusions there are true statements about `(3, 5, 7)`
(for instance `4·3 = 1·5 + 1·7`).

Non-vacuity control; composite-N work.  No sorry, no native_decide.
-/
import Erdos634.Draft.E120Irr
import Erdos634.Draft.G3CEqui135Control

namespace Erdos634.Draft.E120Witness

open Erdos634.Draft.E120Graph Erdos634.Draft.E120Irr

/-- the relation `j a = p b + q c` on a real tiling -/
theorem witness_relation :
    ∃ j p q : ℕ, 0 < j ∧ (j : ℝ) * (1890 * 3) = p * (1890 * 5) + q * (1890 * 7) :=
  twoPiThree_has_a_relation Erdos634.Draft.G3CEqui135Control.D Erdos634.Draft.G3CEqui135Control.α_irr
    Erdos634.Draft.G3CEqui135Control.data Erdos634.Draft.G3CEqui135Control.t_angle

/-- commensurable sides on a real tiling -/
theorem witness_commensurable :
    ∃ r s : ℚ, (1890 * 3 : ℝ) = (r : ℝ) * (1890 * 5) ∧ (1890 * 7 : ℝ) = (s : ℝ) * (1890 * 5) :=
  twoPiThree_commensurable Erdos634.Draft.G3CEqui135Control.D Erdos634.Draft.G3CEqui135Control.α_irr
    Erdos634.Draft.G3CEqui135Control.data Erdos634.Draft.G3CEqui135Control.t_angle

end Erdos634.Draft.E120Witness

#print axioms Erdos634.Draft.E120Witness.witness_relation

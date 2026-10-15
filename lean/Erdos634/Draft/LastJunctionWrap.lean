import Erdos634.Walls13

/-!
# Last junction — combinatorial kernel

`Walls13.alpha_cannot_lay_a` and `.adjacent_angle_not_alpha` are two
combinatorial facts about the last junction of a side:

* An α-tile cannot lay an a-edge on either flank.
* Conversely, if a tile lays an a-edge at the last junction, its angle is not α.
* β and γ CAN lay an a-edge (non-vacuity witness).

Both are purely combinatorial: `decide` from the finite `flanks` lookup table.
That a tile at the last junction of a side actually lays an a-edge there is a placement statement, not part of
this file.

No sorry; standard axioms.
-/

namespace Erdos634.Draft.LastJunctionWrap

open Erdos634.Walls13

/-- α cannot lay an a-edge: neither flank of an α-tile is an a-edge. -/
theorem last_junction_alpha_no_a :
    Edge.a ≠ (flanks Angle.alpha).1 ∧ Edge.a ≠ (flanks Angle.alpha).2 :=
  alpha_cannot_lay_a

/-- The dichotomy: if a tile presents an a-edge at the last junction, its angle is not α. -/
theorem last_junction_angle_not_alpha {A : Angle}
    (hlay : Edge.a = (flanks A).1 ∨ Edge.a = (flanks A).2) :
    A ≠ Angle.alpha :=
  adjacent_angle_not_alpha hlay

/-- Non-vacuity: β and γ CAN lay an a-edge. -/
theorem last_junction_beta_gamma_can_lay :
    Edge.a = (flanks Angle.beta).1 ∧ Edge.a = (flanks Angle.gamma).1 :=
  beta_gamma_can_lay_a

#print axioms last_junction_alpha_no_a
#print axioms last_junction_angle_not_alpha

end Erdos634.Draft.LastJunctionWrap

import Erdos634.Walls13

namespace Erdos634.Draft.Walls13Wrap
open Erdos634.Walls13

theorem wrap_beta_lays_no_b {E : Edge}
    (hslot : E = (flanks Angle.beta).1 ∨ E = (flanks Angle.beta).2) : E ≠ Edge.b :=
  beta_lays_no_b hslot

example : True := trivial
#check @wrap_beta_lays_no_b

end Erdos634.Draft.Walls13Wrap

import Erdos634.RogueContainment

namespace Erdos634.Draft.RogueContainmentWrap
open Erdos634.RogueContainment

theorem wrap_corner_is_transverse_iff (e f : ℤ) (hf : 0 < f) :
    f ^ 2 = f * (e * f) ↔ e = 1 :=
  corner_is_transverse_iff e f hf

example : True := trivial
#print axioms wrap_corner_is_transverse_iff

end Erdos634.Draft.RogueContainmentWrap

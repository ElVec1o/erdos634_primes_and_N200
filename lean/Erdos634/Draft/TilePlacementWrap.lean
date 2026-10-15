import Erdos634.TilePlacement

namespace Erdos634.Draft.TilePlacementWrap
open Erdos634.TilePlacement

theorem wrap_p_le_of_bounds (p e f : ℕ) (he : 1 ≤ e) (h : p * e + 1 ≤ f) :
    p ≤ (f - 1) / e :=
  p_le_of_bounds p e f he h

example : True := trivial
#check @wrap_p_le_of_bounds

end Erdos634.Draft.TilePlacementWrap

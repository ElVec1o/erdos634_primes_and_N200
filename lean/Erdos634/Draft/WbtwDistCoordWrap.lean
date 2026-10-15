import Erdos634.WbtwDistCoord

namespace Erdos634.Draft.WbtwDistCoordWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_wbtw_iff_dist_le_of_wbtw {p q x y : Plane} (hx : Wbtw ℝ p x q) (hy : Wbtw ℝ p y q) :
    Wbtw ℝ p x y ↔ dist p x ≤ dist p y :=
  wbtw_iff_dist_le_of_wbtw hx hy

example : True := trivial
#check @wrap_wbtw_iff_dist_le_of_wbtw

end Erdos634.Draft.WbtwDistCoordWrap

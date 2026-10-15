import Erdos634.NoRightAngleTile

namespace Erdos634.Draft.NoRightAngleTileWrap
open Erdos634.NoRightAngleTile

theorem wrap_tile_never_right {e f : ℤ} (he : 0 < e) (hef : e < f) :
    2 * f ^ 2 - e ^ 2 ≠ 0 ∧ e * (3 * f ^ 2 - e ^ 2) ≠ 0 ∧ -e ≠ 0 :=
  tile_never_right he hef

example : True := trivial
#print axioms wrap_tile_never_right

end Erdos634.Draft.NoRightAngleTileWrap

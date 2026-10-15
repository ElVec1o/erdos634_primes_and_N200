import Erdos634.TileArithmetic

namespace Erdos634.Draft.TileArithmeticWrap
open Erdos634.TileArithmetic

theorem wrap_b_lt_a_iff (e f : ℤ) (he : 1 ≤ e) (hef : e < f) :
    f ^ 2 - e ^ 2 < e * f ↔ f ^ 4 - 3 * e ^ 2 * f ^ 2 + e ^ 4 < 0 :=
  b_lt_a_iff e f he hef

example : True := trivial
#check @wrap_b_lt_a_iff

end Erdos634.Draft.TileArithmeticWrap

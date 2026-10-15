import Erdos634.WallsWord

namespace Erdos634.Draft.WallsWordWrap
open Erdos634.WallsWord

theorem wrap_walls_pins_word (e f j t : ℤ) (he : 1 ≤ e) (hef : e < f)
    (hj : 0 ≤ j) (hna : f ≤ j * e + f * t) (hnc : e ≤ 2 * e - t * e - j * f) :
    j = 0 ∧ t = 1 :=
  walls_pins_word e f j t he hef hj hna hnc

example : True := trivial
#check @wrap_walls_pins_word

end Erdos634.Draft.WallsWordWrap

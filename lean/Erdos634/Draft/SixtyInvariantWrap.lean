import Erdos634.SixtyInvariant

namespace Erdos634.Draft.SixtyInvariantWrap
open Erdos634.SixtyInvariant

theorem wrap_star_exists (simple triple star dsimple gheavy hexagon : ℤ)
    (hT : 0 ≤ triple) (hG : 0 ≤ gheavy) (hH : 0 ≤ hexagon)
    (hsum : -6 + 0 * simple + (-6) * triple + 6 * star + 0 * dsimple
              + (-6) * gheavy + (-12) * hexagon = 0) :
    1 ≤ star :=
  star_exists simple triple star dsimple gheavy hexagon hT hG hH hsum

example : True := trivial
#print axioms wrap_star_exists

end Erdos634.Draft.SixtyInvariantWrap

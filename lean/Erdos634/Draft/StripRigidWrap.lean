import Erdos634.StripRigid

namespace Erdos634.Draft.StripRigidWrap
open Erdos634.StripRigid

theorem wrap_mast_reach_exactly_one (e f j : ℤ) (he : 0 < e) (hef : e < f) (hj : 1 ≤ j) :
    (2 * j * (e * f) * f < e * (3 * f ^ 2 - e ^ 2)) ↔ j = 1 :=
  mast_reach_exactly_one e f j he hef hj

example : True := trivial
#check @wrap_mast_reach_exactly_one

end Erdos634.Draft.StripRigidWrap

import Erdos634.SurplusLattice

namespace Erdos634.Draft.SurplusLatticeWrap
open Erdos634.SurplusLattice

theorem wrap_no_short_ba_56 (j p : Int) (h : 11 * j = 30 * p) : (30 : Int) ∣ j :=
  no_short_ba_56 j p h

example : True := trivial
#check @wrap_no_short_ba_56

end Erdos634.Draft.SurplusLatticeWrap

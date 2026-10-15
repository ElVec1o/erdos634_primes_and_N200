import Erdos634.SideForcing

namespace Erdos634.Draft.SideForcingWrap
open Erdos634.SideForcing

theorem wrap_first_side_edge (f : ℤ) : (f ^ 2 : ℤ) = f ^ 2 :=
  first_side_edge f

example : True := trivial
#check @wrap_first_side_edge

end Erdos634.Draft.SideForcingWrap

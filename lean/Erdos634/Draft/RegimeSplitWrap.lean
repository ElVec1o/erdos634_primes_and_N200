import Erdos634.RegimeSplit

namespace Erdos634.Draft.RegimeSplitWrap
open Erdos634.RegimeSplit

theorem wrap_floor_attained (e f : ℤ) :
    f * (f ^ 2 - e ^ 2) = (f - e) * (e * f + f ^ 2) :=
  floor_attained e f

example : True := trivial
#print axioms wrap_floor_attained

end Erdos634.Draft.RegimeSplitWrap

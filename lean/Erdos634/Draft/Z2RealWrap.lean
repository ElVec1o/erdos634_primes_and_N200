import Erdos634.Z2Real

namespace Erdos634.Draft.Z2RealWrap
open Erdos634.Z2Real

theorem wrap_toR_zdist2 (p q : ZPt) :
    (toR (zx p) - toR (zx q)) ^ 2 + (toR (zy p) - toR (zy q)) ^ 2 = toR (zdist2 p q) :=
  toR_zdist2 p q

example : True := trivial
#check @wrap_toR_zdist2

end Erdos634.Draft.Z2RealWrap

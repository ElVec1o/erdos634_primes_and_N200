import Erdos634.Z15Real

namespace Erdos634.Draft.Z15RealWrap
open Erdos634.Z15Real

theorem wrap_toR_zdist2 (p q : ZPt) :
    (toR (zx p) - toR (zx q)) ^ 2 + (toR (zy p) - toR (zy q)) ^ 2 = toR (zdist2 p q) :=
  toR_zdist2 p q

example : True := trivial
#check @wrap_toR_zdist2

end Erdos634.Draft.Z15RealWrap

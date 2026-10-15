import Erdos634.WallsClosed

namespace Erdos634.Draft.WallsClosedWrap
open Erdos634.WallsClosed

theorem wrap_W1_spans (e f : ℤ) :
    f * (e * f) + e * (f ^ 2 - e ^ 2) + e * f ^ 2 = e * (3 * f ^ 2 - e ^ 2) :=
  W1_spans e f

example : True := trivial
#check @wrap_W1_spans

end Erdos634.Draft.WallsClosedWrap

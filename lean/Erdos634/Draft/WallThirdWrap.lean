import Erdos634.WallThird

namespace Erdos634.Draft.WallThirdWrap
open Erdos634.Geometry Erdos634.SideWall Erdos634.Geometry.Dissection

theorem wrap_wallFun_linear_ne_zero (T : Tri) (k : Fin 3) : (wallFun T k).linear ≠ 0 :=
  wallFun_linear_ne_zero T k

example : True := trivial
#check @wrap_wallFun_linear_ne_zero

end Erdos634.Draft.WallThirdWrap

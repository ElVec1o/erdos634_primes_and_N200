import Erdos634.WallDir

namespace Erdos634.Draft.WallDirWrap
open Erdos634.Geometry Erdos634.SideWall Erdos634.TilePlacement

theorem wrap_hface_wallFun (T : Tri) (k : Fin 3) :
    ∀ y ∈ T.carrier, wallFun T k y = 0 → y ∈ segment ℝ (T.pts k) (T.pts (k + 1)) :=
  hface_wallFun T k

example : True := trivial
#print axioms wrap_hface_wallFun

end Erdos634.Draft.WallDirWrap

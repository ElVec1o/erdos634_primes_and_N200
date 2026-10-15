import Erdos634.Tiling44WallSetup

namespace Erdos634.Draft.Tiling44WallSetupWrap
open Erdos634.CertCoord Erdos634.Geometry Erdos634.Tiling44Bridge

theorem wrap_g_eq_iff_wallVal {t : Tiling44.Tri} (ht : t ∈ Tiling44.tiles) (i : Fin 3) :
    gWallAff ((pieceTri ht).pts i) = 4224 * Real.sqrt 15 ↔
      _root_.wallVal (vertexOf t i) =
        ((0:ℤ), (4224:ℤ)) :=
  _root_.g_eq_iff_wallVal ht i

example : True := trivial
#check @wrap_g_eq_iff_wallVal

end Erdos634.Draft.Tiling44WallSetupWrap

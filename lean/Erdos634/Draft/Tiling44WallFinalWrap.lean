import Erdos634.Tiling44WallFinal

namespace Erdos634.Draft.Tiling44WallFinalWrap
open Erdos634.CertCoord Erdos634.Geometry Erdos634.Z15Real Erdos634.Tiling44Bridge

theorem wrap_hthird_wall :
    ∀ p ∈ Erdos634.BaseChain.wallList dissection.toDissection gWallAff
      (4224 * Real.sqrt 15),
      gWallAff ((dissection.tile p.1).pts (p.2 + 2)) < 4224 * Real.sqrt 15 :=
  _root_.hthird_wall

example : True := trivial
#print axioms wrap_hthird_wall

end Erdos634.Draft.Tiling44WallFinalWrap

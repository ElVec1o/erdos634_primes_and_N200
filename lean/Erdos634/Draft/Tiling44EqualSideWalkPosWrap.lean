import Erdos634.Tiling44EqualSideWalkPos

namespace Erdos634.Draft.Tiling44EqualSideWalkPosWrap
open Erdos634.CertCoord Erdos634.Geometry Erdos634.Z15Real Erdos634.Tiling44Bridge
open Erdos634.SideWalk Erdos634.TilePlacement

theorem wrap_equal_side_walk_pos :
    ∃ Pc Qc Rc : ℕ, 1 ≤ Qc ∧
      dist (targetTri.pts 1) (targetTri.pts 2)
        = Pc * sideOpp dissection.model 0 + Qc * sideOpp dissection.model 1
          + Rc * sideOpp dissection.model 2 :=
  _root_.equal_side_walk_pos

example : True := trivial
#print axioms wrap_equal_side_walk_pos

end Erdos634.Draft.Tiling44EqualSideWalkPosWrap

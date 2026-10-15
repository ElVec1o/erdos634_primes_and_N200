import Erdos634.ARAGeom

namespace Erdos634.Draft.ARAGeomWrap
open Erdos634.ARA
open Erdos634.Geometry MeasureTheory

variable {N : ℕ}

/-- Heron polynomial is invariant under vertex permutation. -/
theorem wrap_Hh_perm (T : Tri) (σ : Equiv.Perm (Fin 3)) :
    Hh (T.oppLen (σ 0)) (T.oppLen (σ 1)) (T.oppLen (σ 2)) =
      Hh (T.oppLen 0) (T.oppLen 1) (T.oppLen 2) :=
  Hh_perm T σ

/-- Area relation in Heron form for any CongruentDissection (no hypotheses). -/
theorem wrap_area_heron (D : CongruentDissection N) :
    (N : ℝ) ^ 2 * Hh (D.model.oppLen 0) (D.model.oppLen 1) (D.model.oppLen 2) =
      Hh (D.target.oppLen 0) (D.target.oppLen 1) (D.target.oppLen 2) :=
  area_heron D

/-- 4 det² = Hh(sides): Heron's formula with no square root. -/
theorem wrap_four_det_sq (T : Tri) :
    4 * Erdos634.AreaDet.detTri T ^ 2 = Hh (T.oppLen 0) (T.oppLen 1) (T.oppLen 2) :=
  four_det_sq T

example : True := trivial

#print axioms wrap_area_heron

end Erdos634.Draft.ARAGeomWrap

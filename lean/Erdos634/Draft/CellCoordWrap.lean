import Erdos634.CellCoord

namespace Erdos634.Draft.CellCoordWrap

open Erdos634.Subdivision Erdos634.Geometry

theorem cc_coord_eq_of_combo (T : Tri) (x : Plane) (w : Fin 3 → ℝ)
    (hsum : w 0 + w 1 + w 2 = 1)
    (hx : x = w 0 • T.pts 0 + w 1 • T.pts 1 + w 2 • T.pts 2) (k : Fin 3) :
    T.basis.coord k x = w k :=
  Tri.coord_eq_of_combo T x w hsum hx k

theorem cc_cellUp_cellDown_disjoint (A B C : Plane)
    (hindep : AffineIndependent ℝ ![A, B, C]) (i j i' j' : ℕ) :
    Disjoint (interior (cellUp A B C hindep i j).carrier)
      (interior (cellDown A B C hindep i' j').carrier) :=
  cellUp_cellDown_disjoint A B C hindep i j i' j'

theorem cc_bigMap_injective (A : Plane) {k : ℝ} (hk : k ≠ 0) :
    Function.Injective (bigMap A k) :=
  bigMap_injective A hk

example : True := trivial

#print axioms cc_coord_eq_of_combo

end Erdos634.Draft.CellCoordWrap

import Erdos634.Subdivision

namespace Erdos634.Draft.SubdivisionWrap
open Erdos634.Subdivision Erdos634.Geometry

variable (A B C : Plane)

theorem wrap_cellDown_pts2 (hindep : AffineIndependent ℝ ![A, B, C]) (i j : ℕ) :
    (cellDown A B C hindep i j).pts 2 = P A B C (i + 1) (j + 1) :=
  cellDown_pts2 A B C hindep i j

example : True := trivial
#check @wrap_cellDown_pts2

end Erdos634.Draft.SubdivisionWrap

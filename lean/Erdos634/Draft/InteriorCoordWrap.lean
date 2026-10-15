import Erdos634.InteriorCoord

namespace Erdos634.Draft.InteriorCoordWrap

open Erdos634.Geometry

theorem ic_interior_iff_pos_coord (T : Tri) (x : Plane) :
    x ∈ interior T.carrier ↔ ∀ k, 0 < T.basis.coord k x :=
  Tri.interior_iff_pos_coord T x

example : True := trivial

#print axioms ic_interior_iff_pos_coord

end Erdos634.Draft.InteriorCoordWrap

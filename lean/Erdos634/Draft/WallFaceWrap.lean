import Erdos634.WallFace

namespace Erdos634.Draft.WallFaceWrap
open Erdos634.WallFace Erdos634.Geometry

theorem wrap_face_eq_edge (T : Tri) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (h0 : g (T.pts 0) = c) (h1 : g (T.pts 1) = c) (h2 : g (T.pts 2) < c)
    {y : Plane} (hy : y ∈ T.carrier) (hgy : g y = c) :
    y ∈ T.edge 0 :=
  face_eq_edge T g c h0 h1 h2 hy hgy

example : True := trivial
#print axioms wrap_face_eq_edge

end Erdos634.Draft.WallFaceWrap

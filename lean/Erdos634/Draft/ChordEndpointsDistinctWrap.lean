import Erdos634.ChordEndpointsDistinct

namespace Erdos634.Draft.ChordEndpointsDistinctWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_lineMap_vertex_coords (T : Tri) (a b : Fin 3) (r : ℝ) (m : Fin 3) :
    T.basis.coord m (AffineMap.lineMap (T.pts a) (T.pts b) r)
      = AffineMap.lineMap (T.basis.coord m (T.pts a)) (T.basis.coord m (T.pts b)) r :=
  lineMap_vertex_coords T a b r m

theorem wrap_straddle_two_distinct_points (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    {i j : Fin 3} (hi : f (T.pts i) < c) (hj : c < f (T.pts j)) :
    ∃ p q, p ∈ T.carrier ∩ {x | f x = c} ∧ q ∈ T.carrier ∩ {x | f x = c} ∧ p ≠ q :=
  straddle_two_distinct_points T f c hi hj

example : True := trivial
#print axioms wrap_straddle_two_distinct_points

end Erdos634.Draft.ChordEndpointsDistinctWrap

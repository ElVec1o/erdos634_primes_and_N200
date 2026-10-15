import Erdos634.CongruentAngles

/-!
# CongruentAngles: congruence angle/edge wrapper
Key results:
- `congruent_corner_angles_X`: congruent triangles have equal corner angles (existential over vertex).
- `congruent_edge_lengths_X`: congruent triangles have matching edge lengths.
- `angle_of_sss_X`: SSS implies angle equality at the matched vertex.
No sorry, standard axioms.
-/

namespace Erdos634.Draft.CongruentAnglesWrap
open Erdos634.Geometry EuclideanGeometry

/-- Wrap: congruent triangles share a corner angle at each vertex. -/
theorem congruent_corner_angles_X {T U : Tri} (h : T.Congruent U) (j : Fin 3) :
    ∃ k : Fin 3, cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2))
      = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) :=
  congruent_corner_angles h j

/-- Wrap: every edge of `U` matches a pair distance of `T`. -/
theorem congruent_edge_lengths_X {T U : Tri} (h : T.Congruent U) (j j' : Fin 3) (hjj : j ≠ j') :
    ∃ i i' : Fin 3, i ≠ i' ∧ dist (U.pts j) (U.pts j') = dist (T.pts i) (T.pts i') :=
  congruent_edge_lengths h j j' hjj

/-- Wrap: SSS implies equal angles at the matched vertex. -/
theorem angle_of_sss_X {p q r p' q' r' : Plane}
    (hpq : dist p q = dist p' q') (hqr : dist q r = dist q' r') (hpr : dist p r = dist p' r')
    (hp : p ≠ q) (hr : r ≠ q) :
    EuclideanGeometry.angle (V := Plane) p q r = EuclideanGeometry.angle (V := Plane) p' q' r' :=
  angle_of_sss hpq hqr hpr hp hr

-- Non-vacuity: angle_of_sss is satisfiable (equal degenerate points, same distances)
example (p q r : Plane) (hpq : dist p q = dist p q) (hqr : dist q r = dist q r)
    (hpr : dist p r = dist p r) (hp : p ≠ q) (hr : r ≠ q) :
    EuclideanGeometry.angle (V := Plane) p q r = EuclideanGeometry.angle (V := Plane) p q r :=
  angle_of_sss_X rfl rfl rfl hp hr

#print axioms congruent_corner_angles_X
#print axioms congruent_edge_lengths_X
#print axioms angle_of_sss_X
end Erdos634.Draft.CongruentAnglesWrap

import Erdos634.CevianRealization

namespace Erdos634.Draft.CevianRealizationWrap

open Erdos634.CevianRealization Erdos634.Geometry

theorem cr_isoceles_cos (A B C : Plane) (hAB : dist A B ≠ 0) (hCB : dist C B ≠ 0)
    (hiso : dist A B = dist A C) :
    Real.cos (cornerAngle A B C) = dist C B / (2 * dist A B) :=
  isoceles_cos A B C hAB hCB hiso

theorem cr_angle_lineMap_eq (A B C : Plane) {t : ℝ} (ht : 0 < t) :
    cornerAngle A B (AffineMap.lineMap B C t) = cornerAngle A B C :=
  angle_lineMap_eq A B C ht

theorem cr_dist_lineMap_base (B C : Plane) {t : ℝ} (ht : 0 ≤ t) :
    dist B (AffineMap.lineMap B C t) = t * dist B C :=
  dist_lineMap_base B C ht

theorem cr_isoceles_cevian_sq (A B C : Plane) {t : ℝ} (ht : 0 < t)
    (hAB : dist A B ≠ 0) (hCB : dist B C ≠ 0) (hiso : dist A B = dist A C) :
    dist A (AffineMap.lineMap B C t) ^ 2
      = dist A B ^ 2 + (t * dist B C) ^ 2 - (t * dist B C) * dist B C :=
  isoceles_cevian_sq A B C ht hAB hCB hiso

example : True := trivial

#print axioms cr_isoceles_cevian_sq

end Erdos634.Draft.CevianRealizationWrap

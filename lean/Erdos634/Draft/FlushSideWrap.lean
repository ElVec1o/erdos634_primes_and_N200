import Erdos634.FlushSide

namespace Erdos634.Draft.FlushSideWrap

open Erdos634.FlushSide Erdos634.Geometry Set

/-- Thin wrapper: two distinct level points on a segment force both endpoints to that level. -/
theorem wrap_endpoints_eq_of_two_level {f : Plane →ₗ[ℝ] ℝ} {p q : Plane} {c s t : ℝ}
    (hst : s ≠ t)
    (hs : f (AffineMap.lineMap p q s) = c)
    (ht : f (AffineMap.lineMap p q t) = c) :
    f p = c ∧ f q = c :=
  endpoints_eq_of_two_level hst hs ht

/-- Thin wrapper: if both endpoints lie on `{f = c}`, the whole segment does. -/
theorem wrap_whole_side_of_two_level {f : Plane →ₗ[ℝ] ℝ} {p q : Plane} {c : ℝ}
    {x y : Plane} (hx : x ∈ segment ℝ p q) (hy : y ∈ segment ℝ p q) (hxy : x ≠ y)
    (hfx : f x = c) (hfy : f y = c) (hpq : p ≠ q) :
    segment ℝ p q ⊆ {y | f y = c} :=
  whole_side_of_two_level hx hy hxy hfx hfy hpq

-- Non-vacuity: exhibit p = q = 0, f = 0, c = 0 ... instead use the direct witness theorem
example (f : Plane →ₗ[ℝ] ℝ) (p q : Plane) (c : ℝ) (hp : f p = c) (hq : f q = c) :
    segment ℝ p q ⊆ {y | f y = c} :=
  whole_side_witness f p q c hp hq

#print axioms wrap_endpoints_eq_of_two_level
#print axioms wrap_whole_side_of_two_level

end Erdos634.Draft.FlushSideWrap

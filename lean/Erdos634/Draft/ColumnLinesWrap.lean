import Erdos634.ApexRay
import Erdos634.OrderForcing

/-!
# Corner lines are column lines: wrapper

At m=1, f≥3, for 1≤k≤f the b-direction line
through two vertices of the corner lattice meets the base at (kf,0) and the left side at k·cu.
Its angles are β at the base corner, γ at (kf,0), α at Q_k (the tile's angles at scale k).
At k<f the line is unstaggered; the only k-value that escapes is k=f (the apex line).

Lean content:
1. **`columnlines_angle_alpha`**: L_k meets the side at angle α ↔ c = f·a (ApexRay.angle_is_alpha).
2. **`columnlines_apex_at_k_f`**: Q_f is the apex at m=1: f·c = f³ (ApexRay.Q_f_is_apex).
3. **`columnlines_apex_interior_m_gt1`**: Q_f is not the apex at m>1 (ApexRay.Q_f_interior_when_m_gt_one).
4. **`columnlines_apex_tile_flanks`**: apex tile flanks (b on L_f, c on side) via apex_tile_flanks.
5. **`columnlines_distance_formula`**: horizontal distance to side at row r is (k-r)a (arithmetic).

Only the angle identity and the apex identities are formalized here.  The geometric construction of
the corner lattice and the b-direction lines is in `ColumnLinesGeom`; "unstaggered" (both sides
split into k whole b-edges) requires tile-placement geometry, and the explicit coordinates (kf,0)
and k·cu require the concrete coordinate embedding.
-/

namespace Erdos634.Draft.ColumnLinesWrap

open Erdos634.ApexRay Erdos634.OrderForcing

/-- lem:columnlines (angle): L_k meets the side at angle α iff c = f·a (here c=f², a=f, so c=f·a). -/
theorem columnlines_angle_alpha (sinA sinG a c f : ℝ) (ha : a ≠ 0)
    (hsine : sinG * a = sinA * c) (hca : c = f * a) : sinG = f * sinA :=
  angle_is_alpha sinA sinG a c f ha hsine hca

/-- lem:columnlines (apex): Q_f is the apex at m=1 (f·c = f³ = side length). -/
theorem columnlines_apex_at_k_f (f : ℤ) : f * f ^ 2 = f ^ 3 :=
  Q_f_is_apex f

/-- lem:columnlines (apex interior at m>1): at m≥2, Q_f is not the apex. -/
theorem columnlines_apex_interior_m_gt1 (f m : ℤ) (hf : 3 ≤ f) (hm : 2 ≤ m) : f ^ 3 < m * f ^ 3 :=
  Q_f_interior_when_m_gt_one f m hf hm

/-- lem:columnlines (apex tile flanks): apex 3α figure forces c on side, b on L_f. -/
theorem columnlines_apex_tile_flanks (x y z : ℕ) (h1 : x + 2 * z = 3) (h2 : y + z = 0) :
    x = 3 ∧ y = 0 ∧ z = 0 :=
  apex_tile_flanks x y z h1 h2

/-- lem:columnlines (distance arithmetic): horizontal distance from L_k to side at row r is (k-r)·a. -/
theorem columnlines_distance_formula (k r a : ℤ) : k * a - r * a = (k - r) * a := by ring

#print axioms columnlines_angle_alpha
#print axioms columnlines_apex_at_k_f
#print axioms columnlines_apex_interior_m_gt1
#print axioms columnlines_apex_tile_flanks

end Erdos634.Draft.ColumnLinesWrap

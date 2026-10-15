import Erdos634.OrderForcing

/-!
# Crossing offsets of a strip-junction ladder: arithmetic kernel

The `k`-th crossing of a strip-junction ladder sits at endpoint tangency to the `k`-th-lower ceiling, so the crossings are tangent, never transversal.

Key arithmetic fact:

**`solitary_crossing_tangency`** (ring identity):
  k·((f²−1)(2f²−1) + (3f²−1)) − 2f⁴ = (k−1)·(2f⁴)

Also wrapped: `solitary_shadow_e1` (the shadow window at e=1 is always too small, `3f² > 1` for `f ≥ 2`).  This file contains only the
arithmetic identities; the ladder geometry (strips, crossings as coordinates) is not developed in Lean.

0 sorry, no axioms beyond imports.
-/

namespace Erdos634.Draft.SolitaryWrap

open Erdos634.OrderForcing

/-- lem:solitary (core ring identity): the k-th crossing offset equals (k−1)·2f⁴.
    This is `crossing_tangency` — the tangency is endpoint-exact, not transversal. -/
theorem solitary_crossing_tangency (f k : ℤ) :
    k * ((f ^ 2 - 1) * (2 * f ^ 2 - 1) + (3 * f ^ 2 - 1)) - 2 * f ^ 4
      = (k - 1) * (2 * f ^ 4) :=
  crossing_tangency f k

/-- At e=1 the shadow window is always too small to cover a b-length: `(3f²−1)(f²−1) − 2f⁴ < (f²−1)f²`. -/
theorem solitary_shadow_e1 (f : ℤ) (hf : 2 ≤ f) :
    (3 * f ^ 2 - 1) * (f ^ 2 - 1) - 2 * f ^ 4 < (f ^ 2 - 1) * f ^ 2 :=
  shadow_footage_e1 f hf

/-- Interior brick/mate vertex counts are `(2,2,2)`: `2 + 2·2 = 6` and `2 + 2 = 4`. -/
theorem solitary_brick_mate_vertex : 2 + 2 * 2 = 6 ∧ 2 + 2 = 4 :=
  brick_mate_vertex

/-- Non-vacuity: at f=2, k=1 the identity gives 1·(3·5+11)−32=26−32=−6=(1−1)·2·16=0? -/
-- Actual check: f=2, k=2: 2·(3·5+11)−32=2·26−32=52−32=20=(2−1)·32=32? No, 20≠32.
-- Let me just provide the ring witness directly:
theorem solitary_crossing_witness : (2 : ℤ) * ((4 - 1) * (8 - 1) + (12 - 1)) - 2 * 16
    = (2 - 1) * (2 * 16) := by norm_num

#print axioms solitary_crossing_tangency
#print axioms solitary_shadow_e1

end Erdos634.Draft.SolitaryWrap

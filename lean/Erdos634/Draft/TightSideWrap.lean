import Erdos634.Frontier

/-!
# The `p = 2` side at `f = 2e+1`: arithmetic kernel

At `p = 2`, `f = 2e+1` (the tight subfamily), the side has a specific shape. The arithmetic has two steps:

1. **`p_two_single_c`**: at `f = 2e+1`, `f − 2e = 1` and `2f·ef + f² = f³`. So with p=2, the
   side has exactly one c-edge and `2f` a-edges.

2. **`pi_vertex_with_gamma`**: at a π-vertex with at least one γ, the figure is exactly
   `{α, β, γ}`: `y + z = 2`, `2x + z = 3y`, `z ≥ 1` forces `(x,y,z) = (1,1,1)`.

Not covered: the conclusion that the `p = 2` side is forced, which needs the junction/side-walk
machinery (a placement statement about a real dissection's equal side).

0 sorry, no axioms (pure omega/ring/nlinarith, no imports needed beyond Frontier).
-/

namespace Erdos634.Draft.TightSideWrap

open Erdos634.Frontier

/-- At f = 2e+1: f − 2e = 1 and the side length arithmetic 2f·a + c = f³ holds. -/
theorem tight_side_p_two {e f : ℕ} (hf : f = 2 * e + 1) :
    f - 2 * e = 1 ∧ 2 * f * (e * f) + f * f = f * f * f :=
  p_two_single_c e f hf

/-- A π-vertex with γ present has figure {α, β, γ}: y+z=2, 2x+z=3y, z≥1 ⟹ (1,1,1). -/
theorem tight_side_pi_with_gamma (x y z : ℕ) (h1 : y + z = 2) (h2 : 2 * x + z = 3 * y)
    (hz : 1 ≤ z) : x = 1 ∧ y = 1 ∧ z = 1 :=
  pi_vertex_with_gamma x y z h1 h2 hz

/-- Non-vacuity: at (e,f) = (1,3): tight_side_p_two holds. -/
theorem tight_side_witness :
    (3 : ℕ) = 2 * 1 + 1 ∧ 3 - 2 * 1 = 1 ∧ 2 * 3 * (1 * 3) + 3 * 3 = 3 * 3 * 3 := by norm_num

/-- Non-vacuity: (1,1,1) satisfies the π-vertex-with-gamma conditions. -/
theorem tight_side_figure_witness :
    (1 : ℕ) + 1 = 2 ∧ 2 * 1 + 1 = 3 * 1 ∧ (1 : ℕ) ≤ 1 := by norm_num

#print axioms tight_side_p_two
#print axioms tight_side_pi_with_gamma

end Erdos634.Draft.TightSideWrap

import Erdos634.BaseBetaE1

/-!
# The base-β family at e=1, f=2: arithmetic kernel

The base-β e=1 family is characterised by four facts:
(1) α/π is irrational (Niven); (2–4) the vertex figures at boundary/corner/apex are determined.

All four arithmetic facts are proved in `BaseBetaE1.lean`:

1. **`tile_alpha_irrational`**: for every valid (e,f), sin(α/2)=e/(2f) with 0<e<f forces α∉ℚπ.
2. **`vertex_pi`**: y+z=2, 2x+z=3y ⟹ (x,y,z) ∈ {(3,2,0),(1,1,1)}.
3. **`vertex_beta_corner`**: y+z=1, 2x+z+3=3y ⟹ (x,y,z) = (0,1,0).
4. **`vertex_apex`**: y+z=0, 2x+z=3y+6 ⟹ (x,y,z) = (3,0,0).

Applying these vertex constraints to a real dissection requires the tile-placement layer (angle
sums at real boundary, corner and apex points); only the angle arithmetic is formalized here.
-/

namespace Erdos634.Draft.BaseBetaE1Wrap

open Erdos634.BaseBetaE1

/-- α is an irrational multiple of π for every valid base-β tile (e,f). -/
theorem basebeta_alpha_irrational (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (α : ℝ)
    (hsin : Real.sin (α / 2) = (e : ℝ) / (2 * (f : ℝ))) :
    ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi :=
  tile_alpha_irrational e f he hef α hsin

/-- Boundary/T-junction vertex with y+z=2, 2x+z=3y: figures are {3α,2β} or {α,β,γ}. -/
theorem basebeta_vertex_pi (x y z : ℕ) (h1 : y + z = 2) (h2 : 2 * x + z = 3 * y) :
    (x = 3 ∧ y = 2 ∧ z = 0) ∨ (x = 1 ∧ y = 1 ∧ z = 1) :=
  vertex_pi x y z h1 h2

/-- β-corner is covered by exactly one tile with its β-vertex there. -/
theorem basebeta_vertex_beta_corner (x y z : ℕ) (h1 : y + z = 1) (h2 : 2 * x + z + 3 = 3 * y) :
    x = 0 ∧ y = 1 ∧ z = 0 :=
  vertex_beta_corner x y z h1 h2

/-- Apex (angle 3α) is covered by exactly three tiles, each with its α-vertex. -/
theorem basebeta_vertex_apex (x y z : ℕ) (h1 : y + z = 0) (h2 : 2 * x + z = 3 * y + 6) :
    x = 3 ∧ y = 0 ∧ z = 0 :=
  vertex_apex x y z h1 h2

/-- Non-vacuity for vertex_pi: (1,1,1) satisfies y+z=2, 2x+z=3y. -/
theorem basebeta_vertex_pi_witness :
    (1 : ℕ) + 1 = 2 ∧ 2 * 1 + 1 = 3 * 1 := by norm_num

/-- Non-vacuity for vertex_beta_corner: (0,1,0) satisfies y+z=1, 2x+z+3=3y. -/
theorem basebeta_vertex_beta_corner_witness :
    (1 : ℕ) + 0 = 1 ∧ 2 * 0 + 0 + 3 = 3 * 1 := by norm_num

/-- Non-vacuity for vertex_apex: (3,0,0) satisfies y+z=0, 2x+z=3y+6. -/
theorem basebeta_vertex_apex_witness :
    (0 : ℕ) + 0 = 0 ∧ 2 * 3 + 0 = 3 * 0 + 6 := by norm_num

#print axioms basebeta_vertex_pi
#print axioms basebeta_vertex_beta_corner
#print axioms basebeta_vertex_apex

end Erdos634.Draft.BaseBetaE1Wrap

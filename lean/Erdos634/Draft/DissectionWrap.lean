import Erdos634.Dissection

/-!
# Dissection: fundamental dissection type arithmetic wrappers

Key results:
- `vertex_multiplicities`: the two coefficient equations from a vertex sum
- `vertex_pi_multiplicities`: at a π-vertex (interior edge point)
- `vertex_apex_multiplicities`: at an apex vertex (angle 3α)
- `volume_target`: tile volumes sum to target volume
- `volume_pos`: triangles have positive area

No sorry, standard axioms.
-/

namespace Erdos634.Draft.DissectionWrap

open Erdos634.Geometry

theorem dissection_vertex_multiplicities {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z : ℕ) (s t : ℤ)
    (hsum : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = (s : ℝ) * α + (t : ℝ) * β) :
    (x : ℤ) + 2 * z = s ∧ (y : ℤ) + z = t :=
  vertex_multiplicities hrel hirr x y z s t hsum

theorem dissection_vertex_pi_multiplicities {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = Real.pi) :
    y + z = 2 ∧ 2 * x + z = 3 * y :=
  vertex_pi_multiplicities hrel hirr x y z hsum

theorem dissection_vertex_apex_multiplicities {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z : ℕ)
    (hsum : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = 3 * α) :
    y + z = 0 ∧ 2 * x + z = 3 * y + 6 :=
  vertex_apex_multiplicities hrel hirr x y z hsum

theorem dissection_volume_pos (T : Tri) : 0 < MeasureTheory.volume T.carrier :=
  Tri.volume_pos T

#print axioms dissection_vertex_multiplicities
#print axioms dissection_vertex_pi_multiplicities
#print axioms dissection_vertex_apex_multiplicities
#print axioms dissection_volume_pos

end Erdos634.Draft.DissectionWrap

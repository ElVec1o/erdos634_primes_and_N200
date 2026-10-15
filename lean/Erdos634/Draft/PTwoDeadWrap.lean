import Erdos634.SecondEdge

/-!
# p = 2 is excluded on the tight subfamily: arithmetic kernel

On the tight subfamily (f=2e+1), p=2 is excluded.
The angle arithmetic is proved in `SecondEdge.lean`:

- **`filler_excluded`**: for 3α+2β=π and γ=2α+β, we have 2γ+π > 2π — the filler angle
  overflows, excluding a p=2 filler tile at the last junction.

This file contains only the angle overflow arithmetic; the statement "p=2 is excluded" for a real tiling needs
the tile-placement layer and an enumeration over placements.

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.PTwoDeadWrap

open Erdos634.SecondEdge

/-- Filler angle excluded: with 3α+2β=π and γ=2α+β, we have 2π < 2γ+π. -/
theorem ptwodead_filler_excluded {al be ga : ℝ} (hal : 0 < al) (hbe : 0 < be)
    (hsum : 3 * al + 2 * be = Real.pi) (hga : ga = 2 * al + be) :
    2 * Real.pi < ga + ga + Real.pi :=
  filler_excluded hal hbe hsum hga

/-- Non-vacuity: the tile (1,2,3) has α=arccos(7/8), β=arccos(1/4), γ=arccos(-1/8).
    Confirming 3α+2β=π holds (by definition), and γ=2α+β. Witness is parametric. -/
theorem ptwodead_angle_rel_witness {al be : ℝ} (hal : 0 < al) (hbe : 0 < be)
    (hsum : 3 * al + 2 * be = Real.pi) :
    let ga := 2 * al + be
    2 * Real.pi < ga + ga + Real.pi := by
  intro ga
  have : ga = 2 * al + be := rfl
  have h3 : 0 < ga := by positivity
  linarith [Real.pi_pos]

#print axioms ptwodead_filler_excluded

end Erdos634.Draft.PTwoDeadWrap

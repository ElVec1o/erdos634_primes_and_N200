/-
Draft/ChordAreaWitness.lean -- `ChordArea.chord_straddled` and `ChordArea.straddle_basebeta` on a real tiling.

The kernel-checked 44-tiling (`ApexWitness44.D44`: 44 copies of `(2,3,4)` in the triangle `(16,16,22)`, the member
`(1,2)` at scale `m = 2`) satisfies every hypothesis:

* `witness44_third`: ratio `1/3` from the apex (`44/9` is not an integer): some tile crosses the chord;
* `witness44_junction`: the base-β form at `(e, f, m) = (1, 2, 2)` with `M = 1` (the junction at distance `a` from
  the apex, ratio `1/8`): some tile crosses the chord.

So the chord-area statements are not vacuous.  Not a result on 634.  No sorry, no native_decide.
-/
import Erdos634.Draft.ChordArea
import Erdos634.Draft.ApexWitness44

namespace Erdos634.Draft.ChordAreaWitness

open Erdos634.Geometry Erdos634.Draft.ChordArea Erdos634.Draft.ApexWitness44

theorem len44 : Tiling44.tiles.length = 44 := by decide

/-- the chord at ratio `1/3` from the apex of the 44-tiling is crossed by a tile -/
theorem witness44_third :
    ∃ i, (∃ x ∈ (D44.tile i).carrier, D44.target.basis.coord 2 x < 1 - 1 / 3) ∧
      (∃ y ∈ (D44.tile i).carrier, 1 - 1 / 3 < D44.target.basis.coord 2 y) := by
  refine chord_straddled D44 2 (ρ := 1 / 3) (by norm_num) (by norm_num) (fun n h => ?_)
  rw [len44] at h
  have h2 : (n : ℝ) * 9 = 44 := by rw [h]; norm_num
  have h3 : n * 9 = 44 := by exact_mod_cast h2
  omega

/-- the base-β form at `(e, f, m) = (1, 2, 2)`, junction `M = 1` (ratio `1/8`) -/
theorem witness44_junction :
    ∃ i, (∃ x ∈ (D44.tile i).carrier, D44.target.basis.coord 2 x < 1 - 1 / 8) ∧
      (∃ y ∈ (D44.tile i).carrier, 1 - 1 / 8 < D44.target.basis.coord 2 y) :=
  straddle_basebeta D44 2 (e := 1) (f := 2) (m := 2) (M := 1) (ρ := 1 / 8) (by decide) (by norm_num)
    (by rw [len44]; norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)

end Erdos634.Draft.ChordAreaWitness

#print axioms Erdos634.Draft.ChordAreaWitness.witness44_junction

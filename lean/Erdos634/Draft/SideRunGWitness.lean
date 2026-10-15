/-
Draft/SideRunGWitness.lean  Part of `AllThreshold`.

The hypotheses of `SetupG` are satisfied by a real dissection, for `e = 1` and every `f ≥ 2`.

`SideRun.side_theorem_witness` (SideRun.lean) gives, for every `f ≥ 2`, a congruent dissection `D` (a normal form of the
seed tiling of `W_f(1, f)`) with `Setup D f (modelAlpha 1 f) (modelBeta 1 f) (2 α + β) L ax ay`; by
`SideRunGFrame.setupG_one_iff` it is a `SetupG D 1 f ...`.  This is `setupG_witness_one`.

For `e ≥ 2` the analogous witness is the normal form (isometry putting the side `QB` on the `x`-axis, relabelling of the
model so that its opposite sides are `(e f, f² − e², f²)`) of

  * the seed tiling of `W_f(e, f)`, which exists for every member (`CollarG.wTilable_seed e f`, `WSeedG.w_seed`), or
  * the kernel-checked tiling of `W_4(2, 3)` by 224 tiles `(6, 5, 9)` (`Draft/W23.lean`, `w23_scale4`);

the passage from a `CongruentDissection` with `HasSides` on target and model to a `SetupG` is `setup_of_sides` for
general `e` (the analogue of `SideRunMain.setup_of_sides`, which uses `E1NormalForm.normalFormC` with the model triangle
`modelTri n`); it is carried out in `SideRunGMain`.  For every member `1 ≤ e < f` the angle bundle `hA` is satisfiable
(`SideRunGFrame.angleData_model`) and `TileOK` holds for coprime `e < f` (`tileOK_of_nat`).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRun
import Erdos634.Draft.SideRunGFrame

namespace Erdos634.Draft.SideRunG

open Erdos634.Geometry Erdos634.BaseBetaTargetCoord Erdos634.Draft.SideRun

/-- **A real dissection satisfies the hypotheses of `SetupG` at `e = 1`.** -/
theorem setupG_witness_one (f : ℕ) (hf : 2 ≤ f) :
    ∃ (N : ℕ) (D : CongruentDissection N) (L ax ay : ℝ),
      SetupG D 1 f (modelAlpha 1 f) (modelBeta 1 f) (2 * modelAlpha 1 f + modelBeta 1 f) L ax ay := by
  obtain ⟨N, D, L, ax, ay, S, -⟩ := side_theorem_witness f hf
  exact ⟨N, D, L, ax, ay, setupG_one_iff.mpr S⟩

end Erdos634.Draft.SideRunG

#print axioms Erdos634.Draft.SideRunG.setupG_witness_one

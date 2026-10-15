/-
Draft/W23.lean: the member `(2, 3)`: the triangle `W_4` and the base-β target `T_4(2, 3)` have tilings, and with
them the base-β target of `(2, 3)` has a tiling at every scale `M ≥ 3`.

    theorem w23_scale4 : ∃ D : CongruentDissection 224, HasSides D.target 112 108 60 ∧ HasSides D.model 6 5 9
    theorem wTilable_2_3_4 : WTilable 2 3 4
    theorem betaTilable_2_3_4 : BetaTilable 2 3 4          -- legs 108, base 184, 368 tiles
    theorem betaTilable_2_3_ge : ∀ M, 3 ≤ M → BetaTilable 2 3 M

The scale `4` is the only scale `M ≥ 3` of this member that the collar (`Draft.CollarG`) does not reach from the seed
(`4 ∉ 3 + ⟨2, 3⟩`).  The tiling of `W_4 = (60, 112, 108)` by `224` copies of `(6, 5, 9)` was found by an exact search
(`rust/mrv2`, tiles placed at the lowest uncovered point), has coordinates in
`ℤ[√2]/81`, was verified exactly and is checked here by the Lean kernel
(`R224Tiling`).  The beta lift (`CollarG.betaTilable_of_wTilable`) gives `T_4(2, 3)`.

Prior art: D. Paliy has a tiling of `W` and of the beta target for the tile `(6, 5, 9)` at every scale
`m ≥ 3`, with a 224-tile seed and a fixed-shape 368-tile extension, and notes that the 368-tiling was already known from a
construction of M. Beeson.  So a 224-tiling of `W_4`, the 368-tiling of `T_4(2, 3)` and the existence of tilings at every
scale `M ≥ 3` are due to them.  The tiling certified here was found independently and has not been compared with his seed.
What is added here is the check of one explicit 224-tiling by the Lean kernel, a Lean proof for every `M ≥ 3` (through
`Draft.CollarG`), and with the two exclusions at `M = 1, 2` the statement "if and only if `M ≥ 3`"
(`UniformThresholdCert.threshold_2_3`).
No sorry, no native_decide.
-/
import Erdos634.R224TilingBridge
import Erdos634.Draft.W13
import Erdos634.Draft.CollarG

open scoped Classical
open Erdos634.Geometry

namespace Erdos634.Draft.W23
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap)
open Erdos634.Draft.UniformThreshold (BetaTilable hasSides_congr)
open Erdos634.Draft.CollarG (WTilable betaTilable_of_wTilable betaTilable_2_3)

/-- **`W` of the member `(2, 3)` at scale `4`**: the triangle `(60, 112, 108)` is cut into `224` copies of
`(6, 5, 9)`. -/
theorem w23_scale4 : ∃ D : CongruentDissection 224, HasSides D.target 112 108 60 ∧ HasSides D.model 6 5 9 := by
  obtain ⟨D, t1, t2, t3, m1, m2, m3⟩ := Erdos634.R224TilingBridge.r224_dissection_shape
  exact Erdos634.Draft.W13.hasSides_of_sq D 81 60 112 108 9 6 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [t1]; norm_num) (by rw [t2]; norm_num)
    (by rw [t3]; norm_num) (by rw [m1]; norm_num) (by rw [m2]; norm_num) (by rw [m3]; norm_num)

/-- the same in the form of `CollarG.WTilable` -/
theorem wTilable_2_3_4 : WTilable 2 3 4 := by
  obtain ⟨D, hT, hM⟩ := w23_scale4
  exact ⟨D, hasSides_congr (hasSides_rot (hasSides_rot hT)) (by norm_num) (by norm_num) (by norm_num),
    hasSides_congr hM (by norm_num) (by norm_num) (by norm_num)⟩

/-- **The base-β target of the member `(2, 3)` at scale `4`** (legs `108`, base `184`) has a tiling. -/
theorem betaTilable_2_3_4 : BetaTilable 2 3 4 :=
  betaTilable_of_wTilable 2 1 4 (by norm_num) (by norm_num) (by norm_num) wTilable_2_3_4

/-- **The base-β target of the member `(2, 3)` has a tiling at every scale `M ≥ 3`.** -/
theorem betaTilable_2_3_ge (M : ℕ) (hM : 3 ≤ M) : BetaTilable 2 3 M := by
  by_cases h4 : M = 4
  · rw [h4]; exact betaTilable_2_3_4
  · exact betaTilable_2_3 M hM h4

end Erdos634.Draft.W23

#print axioms Erdos634.Draft.W23.w23_scale4
#print axioms Erdos634.Draft.W23.betaTilable_2_3_4
#print axioms Erdos634.Draft.W23.betaTilable_2_3_ge

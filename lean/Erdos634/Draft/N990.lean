/-
Draft/N990.lean -- `990` is a tile count (kernel check of a construction of D. Paliy).

`R990TilingBridge.r990_dissection_shape` (kernel-checked certificate `R990Tiling`, coordinates in `ℤ[√3]`, scale
`338`): the triangle with sides `57122, 106470, 96668` = `338 · (169, 315, 286)` is cut into `990` congruent triangles with sides `2366, 2704, 4394` =
`338 · (7, 8, 13)`.

The construction is D. Paliy's (`github.com/DenisUkranian/erdos-634-tilings`, commit 94566090, file
`research/group2-nested-corners/f3-990.json`; unrefereed).  It was converted to exact coordinates and verified exactly,
and the Lean files are generated from the exact data.  This file contains the kernel check.

Composite-N statement.  No sorry, no native_decide.
-/
import Erdos634.R990TilingBridge
import Erdos634.Draft.TileCountFamilies

namespace Erdos634.Draft.N990

open Erdos634.Geometry Erdos634.Draft.TileCountFamilies

/-- **990 is a tile count** (construction due to D. Paliy, github.com/DenisUkranian/erdos-634-tilings, commit
94566090; kernel-checked here). -/
theorem tileCount_990 : TileCount 990 := Erdos634.R990TilingBridge.r990_nonempty_congruentDissection

/-- `990 k²` is a tile count for every `k ≥ 1` (scaling of D. Paliy's tiling). -/
theorem tileCount_990_sq {k : ℕ} (hk : 0 < k) : TileCount (k * k * 990) := tileCount_scale tileCount_990 hk

theorem eq_of_sq {d c : ℝ} (hd : 0 ≤ d) (hc : 0 < c) (h : d ^ 2 = c ^ 2) : d = c := by
  have h2 : (d - c) * (d + c) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linarith
  · linarith

/-- **D. Paliy's 990-tiling with its side lengths** (scale `338`): target sides `57122, 106470, 96668`, tile sides
`2366, 2704, 4394`. -/
theorem dissection_990_sides :
    ∃ D : CongruentDissection 990,
      dist (D.target.pts 0) (D.target.pts 1) = 57122 ∧ dist (D.target.pts 1) (D.target.pts 2) = 106470 ∧
      dist (D.target.pts 2) (D.target.pts 0) = 96668 ∧
      dist (D.model.pts 0) (D.model.pts 1) = 2366 ∧ dist (D.model.pts 1) (D.model.pts 2) = 2704 ∧
      dist (D.model.pts 2) (D.model.pts 0) = 4394 := by
  obtain ⟨D, t1, t2, t3, m1, m2, m3⟩ := Erdos634.R990TilingBridge.r990_dissection_shape
  exact ⟨D, eq_of_sq dist_nonneg (by norm_num) (by rw [t1]; norm_num),
    eq_of_sq dist_nonneg (by norm_num) (by rw [t2]; norm_num),
    eq_of_sq dist_nonneg (by norm_num) (by rw [t3]; norm_num),
    eq_of_sq dist_nonneg (by norm_num) (by rw [m1]; norm_num),
    eq_of_sq dist_nonneg (by norm_num) (by rw [m2]; norm_num),
    eq_of_sq dist_nonneg (by norm_num) (by rw [m3]; norm_num)⟩

end Erdos634.Draft.N990

#print axioms Erdos634.Draft.N990.tileCount_990
#print axioms Erdos634.Draft.N990.tileCount_990_sq
#print axioms Erdos634.Draft.N990.dissection_990_sides

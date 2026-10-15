/-
Draft/N897.lean -- `897` is a tile count (kernel check of a construction of D. Paliy).

`R897TilingBridge.r897_dissection_shape` (kernel-checked certificate `R897Tiling`, coordinates in `ℤ[√55]`, scale
`32`): the triangle with sides `8736, 11776, 8192` = `32 · (273, 368, 256)` is cut into `897` congruent triangles with sides `224, 512, 384` =
`32 · (7, 16, 12)`.

The construction is D. Paliy's (`github.com/DenisUkranian/erdos-634-tilings`, commit 94566090, file
`data/tiling-897.json`; unrefereed).  It was converted to exact coordinates and verified exactly, and the Lean files
are generated from the exact data.  This file contains the kernel check.

Composite-N statement.  No sorry, no native_decide.
-/
import Erdos634.R897TilingBridge
import Erdos634.Draft.TileCountFamilies

namespace Erdos634.Draft.N897

open Erdos634.Geometry Erdos634.Draft.TileCountFamilies

/-- **897 is a tile count** (construction due to D. Paliy, github.com/DenisUkranian/erdos-634-tilings, commit
94566090; kernel-checked here). -/
theorem tileCount_897 : TileCount 897 := Erdos634.R897TilingBridge.r897_nonempty_congruentDissection

/-- `897 k²` is a tile count for every `k ≥ 1` (scaling of D. Paliy's tiling). -/
theorem tileCount_897_sq {k : ℕ} (hk : 0 < k) : TileCount (k * k * 897) := tileCount_scale tileCount_897 hk

theorem eq_of_sq {d c : ℝ} (hd : 0 ≤ d) (hc : 0 < c) (h : d ^ 2 = c ^ 2) : d = c := by
  have h2 : (d - c) * (d + c) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linarith
  · linarith

/-- **D. Paliy's 897-tiling with its side lengths** (scale `32`): target sides `8736, 11776, 8192`, tile sides
`224, 512, 384`. -/
theorem dissection_897_sides :
    ∃ D : CongruentDissection 897,
      dist (D.target.pts 0) (D.target.pts 1) = 8736 ∧ dist (D.target.pts 1) (D.target.pts 2) = 11776 ∧
      dist (D.target.pts 2) (D.target.pts 0) = 8192 ∧
      dist (D.model.pts 0) (D.model.pts 1) = 224 ∧ dist (D.model.pts 1) (D.model.pts 2) = 512 ∧
      dist (D.model.pts 2) (D.model.pts 0) = 384 := by
  obtain ⟨D, t1, t2, t3, m1, m2, m3⟩ := Erdos634.R897TilingBridge.r897_dissection_shape
  exact ⟨D, eq_of_sq dist_nonneg (by norm_num) (by rw [t1]; norm_num),
    eq_of_sq dist_nonneg (by norm_num) (by rw [t2]; norm_num),
    eq_of_sq dist_nonneg (by norm_num) (by rw [t3]; norm_num),
    eq_of_sq dist_nonneg (by norm_num) (by rw [m1]; norm_num),
    eq_of_sq dist_nonneg (by norm_num) (by rw [m2]; norm_num),
    eq_of_sq dist_nonneg (by norm_num) (by rw [m3]; norm_num)⟩

end Erdos634.Draft.N897

#print axioms Erdos634.Draft.N897.tileCount_897
#print axioms Erdos634.Draft.N897.tileCount_897_sq
#print axioms Erdos634.Draft.N897.dissection_897_sides

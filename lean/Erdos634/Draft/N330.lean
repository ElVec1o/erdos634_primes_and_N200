/-
Draft/N330.lean -- `330` is a tile count (kernel check).

`R330TilingBridge.r330_dissection_shape` (kernel-checked certificate `R330Tiling`, coordinates in `ℤ[√3]`, scale
`338`): the triangle with sides `30758, 59488, 65910` = `338 · (91, 176, 195)` is cut into `330` congruent triangles with
sides `4394, 2704, 2366` = `338 · (13, 8, 7)` (the tile `(7, 8, 13)`, angle `2π/3` opposite `13`).

The tiling was found by the floating-point search `rust/mrv2` (lex order), converted to exact coordinates and verified
exactly; the Lean files are generated from the exact data.  Prior art: D. Paliy's ledger announces the
F4 construction for `a < b` at every multiplier, which includes this target (unrefereed; no tiling data of his for
`330` is available).  This file contains the explicit tiling and its kernel check.

Composite-N statement.  No sorry, no native_decide.
-/
import Erdos634.R330TilingBridge
import Erdos634.Draft.TileCountFamilies

namespace Erdos634.Draft.N330

open Erdos634.Geometry Erdos634.Draft.TileCountFamilies

/-- **330 is a tile count** (kernel-checked). -/
theorem tileCount_330 : TileCount 330 := Erdos634.R330TilingBridge.r330_nonempty_congruentDissection

/-- `330 k²` is a tile count for every `k ≥ 1`. -/
theorem tileCount_330_sq {k : ℕ} (hk : 0 < k) : TileCount (k * k * 330) := tileCount_scale tileCount_330 hk

theorem eq_of_sq {d c : ℝ} (hd : 0 ≤ d) (hc : 0 < c) (h : d ^ 2 = c ^ 2) : d = c := by
  have h2 : (d - c) * (d + c) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linarith
  · linarith

/-- **The 330-tiling with its side lengths** (scale `338`): target sides `30758, 59488, 65910`, tile sides
`4394, 2704, 2366`. -/
theorem dissection_330_sides :
    ∃ D : CongruentDissection 330,
      dist (D.target.pts 0) (D.target.pts 1) = 30758 ∧ dist (D.target.pts 1) (D.target.pts 2) = 59488 ∧
      dist (D.target.pts 2) (D.target.pts 0) = 65910 ∧
      dist (D.model.pts 0) (D.model.pts 1) = 4394 ∧ dist (D.model.pts 1) (D.model.pts 2) = 2704 ∧
      dist (D.model.pts 2) (D.model.pts 0) = 2366 := by
  obtain ⟨D, t1, t2, t3, m1, m2, m3⟩ := Erdos634.R330TilingBridge.r330_dissection_shape
  exact ⟨D, eq_of_sq dist_nonneg (by norm_num) (by rw [t1]; norm_num),
    eq_of_sq dist_nonneg (by norm_num) (by rw [t2]; norm_num),
    eq_of_sq dist_nonneg (by norm_num) (by rw [t3]; norm_num),
    eq_of_sq dist_nonneg (by norm_num) (by rw [m1]; norm_num),
    eq_of_sq dist_nonneg (by norm_num) (by rw [m2]; norm_num),
    eq_of_sq dist_nonneg (by norm_num) (by rw [m3]; norm_num)⟩

end Erdos634.Draft.N330

#print axioms Erdos634.Draft.N330.tileCount_330
#print axioms Erdos634.Draft.N330.tileCount_330_sq
#print axioms Erdos634.Draft.N330.dissection_330_sides

/-
Draft/N264.lean -- `264` is a tile count.

`R264TilingBridge.r264_dissection_shape` (kernel-checked certificate `R264Tiling`, coordinates in `ℤ[√3]`): the triangle
with sides `4802, 7546, 7056 = 98 · (49, 77, 72)` is cut into `264` congruent triangles with sides `294, 490, 686 =
98 · (3, 5, 7)`.  The target is the triangle with angles `(β, 2β, 3α)` of the tile `(3, 5, 7)` (shape `F₃`), and
`264 = 3 (a + b)(2a + b)` is the least value the area count allows on that shape.

A tiling of `(49, 77, 72)` by `264` copies of `(5, 3, 7)` is in D. Paliy's claim ledger
(`github.com/DenisUkranian/erdos-634-tilings`, entry "N=264 is admissible", October 2026, unrefereed).  The tiling
certified here was found by the floating-point search `rust/mrv2` (order `lex`), snapped to `ℚ(√3)` and
verified exactly; the Lean files are generated from the exact data.  This file contains the kernel check.

Composite-N statement.  No sorry, no native_decide.
-/
import Erdos634.R264TilingBridge
import Erdos634.Draft.TileCountFamilies

namespace Erdos634.Draft.N264

open Erdos634.Geometry Erdos634.Draft.TileCountFamilies

/-- **264 is a tile count** (result due to D. Paliy; kernel-checked here). -/
theorem tileCount_264 : TileCount 264 := Erdos634.R264TilingBridge.r264_nonempty_congruentDissection

/-- `264 k²` is a tile count for every `k ≥ 1`. -/
theorem tileCount_264_sq {k : ℕ} (hk : 0 < k) : TileCount (k * k * 264) := tileCount_scale tileCount_264 hk

end Erdos634.Draft.N264

#print axioms Erdos634.Draft.N264.tileCount_264

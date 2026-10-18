/-
Draft/N345N506.lean -- `345` and `506` are tile counts (kernel check).

`R345TilingBridge.r345_dissection_shape` / `R506TilingBridge.r506_dissection_shape` (kernel-checked certificates
`R345Tiling` (scale 26) and `R506Tiling` (scale 338), coordinates in `ℤ[√3]`): with the tile `(7, 8, 13)` (angle `2π/3`
opposite `13`),
  * the triangle with sides `26 · (104, 161, 195)` is cut into `345 = (2·8+7)(8+7)` congruent triangles (F4 with `a > b`,
    "reversed F4", `a = 8, b = 7`);
  * the triangle with sides `338 · (161, 169, 176)` is cut into `506 = (8+2·7)(2·8+7)` congruent triangles (F2).

Both layouts are **D. Paliy's nested-corner construction** (unrefereed ledger; precondition `a > b`, `b c - a² ∈ ⟨a,b,c⟩`),
decoded in `the row decoder of the project` (`F4_rev`, `F2_`), made exact there, re-verified with `rust/bonfioli_tiling_engine
bte verify` (`data/witnesses/tiling_345_7_8_13_f4rev_paliy.exact.txt`, `..._506_..._f2_paliy.exact.txt`) and turned into Lean
by `code/analysis/gen_tiling_lean.py`. The credit for the layout is Paliy's; the exact instance and the kernel check are ours.
The symbolic family theorem (every tile satisfying the precondition) is NOT formalized: see PAPER_MAP.

Composite-N statement; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.R345TilingBridge
import Erdos634.R506TilingBridge
import Erdos634.Draft.TileCountFamilies

namespace Erdos634.Draft.N345N506

open Erdos634.Geometry Erdos634.Draft.TileCountFamilies

/-- **345 is a tile count** (kernel-checked; reversed F4 of `(8,7,13)`). -/
theorem tileCount_345 : TileCount 345 := Erdos634.R345TilingBridge.r345_nonempty_congruentDissection

/-- **506 is a tile count** (kernel-checked; F2 of `(8,7,13)`). -/
theorem tileCount_506 : TileCount 506 := Erdos634.R506TilingBridge.r506_nonempty_congruentDissection

theorem tileCount_345_sq {k : ℕ} (hk : 0 < k) : TileCount (k * k * 345) := tileCount_scale tileCount_345 hk
theorem tileCount_506_sq {k : ℕ} (hk : 0 < k) : TileCount (k * k * 506) := tileCount_scale tileCount_506 hk

end Erdos634.Draft.N345N506

#print axioms Erdos634.Draft.N345N506.tileCount_345
#print axioms Erdos634.Draft.N345N506.tileCount_506

/-
Draft/TemplateSquares.lean -- twelve census values that are tile counts by subdividing a template tiling.

Each value is `k² · N₀` with `N₀` one of the template tile counts of `AllTemplates` (found by our template engine `bto`,
2026-10-19), so it follows from `tileCount_scale` (subdivide every tile of the `N₀`-tiling into `k²` congruent copies).
The census of 2026-10-19 listed them as undecided because square closure had not been applied to the template rows
(found by the Conjecture C consistency check, `(project working notes)`).

Composite-N statements; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.T11625
import Erdos634.Draft.T66960
import Erdos634.Draft.T119040
import Erdos634.Draft.T121765
import Erdos634.Draft.T167865
import Erdos634.Draft.T186000

namespace Erdos634.Draft.TemplateSquares

open Erdos634.Draft.TileCountFamilies

theorem tileCount_46500 : TileCount 46500 := tileCount_scale T11625.tileCount_11625 (k := 2) (by norm_num)
theorem tileCount_104625 : TileCount 104625 := tileCount_scale T11625.tileCount_11625 (k := 3) (by norm_num)
theorem tileCount_290625 : TileCount 290625 := tileCount_scale T11625.tileCount_11625 (k := 5) (by norm_num)
theorem tileCount_418500 : TileCount 418500 := tileCount_scale T11625.tileCount_11625 (k := 6) (by norm_num)
theorem tileCount_569625 : TileCount 569625 := tileCount_scale T11625.tileCount_11625 (k := 7) (by norm_num)
theorem tileCount_941625 : TileCount 941625 := tileCount_scale T11625.tileCount_11625 (k := 9) (by norm_num)
theorem tileCount_267840 : TileCount 267840 := tileCount_scale T66960.tileCount_66960 (k := 2) (by norm_num)
theorem tileCount_602640 : TileCount 602640 := tileCount_scale T66960.tileCount_66960 (k := 3) (by norm_num)
theorem tileCount_476160 : TileCount 476160 := tileCount_scale T119040.tileCount_119040 (k := 2) (by norm_num)
theorem tileCount_487060 : TileCount 487060 := tileCount_scale T121765.tileCount_121765 (k := 2) (by norm_num)
theorem tileCount_671460 : TileCount 671460 := tileCount_scale T167865.tileCount_167865 (k := 2) (by norm_num)
theorem tileCount_744000 : TileCount 744000 := tileCount_scale T186000.tileCount_186000 (k := 2) (by norm_num)

end Erdos634.Draft.TemplateSquares

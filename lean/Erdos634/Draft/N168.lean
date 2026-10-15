/-
Draft/N168.lean -- `N = 168` is NOT a tile count.

Every leaf of the non-squarefree chain except the `π/3` equilateral leaf holds for `168` by kernel-checked arithmetic
(`E60Reduce.not_tile_of_e60`).  The `π/3` leaf `GapE60 168` is `E60N168.gapE60_168`: the pair table leaves two pairs, each
refuted by a certificate over `ℤ[√K]` with Galois-conjugate kills.

Composite-N result.  NOT prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.E60N168
import Erdos634.Draft.E60Reduce

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.N168

open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2 Erdos634.Draft.NSQMain Erdos634.Draft.NSQM
open Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs Erdos634.Draft.NSQS1 Erdos634.Draft.NSQRW Erdos634.Draft.NSQRA
open Erdos634.Draft.R8ZF Erdos634.Draft.E60Reduce

/-- **`168` is not a tile count** (no `CongruentDissection 168` exists). -/
theorem not_tile_168 (D : CongruentDissection 168) : False :=
  not_tile_of_e60 168 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) Erdos634.Draft.E60N168.gapE60_168 D

end Erdos634.Draft.N168

#print axioms Erdos634.Draft.N168.not_tile_168

/-
Draft/N132Final.lean -- `N = 132` is NOT a tile count.

`132 = 4 · 33`.  `OpenRed.not_tile_132_of` reduced `132` to one instance: the tile `(5, 3, 7)` on the isosceles
triangle with legs `42` and base `66`.  It is closed here by the kernel-checked certificate
`Refl.MISO132.not_dissection` (exact replay over `ℚ(√3)` of a search tree found with the target in the orientation
leg, base, leg).

    theorem not_tile_132 (D : CongruentDissection 132) : False
    theorem not_tileCount_132 : ¬ TileCount 132

Composite-N result.  NOT prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.OpenReductionsNsq
import Erdos634.Draft.InstLbl
import Erdos634.Refl.MISO132Sound

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.N132F

open Erdos634.Geometry Erdos634.CertNode Erdos634.CertCoord Erdos634.Draft.OpenRed
open Erdos634.Draft.TileCountFamilies Erdos634.Draft.InstLbl Erdos634.Draft.IsoInst Erdos634.Draft.NSQRW

theorem TGT_ISO132 : dist (Refl.MISO132.TGT.pts 0) (Refl.MISO132.TGT.pts 1) = 42 ∧
    dist (Refl.MISO132.TGT.pts 1) (Refl.MISO132.TGT.pts 2) = 66 ∧
    dist (Refl.MISO132.TGT.pts 0) (Refl.MISO132.TGT.pts 2) = 42 :=
  model_sides_rp Refl.MISO132.hDn Refl.MISO132.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- Iso `(a₀, b₀, c₀, k) = (5, 3, 7, 6)`: tile `(5, 3, 7)`, legs `42`, base `66`. -/
theorem isoinst_5_3_7_6 : IsoInst 5 3 7 6 :=
  isoinst_of_cert_lbl 5 3 7 6 Refl.MISO132.TGT Refl.MISO132.MODEL
    ⟨by rw [TGT_ISO132.1]; norm_num, by rw [TGT_ISO132.2.1]; norm_num, by rw [TGT_ISO132.2.2]; norm_num⟩
    ⟨by rw [Refl.MISO132.MODEL_sides.1]; norm_num, by rw [Refl.MISO132.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MISO132.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MISO132.not_dissection D hT hM)

/-- **`132` is not a tile count.** -/
theorem not_tile_132 (D : CongruentDissection 132) : False :=
  not_tile_132_of (@isoinst_5_3_7_6) D


theorem not_tileCount_132 : ¬ TileCount 132 :=
  fun ⟨D⟩ => not_tile_132 D

end Erdos634.Draft.N132F

#print axioms Erdos634.Draft.N132F.not_tile_132

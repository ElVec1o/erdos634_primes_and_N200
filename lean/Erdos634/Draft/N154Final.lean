/-
Draft/N154Final.lean -- `N = 154` is NOT a tile count.

`154 = 7 · 22`.  `OpenRed.not_tile_154_of` reduced `154` to one instance: the tile `(8, 7, 13)` on the isosceles
triangle with legs `91` and base `154`.  It is closed here by the kernel-checked certificate
`Refl.MISO154.not_dissection` (exact replay over `ℚ(√3)` of a search tree found with the target in the orientation
leg, base, leg).

    theorem not_tile_154 (D : CongruentDissection 154) : False
    theorem not_tileCount_154 : ¬ TileCount 154

Composite-N result.  NOT prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.OpenReductions
import Erdos634.Draft.InstLbl
import Erdos634.Refl.MISO154Sound

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.N154F

open Erdos634.Geometry Erdos634.CertNode Erdos634.CertCoord Erdos634.Draft.OpenRed
open Erdos634.Draft.TileCountFamilies Erdos634.Draft.InstLbl Erdos634.Draft.IsoInst Erdos634.Draft.NSQRW

theorem TGT_ISO154 : dist (Refl.MISO154.TGT.pts 0) (Refl.MISO154.TGT.pts 1) = 91 ∧
    dist (Refl.MISO154.TGT.pts 1) (Refl.MISO154.TGT.pts 2) = 154 ∧
    dist (Refl.MISO154.TGT.pts 0) (Refl.MISO154.TGT.pts 2) = 91 :=
  model_sides_rp Refl.MISO154.hDn Refl.MISO154.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- Iso `(a₀, b₀, c₀, k) = (8, 7, 13, 7)`: tile `(8, 7, 13)`, legs `91`, base `154`. -/
theorem isoinst_8_7_13_7 : IsoInst 8 7 13 7 :=
  isoinst_of_cert_lbl 8 7 13 7 Refl.MISO154.TGT Refl.MISO154.MODEL
    ⟨by rw [TGT_ISO154.1]; norm_num, by rw [TGT_ISO154.2.1]; norm_num, by rw [TGT_ISO154.2.2]; norm_num⟩
    ⟨by rw [Refl.MISO154.MODEL_sides.1]; norm_num, by rw [Refl.MISO154.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MISO154.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MISO154.not_dissection D hT hM)

/-- **`154` is not a tile count.** -/
theorem not_tile_154 (D : CongruentDissection 154) : False :=
  not_tile_154_of (@isoinst_8_7_13_7) D


theorem not_tileCount_154 : ¬ TileCount 154 :=
  fun ⟨D⟩ => not_tile_154 D

end Erdos634.Draft.N154F

#print axioms Erdos634.Draft.N154F.not_tile_154

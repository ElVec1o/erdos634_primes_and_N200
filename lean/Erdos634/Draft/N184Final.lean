/-
Draft/N184Final.lean -- `N = 184` is NOT a tile count.

`184 = 8 · 23`.  `OpenRed.not_tile_184_of` reduced `184` to two instances: the tile `(7, 8, 13)` on the isosceles
triangle with legs `104` and base `184`, and the tile `(10, 21, 25)` on the triangle `(184, 210, 250)`.  They are
closed here by the kernel-checked certificates `Refl.MISO184.not_dissection` and `Refl.MS4N184.not_dissection`.

    theorem not_tile_184 (D : CongruentDissection 184) : False
    theorem not_tileCount_184 : ¬ TileCount 184

Composite-N result.  NOT prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.OpenReductionsNsq
import Erdos634.Draft.InstLbl
import Erdos634.Refl.MISO184Sound
import Erdos634.Refl.MS4N184Sound

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.N184F

open Erdos634.Geometry Erdos634.CertNode Erdos634.CertCoord Erdos634.Draft.OpenRed
open Erdos634.Draft.TileCountFamilies Erdos634.Draft.InstLbl Erdos634.Draft.IsoInst Erdos634.Draft.NSQRW

theorem TGT_ISO184 : dist (Refl.MISO184.TGT.pts 0) (Refl.MISO184.TGT.pts 1) = 104 ∧
    dist (Refl.MISO184.TGT.pts 1) (Refl.MISO184.TGT.pts 2) = 184 ∧
    dist (Refl.MISO184.TGT.pts 0) (Refl.MISO184.TGT.pts 2) = 104 :=
  model_sides_rp Refl.MISO184.hDn Refl.MISO184.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- Iso `(a₀, b₀, c₀, k) = (7, 8, 13, 8)`: tile `(7, 8, 13)`, legs `104`, base `184`. -/
theorem isoinst_7_8_13_8 : IsoInst 7 8 13 8 :=
  isoinst_of_cert_lbl 7 8 13 8 Refl.MISO184.TGT Refl.MISO184.MODEL
    ⟨by rw [TGT_ISO184.1]; norm_num, by rw [TGT_ISO184.2.1]; norm_num, by rw [TGT_ISO184.2.2]; norm_num⟩
    ⟨by rw [Refl.MISO184.MODEL_sides.1]; norm_num, by rw [Refl.MISO184.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MISO184.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MISO184.not_dissection D hT hM)

theorem TGT_S4N184 : dist (Refl.MS4N184.TGT.pts 0) (Refl.MS4N184.TGT.pts 1) = 184 ∧
    dist (Refl.MS4N184.TGT.pts 1) (Refl.MS4N184.TGT.pts 2) = 210 ∧
    dist (Refl.MS4N184.TGT.pts 0) (Refl.MS4N184.TGT.pts 2) = 250 :=
  model_sides_rp Refl.MS4N184.hDn Refl.MS4N184.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- S4 `(S', e, f) = (2, 2, 5)`: tile `(10, 21, 25)`, target `(184, 210, 250)`. -/
theorem s4inst_2_2_5 : S4Inst 2 2 5 :=
  s4inst_of_cert_lbl 2 2 5 Refl.MS4N184.TGT Refl.MS4N184.MODEL
    ⟨by rw [TGT_S4N184.1]; norm_num, by rw [TGT_S4N184.2.1]; norm_num, by rw [TGT_S4N184.2.2]; norm_num⟩
    ⟨by rw [Refl.MS4N184.MODEL_sides.1]; norm_num, by rw [Refl.MS4N184.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MS4N184.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MS4N184.not_dissection D hT hM)

/-- **`184` is not a tile count.** -/
theorem not_tile_184 (D : CongruentDissection 184) : False :=
  not_tile_184_of (@isoinst_7_8_13_8) (@s4inst_2_2_5) D


theorem not_tileCount_184 : ¬ TileCount 184 :=
  fun ⟨D⟩ => not_tile_184 D

end Erdos634.Draft.N184F

#print axioms Erdos634.Draft.N184F.not_tile_184

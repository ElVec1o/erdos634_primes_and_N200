/-
Draft/N161Final.lean -- `N = 161` is NOT a tile count.

`161 = 7 · 23`.  `OpenRed.not_tile_161_of` reduced `161` to one instance: the base-α target of the member
`(3, 4)`, tile `(12, 7, 16)` on the isosceles triangle with legs `112` and base `161`.  It is closed here by the
kernel-checked certificate `Refl.MS3N161.not_dissection` (exact replay of a search tree found with the target in
the orientation leg, base, leg).

    theorem not_tile_161 (D : CongruentDissection 161) : False
    theorem not_tileCount_161 : ¬ TileCount 161

Composite-N result.  NOT prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.OpenReductions
import Erdos634.Draft.InstLbl
import Erdos634.Refl.MS3N161Sound

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.N161F

open Erdos634.Geometry Erdos634.CertNode Erdos634.CertCoord Erdos634.Draft.OpenRed
open Erdos634.Draft.TileCountFamilies Erdos634.Draft.InstLbl Erdos634.Draft.IsoInst Erdos634.Draft.NSQRW

theorem TGT_S3N161 : dist (Refl.MS3N161.TGT.pts 0) (Refl.MS3N161.TGT.pts 1) = 112 ∧
    dist (Refl.MS3N161.TGT.pts 1) (Refl.MS3N161.TGT.pts 2) = 161 ∧
    dist (Refl.MS3N161.TGT.pts 0) (Refl.MS3N161.TGT.pts 2) = 112 :=
  model_sides_rp Refl.MS3N161.hDn Refl.MS3N161.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- S3 `(m, e, f) = (1, 3, 4)`: tile `(12, 7, 16)`, legs `112`, base `161`. -/
theorem s3inst_1_3_4 : S3Inst 1 3 4 :=
  s3inst_of_cert_lbl 1 3 4 Refl.MS3N161.TGT Refl.MS3N161.MODEL
    ⟨by rw [TGT_S3N161.1]; norm_num, by rw [TGT_S3N161.2.1]; norm_num, by rw [TGT_S3N161.2.2]; norm_num⟩
    ⟨by rw [Refl.MS3N161.MODEL_sides.1]; norm_num, by rw [Refl.MS3N161.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MS3N161.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MS3N161.not_dissection D hT hM)

/-- **`161` is not a tile count.** -/
theorem not_tile_161 (D : CongruentDissection 161) : False :=
  not_tile_161_of (@s3inst_1_3_4) D


theorem not_tileCount_161 : ¬ TileCount 161 :=
  fun ⟨D⟩ => not_tile_161 D

end Erdos634.Draft.N161F

#print axioms Erdos634.Draft.N161F.not_tile_161

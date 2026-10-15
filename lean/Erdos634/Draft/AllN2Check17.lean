/- AllN2Check17: N = 543, 553, 573, 579, 581
   Squarefree exclusions via C' with sqrt-bounded checks (Wave-2 OOM fix). -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c543_sqf   : LeafSqf 543   := by decide +kernel
private theorem c543_range : LeafRange 543  := by decide +kernel
private theorem c543_ell   : LeafEll 543    := by decide +kernel
private theorem c543_nsq   : NSqChkSq 543   := by decide +kernel
private theorem c543_har   : HArithChkSq 543 := by decide +kernel
private theorem c543_r     : LeafR 543      := by decide +kernel
private theorem c543_e'    : LeafE' 543     := by decide +kernel
private theorem c543_f1    : LeafF1 543     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c543_s2    : S2ChkSq 543    := by decide +kernel
private theorem c543_s3    : S3ChkSq 543    := by decide +kernel
private theorem c543_iso   : LeafIso 543    := by decide +kernel
private theorem c543_nof2  : NoF2ChkSq 543  := by decide +kernel
private theorem c543_nof3  : NoF3ChkSq 543  := by decide +kernel
private theorem c543_nof4z : NoF4zChkSq 543 := by decide +kernel
theorem C'_543 : C' 543 :=
  ⟨c543_sqf, c543_range, c543_ell, leafNSq_of_sq c543_nsq, leafHAr_of_sq c543_har,
   c543_r, c543_e', c543_f1, leafS2_of_sq c543_s2, leafS3_of_sq c543_s3,
   c543_iso, leafR8_of_sq c543_nof2 c543_nof3 c543_nof4z⟩
theorem not_tile'_543 (D : CongruentDissection 543) : False :=
  not_tile_of_conditions' 543 C'_543 D

private theorem c553_sqf   : LeafSqf 553   := by decide +kernel
private theorem c553_range : LeafRange 553  := by decide +kernel
private theorem c553_ell   : LeafEll 553    := by decide +kernel
private theorem c553_nsq   : NSqChkSq 553   := by decide +kernel
private theorem c553_har   : HArithChkSq 553 := by decide +kernel
private theorem c553_r     : LeafR 553      := by decide +kernel
private theorem c553_e'    : LeafE' 553     := by decide +kernel
private theorem c553_f1    : LeafF1 553     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c553_s2    : S2ChkSq 553    := by decide +kernel
private theorem c553_s3    : S3ChkSq 553    := by decide +kernel
private theorem c553_iso   : LeafIso 553    := by decide +kernel
private theorem c553_nof2  : NoF2ChkSq 553  := by decide +kernel
private theorem c553_nof3  : NoF3ChkSq 553  := by decide +kernel
private theorem c553_nof4z : NoF4zChkSq 553 := by decide +kernel
theorem C'_553 : C' 553 :=
  ⟨c553_sqf, c553_range, c553_ell, leafNSq_of_sq c553_nsq, leafHAr_of_sq c553_har,
   c553_r, c553_e', c553_f1, leafS2_of_sq c553_s2, leafS3_of_sq c553_s3,
   c553_iso, leafR8_of_sq c553_nof2 c553_nof3 c553_nof4z⟩
theorem not_tile'_553 (D : CongruentDissection 553) : False :=
  not_tile_of_conditions' 553 C'_553 D

private theorem c573_sqf   : LeafSqf 573   := by decide +kernel
private theorem c573_range : LeafRange 573  := by decide +kernel
private theorem c573_ell   : LeafEll 573    := by decide +kernel
private theorem c573_nsq   : NSqChkSq 573   := by decide +kernel
private theorem c573_har   : HArithChkSq 573 := by decide +kernel
private theorem c573_r     : LeafR 573      := by decide +kernel
private theorem c573_e'    : LeafE' 573     := by decide +kernel
private theorem c573_f1    : LeafF1 573     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c573_s2    : S2ChkSq 573    := by decide +kernel
private theorem c573_s3    : S3ChkSq 573    := by decide +kernel
private theorem c573_iso   : LeafIso 573    := by decide +kernel
private theorem c573_nof2  : NoF2ChkSq 573  := by decide +kernel
private theorem c573_nof3  : NoF3ChkSq 573  := by decide +kernel
private theorem c573_nof4z : NoF4zChkSq 573 := by decide +kernel
theorem C'_573 : C' 573 :=
  ⟨c573_sqf, c573_range, c573_ell, leafNSq_of_sq c573_nsq, leafHAr_of_sq c573_har,
   c573_r, c573_e', c573_f1, leafS2_of_sq c573_s2, leafS3_of_sq c573_s3,
   c573_iso, leafR8_of_sq c573_nof2 c573_nof3 c573_nof4z⟩
theorem not_tile'_573 (D : CongruentDissection 573) : False :=
  not_tile_of_conditions' 573 C'_573 D

private theorem c579_sqf   : LeafSqf 579   := by decide +kernel
private theorem c579_range : LeafRange 579  := by decide +kernel
private theorem c579_ell   : LeafEll 579    := by decide +kernel
private theorem c579_nsq   : NSqChkSq 579   := by decide +kernel
private theorem c579_har   : HArithChkSq 579 := by decide +kernel
private theorem c579_r     : LeafR 579      := by decide +kernel
private theorem c579_e'    : LeafE' 579     := by decide +kernel
private theorem c579_f1    : LeafF1 579     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c579_s2    : S2ChkSq 579    := by decide +kernel
private theorem c579_s3    : S3ChkSq 579    := by decide +kernel
private theorem c579_iso   : LeafIso 579    := by decide +kernel
private theorem c579_nof2  : NoF2ChkSq 579  := by decide +kernel
private theorem c579_nof3  : NoF3ChkSq 579  := by decide +kernel
private theorem c579_nof4z : NoF4zChkSq 579 := by decide +kernel
theorem C'_579 : C' 579 :=
  ⟨c579_sqf, c579_range, c579_ell, leafNSq_of_sq c579_nsq, leafHAr_of_sq c579_har,
   c579_r, c579_e', c579_f1, leafS2_of_sq c579_s2, leafS3_of_sq c579_s3,
   c579_iso, leafR8_of_sq c579_nof2 c579_nof3 c579_nof4z⟩
theorem not_tile'_579 (D : CongruentDissection 579) : False :=
  not_tile_of_conditions' 579 C'_579 D

private theorem c581_sqf   : LeafSqf 581   := by decide +kernel
private theorem c581_range : LeafRange 581  := by decide +kernel
private theorem c581_ell   : LeafEll 581    := by decide +kernel
private theorem c581_nsq   : NSqChkSq 581   := by decide +kernel
private theorem c581_har   : HArithChkSq 581 := by decide +kernel
private theorem c581_r     : LeafR 581      := by decide +kernel
private theorem c581_e'    : LeafE' 581     := by decide +kernel
private theorem c581_f1    : LeafF1 581     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c581_s2    : S2ChkSq 581    := by decide +kernel
private theorem c581_s3    : S3ChkSq 581    := by decide +kernel
private theorem c581_iso   : LeafIso 581    := by decide +kernel
private theorem c581_nof2  : NoF2ChkSq 581  := by decide +kernel
private theorem c581_nof3  : NoF3ChkSq 581  := by decide +kernel
private theorem c581_nof4z : NoF4zChkSq 581 := by decide +kernel
theorem C'_581 : C' 581 :=
  ⟨c581_sqf, c581_range, c581_ell, leafNSq_of_sq c581_nsq, leafHAr_of_sq c581_har,
   c581_r, c581_e', c581_f1, leafS2_of_sq c581_s2, leafS3_of_sq c581_s3,
   c581_iso, leafR8_of_sq c581_nof2 c581_nof3 c581_nof4z⟩
theorem not_tile'_581 (D : CongruentDissection 581) : False :=
  not_tile_of_conditions' 581 C'_581 D

end Erdos634.Draft.AllN2

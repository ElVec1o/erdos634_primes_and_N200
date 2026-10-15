/- AllN2Check35: N = 1435, 1437, 1441, 1443, 1461
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1435_sqf   : LeafSqf 1435   := by decide +kernel
private theorem c1435_range : LeafRange 1435  := by decide +kernel
private theorem c1435_ell   : LeafEll 1435    := by decide +kernel
private theorem c1435_nsq   : NSqChkSq 1435   := by decide +kernel
private theorem c1435_har   : HArithChkSq 1435 := by decide +kernel
private theorem c1435_r     : LeafR 1435      := by decide +kernel
private theorem c1435_e'    : LeafE' 1435     := by decide +kernel
private theorem c1435_f1    : LeafF1 1435     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1435_s2    : S2ChkSq 1435    := by decide +kernel
private theorem c1435_s3    : S3ChkSq 1435    := by decide +kernel
private theorem c1435_iso   : LeafIso 1435    := by decide +kernel
private theorem c1435_nof2  : NoF2ChkSq 1435  := by decide +kernel
private theorem c1435_nof3  : NoF3ChkSq 1435  := by decide +kernel
private theorem c1435_nof4z : NoF4zChkSq 1435 := by decide +kernel
theorem C'_1435 : C' 1435 :=
  ⟨c1435_sqf, c1435_range, c1435_ell, leafNSq_of_sq c1435_nsq, leafHAr_of_sq c1435_har,
   c1435_r, c1435_e', c1435_f1, leafS2_of_sq c1435_s2, leafS3_of_sq c1435_s3,
   c1435_iso, leafR8_of_sq c1435_nof2 c1435_nof3 c1435_nof4z⟩
theorem not_tile'_1435 (D : CongruentDissection 1435) : False :=
  not_tile_of_conditions' 1435 C'_1435 D

private theorem c1437_sqf   : LeafSqf 1437   := by decide +kernel
private theorem c1437_range : LeafRange 1437  := by decide +kernel
private theorem c1437_ell   : LeafEll 1437    := by decide +kernel
private theorem c1437_nsq   : NSqChkSq 1437   := by decide +kernel
private theorem c1437_har   : HArithChkSq 1437 := by decide +kernel
private theorem c1437_r     : LeafR 1437      := by decide +kernel
private theorem c1437_e'    : LeafE' 1437     := by decide +kernel
private theorem c1437_f1    : LeafF1 1437     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1437_s2    : S2ChkSq 1437    := by decide +kernel
private theorem c1437_s3    : S3ChkSq 1437    := by decide +kernel
private theorem c1437_iso   : LeafIso 1437    := by decide +kernel
private theorem c1437_nof2  : NoF2ChkSq 1437  := by decide +kernel
private theorem c1437_nof3  : NoF3ChkSq 1437  := by decide +kernel
private theorem c1437_nof4z : NoF4zChkSq 1437 := by decide +kernel
theorem C'_1437 : C' 1437 :=
  ⟨c1437_sqf, c1437_range, c1437_ell, leafNSq_of_sq c1437_nsq, leafHAr_of_sq c1437_har,
   c1437_r, c1437_e', c1437_f1, leafS2_of_sq c1437_s2, leafS3_of_sq c1437_s3,
   c1437_iso, leafR8_of_sq c1437_nof2 c1437_nof3 c1437_nof4z⟩
theorem not_tile'_1437 (D : CongruentDissection 1437) : False :=
  not_tile_of_conditions' 1437 C'_1437 D

private theorem c1441_sqf   : LeafSqf 1441   := by decide +kernel
private theorem c1441_range : LeafRange 1441  := by decide +kernel
private theorem c1441_ell   : LeafEll 1441    := by decide +kernel
private theorem c1441_nsq   : NSqChkSq 1441   := by decide +kernel
private theorem c1441_har   : HArithChkSq 1441 := by decide +kernel
private theorem c1441_r     : LeafR 1441      := by decide +kernel
private theorem c1441_e'    : LeafE' 1441     := by decide +kernel
private theorem c1441_f1    : LeafF1 1441     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1441_s2    : S2ChkSq 1441    := by decide +kernel
private theorem c1441_s3    : S3ChkSq 1441    := by decide +kernel
private theorem c1441_iso   : LeafIso 1441    := by decide +kernel
private theorem c1441_nof2  : NoF2ChkSq 1441  := by decide +kernel
private theorem c1441_nof3  : NoF3ChkSq 1441  := by decide +kernel
private theorem c1441_nof4z : NoF4zChkSq 1441 := by decide +kernel
theorem C'_1441 : C' 1441 :=
  ⟨c1441_sqf, c1441_range, c1441_ell, leafNSq_of_sq c1441_nsq, leafHAr_of_sq c1441_har,
   c1441_r, c1441_e', c1441_f1, leafS2_of_sq c1441_s2, leafS3_of_sq c1441_s3,
   c1441_iso, leafR8_of_sq c1441_nof2 c1441_nof3 c1441_nof4z⟩
theorem not_tile'_1441 (D : CongruentDissection 1441) : False :=
  not_tile_of_conditions' 1441 C'_1441 D

private theorem c1443_sqf   : LeafSqf 1443   := by decide +kernel
private theorem c1443_range : LeafRange 1443  := by decide +kernel
private theorem c1443_ell   : LeafEll 1443    := by decide +kernel
private theorem c1443_nsq   : NSqChkSq 1443   := by decide +kernel
private theorem c1443_har   : HArithChkSq 1443 := by decide +kernel
private theorem c1443_r     : LeafR 1443      := by decide +kernel
private theorem c1443_e'    : LeafE' 1443     := by decide +kernel
private theorem c1443_f1    : LeafF1 1443     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1443_s2    : S2ChkSq 1443    := by decide +kernel
private theorem c1443_s3    : S3ChkSq 1443    := by decide +kernel
private theorem c1443_iso   : LeafIso 1443    := by decide +kernel
private theorem c1443_nof2  : NoF2ChkSq 1443  := by decide +kernel
private theorem c1443_nof3  : NoF3ChkSq 1443  := by decide +kernel
private theorem c1443_nof4z : NoF4zChkSq 1443 := by decide +kernel
theorem C'_1443 : C' 1443 :=
  ⟨c1443_sqf, c1443_range, c1443_ell, leafNSq_of_sq c1443_nsq, leafHAr_of_sq c1443_har,
   c1443_r, c1443_e', c1443_f1, leafS2_of_sq c1443_s2, leafS3_of_sq c1443_s3,
   c1443_iso, leafR8_of_sq c1443_nof2 c1443_nof3 c1443_nof4z⟩
theorem not_tile'_1443 (D : CongruentDissection 1443) : False :=
  not_tile_of_conditions' 1443 C'_1443 D

private theorem c1461_sqf   : LeafSqf 1461   := by decide +kernel
private theorem c1461_range : LeafRange 1461  := by decide +kernel
private theorem c1461_ell   : LeafEll 1461    := by decide +kernel
private theorem c1461_nsq   : NSqChkSq 1461   := by decide +kernel
private theorem c1461_har   : HArithChkSq 1461 := by decide +kernel
private theorem c1461_r     : LeafR 1461      := by decide +kernel
private theorem c1461_e'    : LeafE' 1461     := by decide +kernel
private theorem c1461_f1    : LeafF1 1461     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1461_s2    : S2ChkSq 1461    := by decide +kernel
private theorem c1461_s3    : S3ChkSq 1461    := by decide +kernel
private theorem c1461_iso   : LeafIso 1461    := by decide +kernel
private theorem c1461_nof2  : NoF2ChkSq 1461  := by decide +kernel
private theorem c1461_nof3  : NoF3ChkSq 1461  := by decide +kernel
private theorem c1461_nof4z : NoF4zChkSq 1461 := by decide +kernel
theorem C'_1461 : C' 1461 :=
  ⟨c1461_sqf, c1461_range, c1461_ell, leafNSq_of_sq c1461_nsq, leafHAr_of_sq c1461_har,
   c1461_r, c1461_e', c1461_f1, leafS2_of_sq c1461_s2, leafS3_of_sq c1461_s3,
   c1461_iso, leafR8_of_sq c1461_nof2 c1461_nof3 c1461_nof4z⟩
theorem not_tile'_1461 (D : CongruentDissection 1461) : False :=
  not_tile_of_conditions' 1461 C'_1461 D

end Erdos634.Draft.AllN2

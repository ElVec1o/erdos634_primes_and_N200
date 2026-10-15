/- AllN2Check33: N = 1351, 1355, 1371, 1379, 1383
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1351_sqf   : LeafSqf 1351   := by decide +kernel
private theorem c1351_range : LeafRange 1351  := by decide +kernel
private theorem c1351_ell   : LeafEll 1351    := by decide +kernel
private theorem c1351_nsq   : NSqChkSq 1351   := by decide +kernel
private theorem c1351_har   : HArithChkSq 1351 := by decide +kernel
private theorem c1351_r     : LeafR 1351      := by decide +kernel
private theorem c1351_e'    : LeafE' 1351     := by decide +kernel
private theorem c1351_f1    : LeafF1 1351     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1351_s2    : S2ChkSq 1351    := by decide +kernel
private theorem c1351_s3    : S3ChkSq 1351    := by decide +kernel
private theorem c1351_iso   : LeafIso 1351    := by decide +kernel
private theorem c1351_nof2  : NoF2ChkSq 1351  := by decide +kernel
private theorem c1351_nof3  : NoF3ChkSq 1351  := by decide +kernel
private theorem c1351_nof4z : NoF4zChkSq 1351 := by decide +kernel
theorem C'_1351 : C' 1351 :=
  ⟨c1351_sqf, c1351_range, c1351_ell, leafNSq_of_sq c1351_nsq, leafHAr_of_sq c1351_har,
   c1351_r, c1351_e', c1351_f1, leafS2_of_sq c1351_s2, leafS3_of_sq c1351_s3,
   c1351_iso, leafR8_of_sq c1351_nof2 c1351_nof3 c1351_nof4z⟩
theorem not_tile'_1351 (D : CongruentDissection 1351) : False :=
  not_tile_of_conditions' 1351 C'_1351 D

private theorem c1355_sqf   : LeafSqf 1355   := by decide +kernel
private theorem c1355_range : LeafRange 1355  := by decide +kernel
private theorem c1355_ell   : LeafEll 1355    := by decide +kernel
private theorem c1355_nsq   : NSqChkSq 1355   := by decide +kernel
private theorem c1355_har   : HArithChkSq 1355 := by decide +kernel
private theorem c1355_r     : LeafR 1355      := by decide +kernel
private theorem c1355_e'    : LeafE' 1355     := by decide +kernel
private theorem c1355_f1    : LeafF1 1355     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1355_s2    : S2ChkSq 1355    := by decide +kernel
private theorem c1355_s3    : S3ChkSq 1355    := by decide +kernel
private theorem c1355_iso   : LeafIso 1355    := by decide +kernel
private theorem c1355_nof2  : NoF2ChkSq 1355  := by decide +kernel
private theorem c1355_nof3  : NoF3ChkSq 1355  := by decide +kernel
private theorem c1355_nof4z : NoF4zChkSq 1355 := by decide +kernel
theorem C'_1355 : C' 1355 :=
  ⟨c1355_sqf, c1355_range, c1355_ell, leafNSq_of_sq c1355_nsq, leafHAr_of_sq c1355_har,
   c1355_r, c1355_e', c1355_f1, leafS2_of_sq c1355_s2, leafS3_of_sq c1355_s3,
   c1355_iso, leafR8_of_sq c1355_nof2 c1355_nof3 c1355_nof4z⟩
theorem not_tile'_1355 (D : CongruentDissection 1355) : False :=
  not_tile_of_conditions' 1355 C'_1355 D

private theorem c1371_sqf   : LeafSqf 1371   := by decide +kernel
private theorem c1371_range : LeafRange 1371  := by decide +kernel
private theorem c1371_ell   : LeafEll 1371    := by decide +kernel
private theorem c1371_nsq   : NSqChkSq 1371   := by decide +kernel
private theorem c1371_har   : HArithChkSq 1371 := by decide +kernel
private theorem c1371_r     : LeafR 1371      := by decide +kernel
private theorem c1371_e'    : LeafE' 1371     := by decide +kernel
private theorem c1371_f1    : LeafF1 1371     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1371_s2    : S2ChkSq 1371    := by decide +kernel
private theorem c1371_s3    : S3ChkSq 1371    := by decide +kernel
private theorem c1371_iso   : LeafIso 1371    := by decide +kernel
private theorem c1371_nof2  : NoF2ChkSq 1371  := by decide +kernel
private theorem c1371_nof3  : NoF3ChkSq 1371  := by decide +kernel
private theorem c1371_nof4z : NoF4zChkSq 1371 := by decide +kernel
theorem C'_1371 : C' 1371 :=
  ⟨c1371_sqf, c1371_range, c1371_ell, leafNSq_of_sq c1371_nsq, leafHAr_of_sq c1371_har,
   c1371_r, c1371_e', c1371_f1, leafS2_of_sq c1371_s2, leafS3_of_sq c1371_s3,
   c1371_iso, leafR8_of_sq c1371_nof2 c1371_nof3 c1371_nof4z⟩
theorem not_tile'_1371 (D : CongruentDissection 1371) : False :=
  not_tile_of_conditions' 1371 C'_1371 D

private theorem c1379_sqf   : LeafSqf 1379   := by decide +kernel
private theorem c1379_range : LeafRange 1379  := by decide +kernel
private theorem c1379_ell   : LeafEll 1379    := by decide +kernel
private theorem c1379_nsq   : NSqChkSq 1379   := by decide +kernel
private theorem c1379_har   : HArithChkSq 1379 := by decide +kernel
private theorem c1379_r     : LeafR 1379      := by decide +kernel
private theorem c1379_e'    : LeafE' 1379     := by decide +kernel
private theorem c1379_f1    : LeafF1 1379     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1379_s2    : S2ChkSq 1379    := by decide +kernel
private theorem c1379_s3    : S3ChkSq 1379    := by decide +kernel
private theorem c1379_iso   : LeafIso 1379    := by decide +kernel
private theorem c1379_nof2  : NoF2ChkSq 1379  := by decide +kernel
private theorem c1379_nof3  : NoF3ChkSq 1379  := by decide +kernel
private theorem c1379_nof4z : NoF4zChkSq 1379 := by decide +kernel
theorem C'_1379 : C' 1379 :=
  ⟨c1379_sqf, c1379_range, c1379_ell, leafNSq_of_sq c1379_nsq, leafHAr_of_sq c1379_har,
   c1379_r, c1379_e', c1379_f1, leafS2_of_sq c1379_s2, leafS3_of_sq c1379_s3,
   c1379_iso, leafR8_of_sq c1379_nof2 c1379_nof3 c1379_nof4z⟩
theorem not_tile'_1379 (D : CongruentDissection 1379) : False :=
  not_tile_of_conditions' 1379 C'_1379 D

private theorem c1383_sqf   : LeafSqf 1383   := by decide +kernel
private theorem c1383_range : LeafRange 1383  := by decide +kernel
private theorem c1383_ell   : LeafEll 1383    := by decide +kernel
private theorem c1383_nsq   : NSqChkSq 1383   := by decide +kernel
private theorem c1383_har   : HArithChkSq 1383 := by decide +kernel
private theorem c1383_r     : LeafR 1383      := by decide +kernel
private theorem c1383_e'    : LeafE' 1383     := by decide +kernel
private theorem c1383_f1    : LeafF1 1383     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1383_s2    : S2ChkSq 1383    := by decide +kernel
private theorem c1383_s3    : S3ChkSq 1383    := by decide +kernel
private theorem c1383_iso   : LeafIso 1383    := by decide +kernel
private theorem c1383_nof2  : NoF2ChkSq 1383  := by decide +kernel
private theorem c1383_nof3  : NoF3ChkSq 1383  := by decide +kernel
private theorem c1383_nof4z : NoF4zChkSq 1383 := by decide +kernel
theorem C'_1383 : C' 1383 :=
  ⟨c1383_sqf, c1383_range, c1383_ell, leafNSq_of_sq c1383_nsq, leafHAr_of_sq c1383_har,
   c1383_r, c1383_e', c1383_f1, leafS2_of_sq c1383_s2, leafS3_of_sq c1383_s3,
   c1383_iso, leafR8_of_sq c1383_nof2 c1383_nof3 c1383_nof4z⟩
theorem not_tile'_1383 (D : CongruentDissection 1383) : False :=
  not_tile_of_conditions' 1383 C'_1383 D

end Erdos634.Draft.AllN2

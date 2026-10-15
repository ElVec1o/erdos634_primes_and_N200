/- AllN2Check32: N = 1315, 1317, 1329, 1337, 1347
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1315_sqf   : LeafSqf 1315   := by decide +kernel
private theorem c1315_range : LeafRange 1315  := by decide +kernel
private theorem c1315_ell   : LeafEll 1315    := by decide +kernel
private theorem c1315_nsq   : NSqChkSq 1315   := by decide +kernel
private theorem c1315_har   : HArithChkSq 1315 := by decide +kernel
private theorem c1315_r     : LeafR 1315      := by decide +kernel
private theorem c1315_e'    : LeafE' 1315     := by decide +kernel
private theorem c1315_f1    : LeafF1 1315     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1315_s2    : S2ChkSq 1315    := by decide +kernel
private theorem c1315_s3    : S3ChkSq 1315    := by decide +kernel
private theorem c1315_iso   : LeafIso 1315    := by decide +kernel
private theorem c1315_nof2  : NoF2ChkSq 1315  := by decide +kernel
private theorem c1315_nof3  : NoF3ChkSq 1315  := by decide +kernel
private theorem c1315_nof4z : NoF4zChkSq 1315 := by decide +kernel
theorem C'_1315 : C' 1315 :=
  ⟨c1315_sqf, c1315_range, c1315_ell, leafNSq_of_sq c1315_nsq, leafHAr_of_sq c1315_har,
   c1315_r, c1315_e', c1315_f1, leafS2_of_sq c1315_s2, leafS3_of_sq c1315_s3,
   c1315_iso, leafR8_of_sq c1315_nof2 c1315_nof3 c1315_nof4z⟩
theorem not_tile'_1315 (D : CongruentDissection 1315) : False :=
  not_tile_of_conditions' 1315 C'_1315 D

private theorem c1317_sqf   : LeafSqf 1317   := by decide +kernel
private theorem c1317_range : LeafRange 1317  := by decide +kernel
private theorem c1317_ell   : LeafEll 1317    := by decide +kernel
private theorem c1317_nsq   : NSqChkSq 1317   := by decide +kernel
private theorem c1317_har   : HArithChkSq 1317 := by decide +kernel
private theorem c1317_r     : LeafR 1317      := by decide +kernel
private theorem c1317_e'    : LeafE' 1317     := by decide +kernel
private theorem c1317_f1    : LeafF1 1317     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1317_s2    : S2ChkSq 1317    := by decide +kernel
private theorem c1317_s3    : S3ChkSq 1317    := by decide +kernel
private theorem c1317_iso   : LeafIso 1317    := by decide +kernel
private theorem c1317_nof2  : NoF2ChkSq 1317  := by decide +kernel
private theorem c1317_nof3  : NoF3ChkSq 1317  := by decide +kernel
private theorem c1317_nof4z : NoF4zChkSq 1317 := by decide +kernel
theorem C'_1317 : C' 1317 :=
  ⟨c1317_sqf, c1317_range, c1317_ell, leafNSq_of_sq c1317_nsq, leafHAr_of_sq c1317_har,
   c1317_r, c1317_e', c1317_f1, leafS2_of_sq c1317_s2, leafS3_of_sq c1317_s3,
   c1317_iso, leafR8_of_sq c1317_nof2 c1317_nof3 c1317_nof4z⟩
theorem not_tile'_1317 (D : CongruentDissection 1317) : False :=
  not_tile_of_conditions' 1317 C'_1317 D

private theorem c1329_sqf   : LeafSqf 1329   := by decide +kernel
private theorem c1329_range : LeafRange 1329  := by decide +kernel
private theorem c1329_ell   : LeafEll 1329    := by decide +kernel
private theorem c1329_nsq   : NSqChkSq 1329   := by decide +kernel
private theorem c1329_har   : HArithChkSq 1329 := by decide +kernel
private theorem c1329_r     : LeafR 1329      := by decide +kernel
private theorem c1329_e'    : LeafE' 1329     := by decide +kernel
private theorem c1329_f1    : LeafF1 1329     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1329_s2    : S2ChkSq 1329    := by decide +kernel
private theorem c1329_s3    : S3ChkSq 1329    := by decide +kernel
private theorem c1329_iso   : LeafIso 1329    := by decide +kernel
private theorem c1329_nof2  : NoF2ChkSq 1329  := by decide +kernel
private theorem c1329_nof3  : NoF3ChkSq 1329  := by decide +kernel
private theorem c1329_nof4z : NoF4zChkSq 1329 := by decide +kernel
theorem C'_1329 : C' 1329 :=
  ⟨c1329_sqf, c1329_range, c1329_ell, leafNSq_of_sq c1329_nsq, leafHAr_of_sq c1329_har,
   c1329_r, c1329_e', c1329_f1, leafS2_of_sq c1329_s2, leafS3_of_sq c1329_s3,
   c1329_iso, leafR8_of_sq c1329_nof2 c1329_nof3 c1329_nof4z⟩
theorem not_tile'_1329 (D : CongruentDissection 1329) : False :=
  not_tile_of_conditions' 1329 C'_1329 D

private theorem c1337_sqf   : LeafSqf 1337   := by decide +kernel
private theorem c1337_range : LeafRange 1337  := by decide +kernel
private theorem c1337_ell   : LeafEll 1337    := by decide +kernel
private theorem c1337_nsq   : NSqChkSq 1337   := by decide +kernel
private theorem c1337_har   : HArithChkSq 1337 := by decide +kernel
private theorem c1337_r     : LeafR 1337      := by decide +kernel
private theorem c1337_e'    : LeafE' 1337     := by decide +kernel
private theorem c1337_f1    : LeafF1 1337     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1337_s2    : S2ChkSq 1337    := by decide +kernel
private theorem c1337_s3    : S3ChkSq 1337    := by decide +kernel
private theorem c1337_iso   : LeafIso 1337    := by decide +kernel
private theorem c1337_nof2  : NoF2ChkSq 1337  := by decide +kernel
private theorem c1337_nof3  : NoF3ChkSq 1337  := by decide +kernel
private theorem c1337_nof4z : NoF4zChkSq 1337 := by decide +kernel
theorem C'_1337 : C' 1337 :=
  ⟨c1337_sqf, c1337_range, c1337_ell, leafNSq_of_sq c1337_nsq, leafHAr_of_sq c1337_har,
   c1337_r, c1337_e', c1337_f1, leafS2_of_sq c1337_s2, leafS3_of_sq c1337_s3,
   c1337_iso, leafR8_of_sq c1337_nof2 c1337_nof3 c1337_nof4z⟩
theorem not_tile'_1337 (D : CongruentDissection 1337) : False :=
  not_tile_of_conditions' 1337 C'_1337 D

private theorem c1347_sqf   : LeafSqf 1347   := by decide +kernel
private theorem c1347_range : LeafRange 1347  := by decide +kernel
private theorem c1347_ell   : LeafEll 1347    := by decide +kernel
private theorem c1347_nsq   : NSqChkSq 1347   := by decide +kernel
private theorem c1347_har   : HArithChkSq 1347 := by decide +kernel
private theorem c1347_r     : LeafR 1347      := by decide +kernel
private theorem c1347_e'    : LeafE' 1347     := by decide +kernel
private theorem c1347_f1    : LeafF1 1347     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1347_s2    : S2ChkSq 1347    := by decide +kernel
private theorem c1347_s3    : S3ChkSq 1347    := by decide +kernel
private theorem c1347_iso   : LeafIso 1347    := by decide +kernel
private theorem c1347_nof2  : NoF2ChkSq 1347  := by decide +kernel
private theorem c1347_nof3  : NoF3ChkSq 1347  := by decide +kernel
private theorem c1347_nof4z : NoF4zChkSq 1347 := by decide +kernel
theorem C'_1347 : C' 1347 :=
  ⟨c1347_sqf, c1347_range, c1347_ell, leafNSq_of_sq c1347_nsq, leafHAr_of_sq c1347_har,
   c1347_r, c1347_e', c1347_f1, leafS2_of_sq c1347_s2, leafS3_of_sq c1347_s3,
   c1347_iso, leafR8_of_sq c1347_nof2 c1347_nof3 c1347_nof4z⟩
theorem not_tile'_1347 (D : CongruentDissection 1347) : False :=
  not_tile_of_conditions' 1347 C'_1347 D

end Erdos634.Draft.AllN2

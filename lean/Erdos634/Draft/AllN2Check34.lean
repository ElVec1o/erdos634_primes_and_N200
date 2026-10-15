/- AllN2Check34: N = 1389, 1393, 1397, 1401, 1415
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1389_sqf   : LeafSqf 1389   := by decide +kernel
private theorem c1389_range : LeafRange 1389  := by decide +kernel
private theorem c1389_ell   : LeafEll 1389    := by decide +kernel
private theorem c1389_nsq   : NSqChkSq 1389   := by decide +kernel
private theorem c1389_har   : HArithChkSq 1389 := by decide +kernel
private theorem c1389_r     : LeafR 1389      := by decide +kernel
private theorem c1389_e'    : LeafE' 1389     := by decide +kernel
private theorem c1389_f1    : LeafF1 1389     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1389_s2    : S2ChkSq 1389    := by decide +kernel
private theorem c1389_s3    : S3ChkSq 1389    := by decide +kernel
private theorem c1389_iso   : LeafIso 1389    := by decide +kernel
private theorem c1389_nof2  : NoF2ChkSq 1389  := by decide +kernel
private theorem c1389_nof3  : NoF3ChkSq 1389  := by decide +kernel
private theorem c1389_nof4z : NoF4zChkSq 1389 := by decide +kernel
theorem C'_1389 : C' 1389 :=
  ⟨c1389_sqf, c1389_range, c1389_ell, leafNSq_of_sq c1389_nsq, leafHAr_of_sq c1389_har,
   c1389_r, c1389_e', c1389_f1, leafS2_of_sq c1389_s2, leafS3_of_sq c1389_s3,
   c1389_iso, leafR8_of_sq c1389_nof2 c1389_nof3 c1389_nof4z⟩
theorem not_tile'_1389 (D : CongruentDissection 1389) : False :=
  not_tile_of_conditions' 1389 C'_1389 D

private theorem c1393_sqf   : LeafSqf 1393   := by decide +kernel
private theorem c1393_range : LeafRange 1393  := by decide +kernel
private theorem c1393_ell   : LeafEll 1393    := by decide +kernel
private theorem c1393_nsq   : NSqChkSq 1393   := by decide +kernel
private theorem c1393_har   : HArithChkSq 1393 := by decide +kernel
private theorem c1393_r     : LeafR 1393      := by decide +kernel
private theorem c1393_e'    : LeafE' 1393     := by decide +kernel
private theorem c1393_f1    : LeafF1 1393     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1393_s2    : S2ChkSq 1393    := by decide +kernel
private theorem c1393_s3    : S3ChkSq 1393    := by decide +kernel
private theorem c1393_iso   : LeafIso 1393    := by decide +kernel
private theorem c1393_nof2  : NoF2ChkSq 1393  := by decide +kernel
private theorem c1393_nof3  : NoF3ChkSq 1393  := by decide +kernel
private theorem c1393_nof4z : NoF4zChkSq 1393 := by decide +kernel
theorem C'_1393 : C' 1393 :=
  ⟨c1393_sqf, c1393_range, c1393_ell, leafNSq_of_sq c1393_nsq, leafHAr_of_sq c1393_har,
   c1393_r, c1393_e', c1393_f1, leafS2_of_sq c1393_s2, leafS3_of_sq c1393_s3,
   c1393_iso, leafR8_of_sq c1393_nof2 c1393_nof3 c1393_nof4z⟩
theorem not_tile'_1393 (D : CongruentDissection 1393) : False :=
  not_tile_of_conditions' 1393 C'_1393 D

private theorem c1397_sqf   : LeafSqf 1397   := by decide +kernel
private theorem c1397_range : LeafRange 1397  := by decide +kernel
private theorem c1397_ell   : LeafEll 1397    := by decide +kernel
private theorem c1397_nsq   : NSqChkSq 1397   := by decide +kernel
private theorem c1397_har   : HArithChkSq 1397 := by decide +kernel
private theorem c1397_r     : LeafR 1397      := by decide +kernel
private theorem c1397_e'    : LeafE' 1397     := by decide +kernel
private theorem c1397_f1    : LeafF1 1397     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1397_s2    : S2ChkSq 1397    := by decide +kernel
private theorem c1397_s3    : S3ChkSq 1397    := by decide +kernel
private theorem c1397_iso   : LeafIso 1397    := by decide +kernel
private theorem c1397_nof2  : NoF2ChkSq 1397  := by decide +kernel
private theorem c1397_nof3  : NoF3ChkSq 1397  := by decide +kernel
private theorem c1397_nof4z : NoF4zChkSq 1397 := by decide +kernel
theorem C'_1397 : C' 1397 :=
  ⟨c1397_sqf, c1397_range, c1397_ell, leafNSq_of_sq c1397_nsq, leafHAr_of_sq c1397_har,
   c1397_r, c1397_e', c1397_f1, leafS2_of_sq c1397_s2, leafS3_of_sq c1397_s3,
   c1397_iso, leafR8_of_sq c1397_nof2 c1397_nof3 c1397_nof4z⟩
theorem not_tile'_1397 (D : CongruentDissection 1397) : False :=
  not_tile_of_conditions' 1397 C'_1397 D

private theorem c1401_sqf   : LeafSqf 1401   := by decide +kernel
private theorem c1401_range : LeafRange 1401  := by decide +kernel
private theorem c1401_ell   : LeafEll 1401    := by decide +kernel
private theorem c1401_nsq   : NSqChkSq 1401   := by decide +kernel
private theorem c1401_har   : HArithChkSq 1401 := by decide +kernel
private theorem c1401_r     : LeafR 1401      := by decide +kernel
private theorem c1401_e'    : LeafE' 1401     := by decide +kernel
private theorem c1401_f1    : LeafF1 1401     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1401_s2    : S2ChkSq 1401    := by decide +kernel
private theorem c1401_s3    : S3ChkSq 1401    := by decide +kernel
private theorem c1401_iso   : LeafIso 1401    := by decide +kernel
private theorem c1401_nof2  : NoF2ChkSq 1401  := by decide +kernel
private theorem c1401_nof3  : NoF3ChkSq 1401  := by decide +kernel
private theorem c1401_nof4z : NoF4zChkSq 1401 := by decide +kernel
theorem C'_1401 : C' 1401 :=
  ⟨c1401_sqf, c1401_range, c1401_ell, leafNSq_of_sq c1401_nsq, leafHAr_of_sq c1401_har,
   c1401_r, c1401_e', c1401_f1, leafS2_of_sq c1401_s2, leafS3_of_sq c1401_s3,
   c1401_iso, leafR8_of_sq c1401_nof2 c1401_nof3 c1401_nof4z⟩
theorem not_tile'_1401 (D : CongruentDissection 1401) : False :=
  not_tile_of_conditions' 1401 C'_1401 D

private theorem c1415_sqf   : LeafSqf 1415   := by decide +kernel
private theorem c1415_range : LeafRange 1415  := by decide +kernel
private theorem c1415_ell   : LeafEll 1415    := by decide +kernel
private theorem c1415_nsq   : NSqChkSq 1415   := by decide +kernel
private theorem c1415_har   : HArithChkSq 1415 := by decide +kernel
private theorem c1415_r     : LeafR 1415      := by decide +kernel
private theorem c1415_e'    : LeafE' 1415     := by decide +kernel
private theorem c1415_f1    : LeafF1 1415     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1415_s2    : S2ChkSq 1415    := by decide +kernel
private theorem c1415_s3    : S3ChkSq 1415    := by decide +kernel
private theorem c1415_iso   : LeafIso 1415    := by decide +kernel
private theorem c1415_nof2  : NoF2ChkSq 1415  := by decide +kernel
private theorem c1415_nof3  : NoF3ChkSq 1415  := by decide +kernel
private theorem c1415_nof4z : NoF4zChkSq 1415 := by decide +kernel
theorem C'_1415 : C' 1415 :=
  ⟨c1415_sqf, c1415_range, c1415_ell, leafNSq_of_sq c1415_nsq, leafHAr_of_sq c1415_har,
   c1415_r, c1415_e', c1415_f1, leafS2_of_sq c1415_s2, leafS3_of_sq c1415_s3,
   c1415_iso, leafR8_of_sq c1415_nof2 c1415_nof3 c1415_nof4z⟩
theorem not_tile'_1415 (D : CongruentDissection 1415) : False :=
  not_tile_of_conditions' 1415 C'_1415 D

end Erdos634.Draft.AllN2

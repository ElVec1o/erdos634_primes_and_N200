/- AllN2Check95: N = 2546, 2551, 2555, 2558, 2559
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2546_sqf   : LeafSqf 2546   := by decide +kernel
private theorem c2546_range : LeafRange 2546  := by decide +kernel
private theorem c2546_ell   : LeafEll 2546    := by decide +kernel
private theorem c2546_nsq   : NSqChkSq 2546   := by decide +kernel
private theorem c2546_har   : HArithChkSq 2546 := by decide +kernel
private theorem c2546_r     : LeafR 2546      := by decide +kernel
private theorem c2546_e'    : LeafE' 2546     := by decide +kernel
private theorem c2546_f1    : LeafF1 2546     := Or.inl (by decide)
private theorem c2546_s2    : S2ChkSq 2546    := by decide +kernel
private theorem c2546_s3    : S3ChkSq 2546    := by decide +kernel
private theorem c2546_iso   : LeafIso 2546    := by decide +kernel
private theorem c2546_nof2  : NoF2ChkSq 2546  := by decide +kernel
private theorem c2546_nof3  : NoF3ChkSq 2546  := by decide +kernel
private theorem c2546_nof4z : NoF4zChkSq 2546 := by decide +kernel
theorem C'_2546 : C' 2546 :=
  ⟨c2546_sqf, c2546_range, c2546_ell, leafNSq_of_sq c2546_nsq, leafHAr_of_sq c2546_har,
   c2546_r, c2546_e', c2546_f1, leafS2_of_sq c2546_s2, leafS3_of_sq c2546_s3,
   c2546_iso, leafR8_of_sq c2546_nof2 c2546_nof3 c2546_nof4z⟩
theorem not_tile'_2546 (D : CongruentDissection 2546) : False :=
  not_tile_of_conditions' 2546 C'_2546 D

private theorem c2551_sqf   : LeafSqf 2551   := by decide +kernel
private theorem c2551_range : LeafRange 2551  := by decide +kernel
private theorem c2551_ell   : LeafEll 2551    := by decide +kernel
private theorem c2551_nsq   : NSqChkSq 2551   := by decide +kernel
private theorem c2551_har   : HArithChkSq 2551 := by decide +kernel
private theorem c2551_r     : LeafR 2551      := by decide +kernel
private theorem c2551_e'    : LeafE' 2551     := by decide +kernel
private theorem c2551_f1    : LeafF1 2551     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2551_s2    : S2ChkSq 2551    := by decide +kernel
private theorem c2551_s3    : S3ChkSq 2551    := by decide +kernel
private theorem c2551_iso   : LeafIso 2551    := by decide +kernel
private theorem c2551_nof2  : NoF2ChkSq 2551  := by decide +kernel
private theorem c2551_nof3  : NoF3ChkSq 2551  := by decide +kernel
private theorem c2551_nof4z : NoF4zChkSq 2551 := by decide +kernel
theorem C'_2551 : C' 2551 :=
  ⟨c2551_sqf, c2551_range, c2551_ell, leafNSq_of_sq c2551_nsq, leafHAr_of_sq c2551_har,
   c2551_r, c2551_e', c2551_f1, leafS2_of_sq c2551_s2, leafS3_of_sq c2551_s3,
   c2551_iso, leafR8_of_sq c2551_nof2 c2551_nof3 c2551_nof4z⟩
theorem not_tile'_2551 (D : CongruentDissection 2551) : False :=
  not_tile_of_conditions' 2551 C'_2551 D

private theorem c2555_sqf   : LeafSqf 2555   := by decide +kernel
private theorem c2555_range : LeafRange 2555  := by decide +kernel
private theorem c2555_ell   : LeafEll 2555    := by decide +kernel
private theorem c2555_nsq   : NSqChkSq 2555   := by decide +kernel
private theorem c2555_har   : HArithChkSq 2555 := by decide +kernel
private theorem c2555_r     : LeafR 2555      := by decide +kernel
private theorem c2555_e'    : LeafE' 2555     := by decide +kernel
private theorem c2555_f1    : LeafF1 2555     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2555_s2    : S2ChkSq 2555    := by decide +kernel
private theorem c2555_s3    : S3ChkSq 2555    := by decide +kernel
private theorem c2555_iso   : LeafIso 2555    := by decide +kernel
private theorem c2555_nof2  : NoF2ChkSq 2555  := by decide +kernel
private theorem c2555_nof3  : NoF3ChkSq 2555  := by decide +kernel
private theorem c2555_nof4z : NoF4zChkSq 2555 := by decide +kernel
theorem C'_2555 : C' 2555 :=
  ⟨c2555_sqf, c2555_range, c2555_ell, leafNSq_of_sq c2555_nsq, leafHAr_of_sq c2555_har,
   c2555_r, c2555_e', c2555_f1, leafS2_of_sq c2555_s2, leafS3_of_sq c2555_s3,
   c2555_iso, leafR8_of_sq c2555_nof2 c2555_nof3 c2555_nof4z⟩
theorem not_tile'_2555 (D : CongruentDissection 2555) : False :=
  not_tile_of_conditions' 2555 C'_2555 D

private theorem c2558_sqf   : LeafSqf 2558   := by decide +kernel
private theorem c2558_range : LeafRange 2558  := by decide +kernel
private theorem c2558_ell   : LeafEll 2558    := by decide +kernel
private theorem c2558_nsq   : NSqChkSq 2558   := by decide +kernel
private theorem c2558_har   : HArithChkSq 2558 := by decide +kernel
private theorem c2558_r     : LeafR 2558      := by decide +kernel
private theorem c2558_e'    : LeafE' 2558     := by decide +kernel
private theorem c2558_f1    : LeafF1 2558     := Or.inl (by decide)
private theorem c2558_s2    : S2ChkSq 2558    := by decide +kernel
private theorem c2558_s3    : S3ChkSq 2558    := by decide +kernel
private theorem c2558_iso   : LeafIso 2558    := by decide +kernel
private theorem c2558_nof2  : NoF2ChkSq 2558  := by decide +kernel
private theorem c2558_nof3  : NoF3ChkSq 2558  := by decide +kernel
private theorem c2558_nof4z : NoF4zChkSq 2558 := by decide +kernel
theorem C'_2558 : C' 2558 :=
  ⟨c2558_sqf, c2558_range, c2558_ell, leafNSq_of_sq c2558_nsq, leafHAr_of_sq c2558_har,
   c2558_r, c2558_e', c2558_f1, leafS2_of_sq c2558_s2, leafS3_of_sq c2558_s3,
   c2558_iso, leafR8_of_sq c2558_nof2 c2558_nof3 c2558_nof4z⟩
theorem not_tile'_2558 (D : CongruentDissection 2558) : False :=
  not_tile_of_conditions' 2558 C'_2558 D

private theorem c2559_sqf   : LeafSqf 2559   := by decide +kernel
private theorem c2559_range : LeafRange 2559  := by decide +kernel
private theorem c2559_ell   : LeafEll 2559    := by decide +kernel
private theorem c2559_nsq   : NSqChkSq 2559   := by decide +kernel
private theorem c2559_har   : HArithChkSq 2559 := by decide +kernel
private theorem c2559_r     : LeafR 2559      := by decide +kernel
private theorem c2559_e'    : LeafE' 2559     := by decide +kernel
private theorem c2559_f1    : LeafF1 2559     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2559_s2    : S2ChkSq 2559    := by decide +kernel
private theorem c2559_s3    : S3ChkSq 2559    := by decide +kernel
private theorem c2559_iso   : LeafIso 2559    := by decide +kernel
private theorem c2559_nof2  : NoF2ChkSq 2559  := by decide +kernel
private theorem c2559_nof3  : NoF3ChkSq 2559  := by decide +kernel
private theorem c2559_nof4z : NoF4zChkSq 2559 := by decide +kernel
theorem C'_2559 : C' 2559 :=
  ⟨c2559_sqf, c2559_range, c2559_ell, leafNSq_of_sq c2559_nsq, leafHAr_of_sq c2559_har,
   c2559_r, c2559_e', c2559_f1, leafS2_of_sq c2559_s2, leafS3_of_sq c2559_s3,
   c2559_iso, leafR8_of_sq c2559_nof2 c2559_nof3 c2559_nof4z⟩
theorem not_tile'_2559 (D : CongruentDissection 2559) : False :=
  not_tile_of_conditions' 2559 C'_2559 D

end Erdos634.Draft.AllN2

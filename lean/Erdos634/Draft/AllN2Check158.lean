/- AllN2Check158: N = 3353, 3355, 3358, 3359, 3367
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3353_sqf   : LeafSqf 3353   := by decide +kernel
private theorem c3353_range : LeafRange 3353  := by decide +kernel
private theorem c3353_ell   : LeafEll 3353    := by decide +kernel
private theorem c3353_nsq   : NSqChkSq 3353   := by decide +kernel
private theorem c3353_har   : HArithChkSq 3353 := by decide +kernel
private theorem c3353_r     : LeafR 3353      := by decide +kernel
private theorem c3353_e'    : LeafE' 3353     := by decide +kernel
private theorem c3353_f1    : LeafF1 3353     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3353_s2    : S2ChkSq 3353    := by decide +kernel
private theorem c3353_s3    : S3ChkSq 3353    := by decide +kernel
private theorem c3353_iso   : LeafIso 3353    := by decide +kernel
private theorem c3353_nof2  : NoF2ChkSq 3353  := by decide +kernel
private theorem c3353_nof3  : NoF3ChkSq 3353  := by decide +kernel
private theorem c3353_nof4z : NoF4zChkSq 3353 := by decide +kernel
theorem C'_3353 : C' 3353 :=
  ⟨c3353_sqf, c3353_range, c3353_ell, leafNSq_of_sq c3353_nsq, leafHAr_of_sq c3353_har,
   c3353_r, c3353_e', c3353_f1, leafS2_of_sq c3353_s2, leafS3_of_sq c3353_s3,
   c3353_iso, leafR8_of_sq c3353_nof2 c3353_nof3 c3353_nof4z⟩
theorem not_tile'_3353 (D : CongruentDissection 3353) : False :=
  not_tile_of_conditions' 3353 C'_3353 D

private theorem c3355_sqf   : LeafSqf 3355   := by decide +kernel
private theorem c3355_range : LeafRange 3355  := by decide +kernel
private theorem c3355_ell   : LeafEll 3355    := by decide +kernel
private theorem c3355_nsq   : NSqChkSq 3355   := by decide +kernel
private theorem c3355_har   : HArithChkSq 3355 := by decide +kernel
private theorem c3355_r     : LeafR 3355      := by decide +kernel
private theorem c3355_e'    : LeafE' 3355     := by decide +kernel
private theorem c3355_f1    : LeafF1 3355     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3355_s2    : S2ChkSq 3355    := by decide +kernel
private theorem c3355_s3    : S3ChkSq 3355    := by decide +kernel
private theorem c3355_iso   : LeafIso 3355    := by decide +kernel
private theorem c3355_nof2  : NoF2ChkSq 3355  := by decide +kernel
private theorem c3355_nof3  : NoF3ChkSq 3355  := by decide +kernel
private theorem c3355_nof4z : NoF4zChkSq 3355 := by decide +kernel
theorem C'_3355 : C' 3355 :=
  ⟨c3355_sqf, c3355_range, c3355_ell, leafNSq_of_sq c3355_nsq, leafHAr_of_sq c3355_har,
   c3355_r, c3355_e', c3355_f1, leafS2_of_sq c3355_s2, leafS3_of_sq c3355_s3,
   c3355_iso, leafR8_of_sq c3355_nof2 c3355_nof3 c3355_nof4z⟩
theorem not_tile'_3355 (D : CongruentDissection 3355) : False :=
  not_tile_of_conditions' 3355 C'_3355 D

private theorem c3358_sqf   : LeafSqf 3358   := by decide +kernel
private theorem c3358_range : LeafRange 3358  := by decide +kernel
private theorem c3358_ell   : LeafEll 3358    := by decide +kernel
private theorem c3358_nsq   : NSqChkSq 3358   := by decide +kernel
private theorem c3358_har   : HArithChkSq 3358 := by decide +kernel
private theorem c3358_r     : LeafR 3358      := by decide +kernel
private theorem c3358_e'    : LeafE' 3358     := by decide +kernel
private theorem c3358_f1    : LeafF1 3358     := Or.inl (by decide)
private theorem c3358_s2    : S2ChkSq 3358    := by decide +kernel
private theorem c3358_s3    : S3ChkSq 3358    := by decide +kernel
private theorem c3358_iso   : LeafIso 3358    := by decide +kernel
private theorem c3358_nof2  : NoF2ChkSq 3358  := by decide +kernel
private theorem c3358_nof3  : NoF3ChkSq 3358  := by decide +kernel
private theorem c3358_nof4z : NoF4zChkSq 3358 := by decide +kernel
theorem C'_3358 : C' 3358 :=
  ⟨c3358_sqf, c3358_range, c3358_ell, leafNSq_of_sq c3358_nsq, leafHAr_of_sq c3358_har,
   c3358_r, c3358_e', c3358_f1, leafS2_of_sq c3358_s2, leafS3_of_sq c3358_s3,
   c3358_iso, leafR8_of_sq c3358_nof2 c3358_nof3 c3358_nof4z⟩
theorem not_tile'_3358 (D : CongruentDissection 3358) : False :=
  not_tile_of_conditions' 3358 C'_3358 D

private theorem c3359_sqf   : LeafSqf 3359   := by decide +kernel
private theorem c3359_range : LeafRange 3359  := by decide +kernel
private theorem c3359_ell   : LeafEll 3359    := by decide +kernel
private theorem c3359_nsq   : NSqChkSq 3359   := by decide +kernel
private theorem c3359_har   : HArithChkSq 3359 := by decide +kernel
private theorem c3359_r     : LeafR 3359      := by decide +kernel
private theorem c3359_e'    : LeafE' 3359     := by decide +kernel
private theorem c3359_f1    : LeafF1 3359     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3359_s2    : S2ChkSq 3359    := by decide +kernel
private theorem c3359_s3    : S3ChkSq 3359    := by decide +kernel
private theorem c3359_iso   : LeafIso 3359    := by decide +kernel
private theorem c3359_nof2  : NoF2ChkSq 3359  := by decide +kernel
private theorem c3359_nof3  : NoF3ChkSq 3359  := by decide +kernel
private theorem c3359_nof4z : NoF4zChkSq 3359 := by decide +kernel
theorem C'_3359 : C' 3359 :=
  ⟨c3359_sqf, c3359_range, c3359_ell, leafNSq_of_sq c3359_nsq, leafHAr_of_sq c3359_har,
   c3359_r, c3359_e', c3359_f1, leafS2_of_sq c3359_s2, leafS3_of_sq c3359_s3,
   c3359_iso, leafR8_of_sq c3359_nof2 c3359_nof3 c3359_nof4z⟩
theorem not_tile'_3359 (D : CongruentDissection 3359) : False :=
  not_tile_of_conditions' 3359 C'_3359 D

private theorem c3367_sqf   : LeafSqf 3367   := by decide +kernel
private theorem c3367_range : LeafRange 3367  := by decide +kernel
private theorem c3367_ell   : LeafEll 3367    := by decide +kernel
private theorem c3367_nsq   : NSqChkSq 3367   := by decide +kernel
private theorem c3367_har   : HArithChkSq 3367 := by decide +kernel
private theorem c3367_r     : LeafR 3367      := by decide +kernel
private theorem c3367_e'    : LeafE' 3367     := by decide +kernel
private theorem c3367_f1    : LeafF1 3367     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3367_s2    : S2ChkSq 3367    := by decide +kernel
private theorem c3367_s3    : S3ChkSq 3367    := by decide +kernel
private theorem c3367_iso   : LeafIso 3367    := by decide +kernel
private theorem c3367_nof2  : NoF2ChkSq 3367  := by decide +kernel
private theorem c3367_nof3  : NoF3ChkSq 3367  := by decide +kernel
private theorem c3367_nof4z : NoF4zChkSq 3367 := by decide +kernel
theorem C'_3367 : C' 3367 :=
  ⟨c3367_sqf, c3367_range, c3367_ell, leafNSq_of_sq c3367_nsq, leafHAr_of_sq c3367_har,
   c3367_r, c3367_e', c3367_f1, leafS2_of_sq c3367_s2, leafS3_of_sq c3367_s3,
   c3367_iso, leafR8_of_sq c3367_nof2 c3367_nof3 c3367_nof4z⟩
theorem not_tile'_3367 (D : CongruentDissection 3367) : False :=
  not_tile_of_conditions' 3367 C'_3367 D

end Erdos634.Draft.AllN2

/- AllN2Check157: N = 3342, 3343, 3346, 3347, 3351
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3342_sqf   : LeafSqf 3342   := by decide +kernel
private theorem c3342_range : LeafRange 3342  := by decide +kernel
private theorem c3342_ell   : LeafEll 3342    := by decide +kernel
private theorem c3342_nsq   : NSqChkSq 3342   := by decide +kernel
private theorem c3342_har   : HArithChkSq 3342 := by decide +kernel
private theorem c3342_r     : LeafR 3342      := by decide +kernel
private theorem c3342_e'    : LeafE' 3342     := by decide +kernel
private theorem c3342_f1    : LeafF1 3342     := Or.inl (by decide)
private theorem c3342_s2    : S2ChkSq 3342    := by decide +kernel
private theorem c3342_s3    : S3ChkSq 3342    := by decide +kernel
private theorem c3342_iso   : LeafIso 3342    := by decide +kernel
private theorem c3342_nof2  : NoF2ChkSq 3342  := by decide +kernel
private theorem c3342_nof3  : NoF3ChkSq 3342  := by decide +kernel
private theorem c3342_nof4z : NoF4zChkSq 3342 := by decide +kernel
theorem C'_3342 : C' 3342 :=
  ⟨c3342_sqf, c3342_range, c3342_ell, leafNSq_of_sq c3342_nsq, leafHAr_of_sq c3342_har,
   c3342_r, c3342_e', c3342_f1, leafS2_of_sq c3342_s2, leafS3_of_sq c3342_s3,
   c3342_iso, leafR8_of_sq c3342_nof2 c3342_nof3 c3342_nof4z⟩
theorem not_tile'_3342 (D : CongruentDissection 3342) : False :=
  not_tile_of_conditions' 3342 C'_3342 D

private theorem c3343_sqf   : LeafSqf 3343   := by decide +kernel
private theorem c3343_range : LeafRange 3343  := by decide +kernel
private theorem c3343_ell   : LeafEll 3343    := by decide +kernel
private theorem c3343_nsq   : NSqChkSq 3343   := by decide +kernel
private theorem c3343_har   : HArithChkSq 3343 := by decide +kernel
private theorem c3343_r     : LeafR 3343      := by decide +kernel
private theorem c3343_e'    : LeafE' 3343     := by decide +kernel
private theorem c3343_f1    : LeafF1 3343     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3343_s2    : S2ChkSq 3343    := by decide +kernel
private theorem c3343_s3    : S3ChkSq 3343    := by decide +kernel
private theorem c3343_iso   : LeafIso 3343    := by decide +kernel
private theorem c3343_nof2  : NoF2ChkSq 3343  := by decide +kernel
private theorem c3343_nof3  : NoF3ChkSq 3343  := by decide +kernel
private theorem c3343_nof4z : NoF4zChkSq 3343 := by decide +kernel
theorem C'_3343 : C' 3343 :=
  ⟨c3343_sqf, c3343_range, c3343_ell, leafNSq_of_sq c3343_nsq, leafHAr_of_sq c3343_har,
   c3343_r, c3343_e', c3343_f1, leafS2_of_sq c3343_s2, leafS3_of_sq c3343_s3,
   c3343_iso, leafR8_of_sq c3343_nof2 c3343_nof3 c3343_nof4z⟩
theorem not_tile'_3343 (D : CongruentDissection 3343) : False :=
  not_tile_of_conditions' 3343 C'_3343 D

private theorem c3346_sqf   : LeafSqf 3346   := by decide +kernel
private theorem c3346_range : LeafRange 3346  := by decide +kernel
private theorem c3346_ell   : LeafEll 3346    := by decide +kernel
private theorem c3346_nsq   : NSqChkSq 3346   := by decide +kernel
private theorem c3346_har   : HArithChkSq 3346 := by decide +kernel
private theorem c3346_r     : LeafR 3346      := by decide +kernel
private theorem c3346_e'    : LeafE' 3346     := by decide +kernel
private theorem c3346_f1    : LeafF1 3346     := Or.inl (by decide)
private theorem c3346_s2    : S2ChkSq 3346    := by decide +kernel
private theorem c3346_s3    : S3ChkSq 3346    := by decide +kernel
private theorem c3346_iso   : LeafIso 3346    := by decide +kernel
private theorem c3346_nof2  : NoF2ChkSq 3346  := by decide +kernel
private theorem c3346_nof3  : NoF3ChkSq 3346  := by decide +kernel
private theorem c3346_nof4z : NoF4zChkSq 3346 := by decide +kernel
theorem C'_3346 : C' 3346 :=
  ⟨c3346_sqf, c3346_range, c3346_ell, leafNSq_of_sq c3346_nsq, leafHAr_of_sq c3346_har,
   c3346_r, c3346_e', c3346_f1, leafS2_of_sq c3346_s2, leafS3_of_sq c3346_s3,
   c3346_iso, leafR8_of_sq c3346_nof2 c3346_nof3 c3346_nof4z⟩
theorem not_tile'_3346 (D : CongruentDissection 3346) : False :=
  not_tile_of_conditions' 3346 C'_3346 D

private theorem c3347_sqf   : LeafSqf 3347   := by decide +kernel
private theorem c3347_range : LeafRange 3347  := by decide +kernel
private theorem c3347_ell   : LeafEll 3347    := by decide +kernel
private theorem c3347_nsq   : NSqChkSq 3347   := by decide +kernel
private theorem c3347_har   : HArithChkSq 3347 := by decide +kernel
private theorem c3347_r     : LeafR 3347      := by decide +kernel
private theorem c3347_e'    : LeafE' 3347     := by decide +kernel
private theorem c3347_f1    : LeafF1 3347     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3347_s2    : S2ChkSq 3347    := by decide +kernel
private theorem c3347_s3    : S3ChkSq 3347    := by decide +kernel
private theorem c3347_iso   : LeafIso 3347    := by decide +kernel
private theorem c3347_nof2  : NoF2ChkSq 3347  := by decide +kernel
private theorem c3347_nof3  : NoF3ChkSq 3347  := by decide +kernel
private theorem c3347_nof4z : NoF4zChkSq 3347 := by decide +kernel
theorem C'_3347 : C' 3347 :=
  ⟨c3347_sqf, c3347_range, c3347_ell, leafNSq_of_sq c3347_nsq, leafHAr_of_sq c3347_har,
   c3347_r, c3347_e', c3347_f1, leafS2_of_sq c3347_s2, leafS3_of_sq c3347_s3,
   c3347_iso, leafR8_of_sq c3347_nof2 c3347_nof3 c3347_nof4z⟩
theorem not_tile'_3347 (D : CongruentDissection 3347) : False :=
  not_tile_of_conditions' 3347 C'_3347 D

private theorem c3351_sqf   : LeafSqf 3351   := by decide +kernel
private theorem c3351_range : LeafRange 3351  := by decide +kernel
private theorem c3351_ell   : LeafEll 3351    := by decide +kernel
private theorem c3351_nsq   : NSqChkSq 3351   := by decide +kernel
private theorem c3351_har   : HArithChkSq 3351 := by decide +kernel
private theorem c3351_r     : LeafR 3351      := by decide +kernel
private theorem c3351_e'    : LeafE' 3351     := by decide +kernel
private theorem c3351_f1    : LeafF1 3351     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3351_s2    : S2ChkSq 3351    := by decide +kernel
private theorem c3351_s3    : S3ChkSq 3351    := by decide +kernel
private theorem c3351_iso   : LeafIso 3351    := by decide +kernel
private theorem c3351_nof2  : NoF2ChkSq 3351  := by decide +kernel
private theorem c3351_nof3  : NoF3ChkSq 3351  := by decide +kernel
private theorem c3351_nof4z : NoF4zChkSq 3351 := by decide +kernel
theorem C'_3351 : C' 3351 :=
  ⟨c3351_sqf, c3351_range, c3351_ell, leafNSq_of_sq c3351_nsq, leafHAr_of_sq c3351_har,
   c3351_r, c3351_e', c3351_f1, leafS2_of_sq c3351_s2, leafS3_of_sq c3351_s3,
   c3351_iso, leafR8_of_sq c3351_nof2 c3351_nof3 c3351_nof4z⟩
theorem not_tile'_3351 (D : CongruentDissection 3351) : False :=
  not_tile_of_conditions' 3351 C'_3351 D

end Erdos634.Draft.AllN2

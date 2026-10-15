/- AllN2Check234: N = 4343, 4345, 4351, 4353, 4354
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4343_sqf   : LeafSqf 4343   := by decide +kernel
private theorem c4343_range : LeafRange 4343  := by decide +kernel
private theorem c4343_ell   : LeafEll 4343    := by decide +kernel
private theorem c4343_nsq   : NSqChkSq 4343   := by decide +kernel
private theorem c4343_har   : HArithChkSq 4343 := by decide +kernel
private theorem c4343_r     : LeafR 4343      := by decide +kernel
private theorem c4343_e'    : LeafE' 4343     := by decide +kernel
private theorem c4343_f1    : LeafF1 4343     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4343_s2    : S2ChkSq 4343    := by decide +kernel
private theorem c4343_s3    : S3ChkSq 4343    := by decide +kernel
private theorem c4343_iso   : LeafIso 4343    := by decide +kernel
private theorem c4343_nof2  : NoF2ChkSq 4343  := by decide +kernel
private theorem c4343_nof3  : NoF3ChkSq 4343  := by decide +kernel
private theorem c4343_nof4z : NoF4zChkSq 4343 := by decide +kernel
theorem C'_4343 : C' 4343 :=
  ⟨c4343_sqf, c4343_range, c4343_ell, leafNSq_of_sq c4343_nsq, leafHAr_of_sq c4343_har,
   c4343_r, c4343_e', c4343_f1, leafS2_of_sq c4343_s2, leafS3_of_sq c4343_s3,
   c4343_iso, leafR8_of_sq c4343_nof2 c4343_nof3 c4343_nof4z⟩
theorem not_tile'_4343 (D : CongruentDissection 4343) : False :=
  not_tile_of_conditions' 4343 C'_4343 D

private theorem c4345_sqf   : LeafSqf 4345   := by decide +kernel
private theorem c4345_range : LeafRange 4345  := by decide +kernel
private theorem c4345_ell   : LeafEll 4345    := by decide +kernel
private theorem c4345_nsq   : NSqChkSq 4345   := by decide +kernel
private theorem c4345_har   : HArithChkSq 4345 := by decide +kernel
private theorem c4345_r     : LeafR 4345      := by decide +kernel
private theorem c4345_e'    : LeafE' 4345     := by decide +kernel
private theorem c4345_f1    : LeafF1 4345     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4345_s2    : S2ChkSq 4345    := by decide +kernel
private theorem c4345_s3    : S3ChkSq 4345    := by decide +kernel
private theorem c4345_iso   : LeafIso 4345    := by decide +kernel
private theorem c4345_nof2  : NoF2ChkSq 4345  := by decide +kernel
private theorem c4345_nof3  : NoF3ChkSq 4345  := by decide +kernel
private theorem c4345_nof4z : NoF4zChkSq 4345 := by decide +kernel
theorem C'_4345 : C' 4345 :=
  ⟨c4345_sqf, c4345_range, c4345_ell, leafNSq_of_sq c4345_nsq, leafHAr_of_sq c4345_har,
   c4345_r, c4345_e', c4345_f1, leafS2_of_sq c4345_s2, leafS3_of_sq c4345_s3,
   c4345_iso, leafR8_of_sq c4345_nof2 c4345_nof3 c4345_nof4z⟩
theorem not_tile'_4345 (D : CongruentDissection 4345) : False :=
  not_tile_of_conditions' 4345 C'_4345 D

private theorem c4351_sqf   : LeafSqf 4351   := by decide +kernel
private theorem c4351_range : LeafRange 4351  := by decide +kernel
private theorem c4351_ell   : LeafEll 4351    := by decide +kernel
private theorem c4351_nsq   : NSqChkSq 4351   := by decide +kernel
private theorem c4351_har   : HArithChkSq 4351 := by decide +kernel
private theorem c4351_r     : LeafR 4351      := by decide +kernel
private theorem c4351_e'    : LeafE' 4351     := by decide +kernel
private theorem c4351_f1    : LeafF1 4351     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4351_s2    : S2ChkSq 4351    := by decide +kernel
private theorem c4351_s3    : S3ChkSq 4351    := by decide +kernel
private theorem c4351_iso   : LeafIso 4351    := by decide +kernel
private theorem c4351_nof2  : NoF2ChkSq 4351  := by decide +kernel
private theorem c4351_nof3  : NoF3ChkSq 4351  := by decide +kernel
private theorem c4351_nof4z : NoF4zChkSq 4351 := by decide +kernel
theorem C'_4351 : C' 4351 :=
  ⟨c4351_sqf, c4351_range, c4351_ell, leafNSq_of_sq c4351_nsq, leafHAr_of_sq c4351_har,
   c4351_r, c4351_e', c4351_f1, leafS2_of_sq c4351_s2, leafS3_of_sq c4351_s3,
   c4351_iso, leafR8_of_sq c4351_nof2 c4351_nof3 c4351_nof4z⟩
theorem not_tile'_4351 (D : CongruentDissection 4351) : False :=
  not_tile_of_conditions' 4351 C'_4351 D

private theorem c4353_sqf   : LeafSqf 4353   := by decide +kernel
private theorem c4353_range : LeafRange 4353  := by decide +kernel
private theorem c4353_ell   : LeafEll 4353    := by decide +kernel
private theorem c4353_nsq   : NSqChkSq 4353   := by decide +kernel
private theorem c4353_har   : HArithChkSq 4353 := by decide +kernel
private theorem c4353_r     : LeafR 4353      := by decide +kernel
private theorem c4353_e'    : LeafE' 4353     := by decide +kernel
private theorem c4353_f1    : LeafF1 4353     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4353_s2    : S2ChkSq 4353    := by decide +kernel
private theorem c4353_s3    : S3ChkSq 4353    := by decide +kernel
private theorem c4353_iso   : LeafIso 4353    := by decide +kernel
private theorem c4353_nof2  : NoF2ChkSq 4353  := by decide +kernel
private theorem c4353_nof3  : NoF3ChkSq 4353  := by decide +kernel
private theorem c4353_nof4z : NoF4zChkSq 4353 := by decide +kernel
theorem C'_4353 : C' 4353 :=
  ⟨c4353_sqf, c4353_range, c4353_ell, leafNSq_of_sq c4353_nsq, leafHAr_of_sq c4353_har,
   c4353_r, c4353_e', c4353_f1, leafS2_of_sq c4353_s2, leafS3_of_sq c4353_s3,
   c4353_iso, leafR8_of_sq c4353_nof2 c4353_nof3 c4353_nof4z⟩
theorem not_tile'_4353 (D : CongruentDissection 4353) : False :=
  not_tile_of_conditions' 4353 C'_4353 D

private theorem c4354_sqf   : LeafSqf 4354   := by decide +kernel
private theorem c4354_range : LeafRange 4354  := by decide +kernel
private theorem c4354_ell   : LeafEll 4354    := by decide +kernel
private theorem c4354_nsq   : NSqChkSq 4354   := by decide +kernel
private theorem c4354_har   : HArithChkSq 4354 := by decide +kernel
private theorem c4354_r     : LeafR 4354      := by decide +kernel
private theorem c4354_e'    : LeafE' 4354     := by decide +kernel
private theorem c4354_f1    : LeafF1 4354     := Or.inl (by decide)
private theorem c4354_s2    : S2ChkSq 4354    := by decide +kernel
private theorem c4354_s3    : S3ChkSq 4354    := by decide +kernel
private theorem c4354_iso   : LeafIso 4354    := by decide +kernel
private theorem c4354_nof2  : NoF2ChkSq 4354  := by decide +kernel
private theorem c4354_nof3  : NoF3ChkSq 4354  := by decide +kernel
private theorem c4354_nof4z : NoF4zChkSq 4354 := by decide +kernel
theorem C'_4354 : C' 4354 :=
  ⟨c4354_sqf, c4354_range, c4354_ell, leafNSq_of_sq c4354_nsq, leafHAr_of_sq c4354_har,
   c4354_r, c4354_e', c4354_f1, leafS2_of_sq c4354_s2, leafS3_of_sq c4354_s3,
   c4354_iso, leafR8_of_sq c4354_nof2 c4354_nof3 c4354_nof4z⟩
theorem not_tile'_4354 (D : CongruentDissection 4354) : False :=
  not_tile_of_conditions' 4354 C'_4354 D

end Erdos634.Draft.AllN2

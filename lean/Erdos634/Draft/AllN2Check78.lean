/- AllN2Check78: N = 2342, 2345, 2347, 2351, 2354
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2342_sqf   : LeafSqf 2342   := by decide +kernel
private theorem c2342_range : LeafRange 2342  := by decide +kernel
private theorem c2342_ell   : LeafEll 2342    := by decide +kernel
private theorem c2342_nsq   : NSqChkSq 2342   := by decide +kernel
private theorem c2342_har   : HArithChkSq 2342 := by decide +kernel
private theorem c2342_r     : LeafR 2342      := by decide +kernel
private theorem c2342_e'    : LeafE' 2342     := by decide +kernel
private theorem c2342_f1    : LeafF1 2342     := Or.inl (by decide)
private theorem c2342_s2    : S2ChkSq 2342    := by decide +kernel
private theorem c2342_s3    : S3ChkSq 2342    := by decide +kernel
private theorem c2342_iso   : LeafIso 2342    := by decide +kernel
private theorem c2342_nof2  : NoF2ChkSq 2342  := by decide +kernel
private theorem c2342_nof3  : NoF3ChkSq 2342  := by decide +kernel
private theorem c2342_nof4z : NoF4zChkSq 2342 := by decide +kernel
theorem C'_2342 : C' 2342 :=
  ⟨c2342_sqf, c2342_range, c2342_ell, leafNSq_of_sq c2342_nsq, leafHAr_of_sq c2342_har,
   c2342_r, c2342_e', c2342_f1, leafS2_of_sq c2342_s2, leafS3_of_sq c2342_s3,
   c2342_iso, leafR8_of_sq c2342_nof2 c2342_nof3 c2342_nof4z⟩
theorem not_tile'_2342 (D : CongruentDissection 2342) : False :=
  not_tile_of_conditions' 2342 C'_2342 D

private theorem c2345_sqf   : LeafSqf 2345   := by decide +kernel
private theorem c2345_range : LeafRange 2345  := by decide +kernel
private theorem c2345_ell   : LeafEll 2345    := by decide +kernel
private theorem c2345_nsq   : NSqChkSq 2345   := by decide +kernel
private theorem c2345_har   : HArithChkSq 2345 := by decide +kernel
private theorem c2345_r     : LeafR 2345      := by decide +kernel
private theorem c2345_e'    : LeafE' 2345     := by decide +kernel
private theorem c2345_f1    : LeafF1 2345     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2345_s2    : S2ChkSq 2345    := by decide +kernel
private theorem c2345_s3    : S3ChkSq 2345    := by decide +kernel
private theorem c2345_iso   : LeafIso 2345    := by decide +kernel
private theorem c2345_nof2  : NoF2ChkSq 2345  := by decide +kernel
private theorem c2345_nof3  : NoF3ChkSq 2345  := by decide +kernel
private theorem c2345_nof4z : NoF4zChkSq 2345 := by decide +kernel
theorem C'_2345 : C' 2345 :=
  ⟨c2345_sqf, c2345_range, c2345_ell, leafNSq_of_sq c2345_nsq, leafHAr_of_sq c2345_har,
   c2345_r, c2345_e', c2345_f1, leafS2_of_sq c2345_s2, leafS3_of_sq c2345_s3,
   c2345_iso, leafR8_of_sq c2345_nof2 c2345_nof3 c2345_nof4z⟩
theorem not_tile'_2345 (D : CongruentDissection 2345) : False :=
  not_tile_of_conditions' 2345 C'_2345 D

private theorem c2347_sqf   : LeafSqf 2347   := by decide +kernel
private theorem c2347_range : LeafRange 2347  := by decide +kernel
private theorem c2347_ell   : LeafEll 2347    := by decide +kernel
private theorem c2347_nsq   : NSqChkSq 2347   := by decide +kernel
private theorem c2347_har   : HArithChkSq 2347 := by decide +kernel
private theorem c2347_r     : LeafR 2347      := by decide +kernel
private theorem c2347_e'    : LeafE' 2347     := by decide +kernel
private theorem c2347_f1    : LeafF1 2347     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2347_s2    : S2ChkSq 2347    := by decide +kernel
private theorem c2347_s3    : S3ChkSq 2347    := by decide +kernel
private theorem c2347_iso   : LeafIso 2347    := by decide +kernel
private theorem c2347_nof2  : NoF2ChkSq 2347  := by decide +kernel
private theorem c2347_nof3  : NoF3ChkSq 2347  := by decide +kernel
private theorem c2347_nof4z : NoF4zChkSq 2347 := by decide +kernel
theorem C'_2347 : C' 2347 :=
  ⟨c2347_sqf, c2347_range, c2347_ell, leafNSq_of_sq c2347_nsq, leafHAr_of_sq c2347_har,
   c2347_r, c2347_e', c2347_f1, leafS2_of_sq c2347_s2, leafS3_of_sq c2347_s3,
   c2347_iso, leafR8_of_sq c2347_nof2 c2347_nof3 c2347_nof4z⟩
theorem not_tile'_2347 (D : CongruentDissection 2347) : False :=
  not_tile_of_conditions' 2347 C'_2347 D

private theorem c2351_sqf   : LeafSqf 2351   := by decide +kernel
private theorem c2351_range : LeafRange 2351  := by decide +kernel
private theorem c2351_ell   : LeafEll 2351    := by decide +kernel
private theorem c2351_nsq   : NSqChkSq 2351   := by decide +kernel
private theorem c2351_har   : HArithChkSq 2351 := by decide +kernel
private theorem c2351_r     : LeafR 2351      := by decide +kernel
private theorem c2351_e'    : LeafE' 2351     := by decide +kernel
private theorem c2351_f1    : LeafF1 2351     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2351_s2    : S2ChkSq 2351    := by decide +kernel
private theorem c2351_s3    : S3ChkSq 2351    := by decide +kernel
private theorem c2351_iso   : LeafIso 2351    := by decide +kernel
private theorem c2351_nof2  : NoF2ChkSq 2351  := by decide +kernel
private theorem c2351_nof3  : NoF3ChkSq 2351  := by decide +kernel
private theorem c2351_nof4z : NoF4zChkSq 2351 := by decide +kernel
theorem C'_2351 : C' 2351 :=
  ⟨c2351_sqf, c2351_range, c2351_ell, leafNSq_of_sq c2351_nsq, leafHAr_of_sq c2351_har,
   c2351_r, c2351_e', c2351_f1, leafS2_of_sq c2351_s2, leafS3_of_sq c2351_s3,
   c2351_iso, leafR8_of_sq c2351_nof2 c2351_nof3 c2351_nof4z⟩
theorem not_tile'_2351 (D : CongruentDissection 2351) : False :=
  not_tile_of_conditions' 2351 C'_2351 D

private theorem c2354_sqf   : LeafSqf 2354   := by decide +kernel
private theorem c2354_range : LeafRange 2354  := by decide +kernel
private theorem c2354_ell   : LeafEll 2354    := by decide +kernel
private theorem c2354_nsq   : NSqChkSq 2354   := by decide +kernel
private theorem c2354_har   : HArithChkSq 2354 := by decide +kernel
private theorem c2354_r     : LeafR 2354      := by decide +kernel
private theorem c2354_e'    : LeafE' 2354     := by decide +kernel
private theorem c2354_f1    : LeafF1 2354     := Or.inl (by decide)
private theorem c2354_s2    : S2ChkSq 2354    := by decide +kernel
private theorem c2354_s3    : S3ChkSq 2354    := by decide +kernel
private theorem c2354_iso   : LeafIso 2354    := by decide +kernel
private theorem c2354_nof2  : NoF2ChkSq 2354  := by decide +kernel
private theorem c2354_nof3  : NoF3ChkSq 2354  := by decide +kernel
private theorem c2354_nof4z : NoF4zChkSq 2354 := by decide +kernel
theorem C'_2354 : C' 2354 :=
  ⟨c2354_sqf, c2354_range, c2354_ell, leafNSq_of_sq c2354_nsq, leafHAr_of_sq c2354_har,
   c2354_r, c2354_e', c2354_f1, leafS2_of_sq c2354_s2, leafS3_of_sq c2354_s3,
   c2354_iso, leafR8_of_sq c2354_nof2 c2354_nof3 c2354_nof4z⟩
theorem not_tile'_2354 (D : CongruentDissection 2354) : False :=
  not_tile_of_conditions' 2354 C'_2354 D

end Erdos634.Draft.AllN2

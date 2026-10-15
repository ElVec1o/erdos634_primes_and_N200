/- AllN2Check93: N = 2518, 2519, 2526, 2530, 2531
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2518_sqf   : LeafSqf 2518   := by decide +kernel
private theorem c2518_range : LeafRange 2518  := by decide +kernel
private theorem c2518_ell   : LeafEll 2518    := by decide +kernel
private theorem c2518_nsq   : NSqChkSq 2518   := by decide +kernel
private theorem c2518_har   : HArithChkSq 2518 := by decide +kernel
private theorem c2518_r     : LeafR 2518      := by decide +kernel
private theorem c2518_e'    : LeafE' 2518     := by decide +kernel
private theorem c2518_f1    : LeafF1 2518     := Or.inl (by decide)
private theorem c2518_s2    : S2ChkSq 2518    := by decide +kernel
private theorem c2518_s3    : S3ChkSq 2518    := by decide +kernel
private theorem c2518_iso   : LeafIso 2518    := by decide +kernel
private theorem c2518_nof2  : NoF2ChkSq 2518  := by decide +kernel
private theorem c2518_nof3  : NoF3ChkSq 2518  := by decide +kernel
private theorem c2518_nof4z : NoF4zChkSq 2518 := by decide +kernel
theorem C'_2518 : C' 2518 :=
  ⟨c2518_sqf, c2518_range, c2518_ell, leafNSq_of_sq c2518_nsq, leafHAr_of_sq c2518_har,
   c2518_r, c2518_e', c2518_f1, leafS2_of_sq c2518_s2, leafS3_of_sq c2518_s3,
   c2518_iso, leafR8_of_sq c2518_nof2 c2518_nof3 c2518_nof4z⟩
theorem not_tile'_2518 (D : CongruentDissection 2518) : False :=
  not_tile_of_conditions' 2518 C'_2518 D

private theorem c2519_sqf   : LeafSqf 2519   := by decide +kernel
private theorem c2519_range : LeafRange 2519  := by decide +kernel
private theorem c2519_ell   : LeafEll 2519    := by decide +kernel
private theorem c2519_nsq   : NSqChkSq 2519   := by decide +kernel
private theorem c2519_har   : HArithChkSq 2519 := by decide +kernel
private theorem c2519_r     : LeafR 2519      := by decide +kernel
private theorem c2519_e'    : LeafE' 2519     := by decide +kernel
private theorem c2519_f1    : LeafF1 2519     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2519_s2    : S2ChkSq 2519    := by decide +kernel
private theorem c2519_s3    : S3ChkSq 2519    := by decide +kernel
private theorem c2519_iso   : LeafIso 2519    := by decide +kernel
private theorem c2519_nof2  : NoF2ChkSq 2519  := by decide +kernel
private theorem c2519_nof3  : NoF3ChkSq 2519  := by decide +kernel
private theorem c2519_nof4z : NoF4zChkSq 2519 := by decide +kernel
theorem C'_2519 : C' 2519 :=
  ⟨c2519_sqf, c2519_range, c2519_ell, leafNSq_of_sq c2519_nsq, leafHAr_of_sq c2519_har,
   c2519_r, c2519_e', c2519_f1, leafS2_of_sq c2519_s2, leafS3_of_sq c2519_s3,
   c2519_iso, leafR8_of_sq c2519_nof2 c2519_nof3 c2519_nof4z⟩
theorem not_tile'_2519 (D : CongruentDissection 2519) : False :=
  not_tile_of_conditions' 2519 C'_2519 D

private theorem c2526_sqf   : LeafSqf 2526   := by decide +kernel
private theorem c2526_range : LeafRange 2526  := by decide +kernel
private theorem c2526_ell   : LeafEll 2526    := by decide +kernel
private theorem c2526_nsq   : NSqChkSq 2526   := by decide +kernel
private theorem c2526_har   : HArithChkSq 2526 := by decide +kernel
private theorem c2526_r     : LeafR 2526      := by decide +kernel
private theorem c2526_e'    : LeafE' 2526     := by decide +kernel
private theorem c2526_f1    : LeafF1 2526     := Or.inl (by decide)
private theorem c2526_s2    : S2ChkSq 2526    := by decide +kernel
private theorem c2526_s3    : S3ChkSq 2526    := by decide +kernel
private theorem c2526_iso   : LeafIso 2526    := by decide +kernel
private theorem c2526_nof2  : NoF2ChkSq 2526  := by decide +kernel
private theorem c2526_nof3  : NoF3ChkSq 2526  := by decide +kernel
private theorem c2526_nof4z : NoF4zChkSq 2526 := by decide +kernel
theorem C'_2526 : C' 2526 :=
  ⟨c2526_sqf, c2526_range, c2526_ell, leafNSq_of_sq c2526_nsq, leafHAr_of_sq c2526_har,
   c2526_r, c2526_e', c2526_f1, leafS2_of_sq c2526_s2, leafS3_of_sq c2526_s3,
   c2526_iso, leafR8_of_sq c2526_nof2 c2526_nof3 c2526_nof4z⟩
theorem not_tile'_2526 (D : CongruentDissection 2526) : False :=
  not_tile_of_conditions' 2526 C'_2526 D

private theorem c2530_sqf   : LeafSqf 2530   := by decide +kernel
private theorem c2530_range : LeafRange 2530  := by decide +kernel
private theorem c2530_ell   : LeafEll 2530    := by decide +kernel
private theorem c2530_nsq   : NSqChkSq 2530   := by decide +kernel
private theorem c2530_har   : HArithChkSq 2530 := by decide +kernel
private theorem c2530_r     : LeafR 2530      := by decide +kernel
private theorem c2530_e'    : LeafE' 2530     := by decide +kernel
private theorem c2530_f1    : LeafF1 2530     := Or.inl (by decide)
private theorem c2530_s2    : S2ChkSq 2530    := by decide +kernel
private theorem c2530_s3    : S3ChkSq 2530    := by decide +kernel
private theorem c2530_iso   : LeafIso 2530    := by decide +kernel
private theorem c2530_nof2  : NoF2ChkSq 2530  := by decide +kernel
private theorem c2530_nof3  : NoF3ChkSq 2530  := by decide +kernel
private theorem c2530_nof4z : NoF4zChkSq 2530 := by decide +kernel
theorem C'_2530 : C' 2530 :=
  ⟨c2530_sqf, c2530_range, c2530_ell, leafNSq_of_sq c2530_nsq, leafHAr_of_sq c2530_har,
   c2530_r, c2530_e', c2530_f1, leafS2_of_sq c2530_s2, leafS3_of_sq c2530_s3,
   c2530_iso, leafR8_of_sq c2530_nof2 c2530_nof3 c2530_nof4z⟩
theorem not_tile'_2530 (D : CongruentDissection 2530) : False :=
  not_tile_of_conditions' 2530 C'_2530 D

private theorem c2531_sqf   : LeafSqf 2531   := by decide +kernel
private theorem c2531_range : LeafRange 2531  := by decide +kernel
private theorem c2531_ell   : LeafEll 2531    := by decide +kernel
private theorem c2531_nsq   : NSqChkSq 2531   := by decide +kernel
private theorem c2531_har   : HArithChkSq 2531 := by decide +kernel
private theorem c2531_r     : LeafR 2531      := by decide +kernel
private theorem c2531_e'    : LeafE' 2531     := by decide +kernel
private theorem c2531_f1    : LeafF1 2531     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2531_s2    : S2ChkSq 2531    := by decide +kernel
private theorem c2531_s3    : S3ChkSq 2531    := by decide +kernel
private theorem c2531_iso   : LeafIso 2531    := by decide +kernel
private theorem c2531_nof2  : NoF2ChkSq 2531  := by decide +kernel
private theorem c2531_nof3  : NoF3ChkSq 2531  := by decide +kernel
private theorem c2531_nof4z : NoF4zChkSq 2531 := by decide +kernel
theorem C'_2531 : C' 2531 :=
  ⟨c2531_sqf, c2531_range, c2531_ell, leafNSq_of_sq c2531_nsq, leafHAr_of_sq c2531_har,
   c2531_r, c2531_e', c2531_f1, leafS2_of_sq c2531_s2, leafS3_of_sq c2531_s3,
   c2531_iso, leafR8_of_sq c2531_nof2 c2531_nof3 c2531_nof4z⟩
theorem not_tile'_2531 (D : CongruentDissection 2531) : False :=
  not_tile_of_conditions' 2531 C'_2531 D

end Erdos634.Draft.AllN2

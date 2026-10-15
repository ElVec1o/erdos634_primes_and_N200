/- AllN2Check155: N = 3318, 3319, 3322, 3323, 3326
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3318_sqf   : LeafSqf 3318   := by decide +kernel
private theorem c3318_range : LeafRange 3318  := by decide +kernel
private theorem c3318_ell   : LeafEll 3318    := by decide +kernel
private theorem c3318_nsq   : NSqChkSq 3318   := by decide +kernel
private theorem c3318_har   : HArithChkSq 3318 := by decide +kernel
private theorem c3318_r     : LeafR 3318      := by decide +kernel
private theorem c3318_e'    : LeafE' 3318     := by decide +kernel
private theorem c3318_f1    : LeafF1 3318     := Or.inl (by decide)
private theorem c3318_s2    : S2ChkSq 3318    := by decide +kernel
private theorem c3318_s3    : S3ChkSq 3318    := by decide +kernel
private theorem c3318_iso   : LeafIso 3318    := by decide +kernel
private theorem c3318_nof2  : NoF2ChkSq 3318  := by decide +kernel
private theorem c3318_nof3  : NoF3ChkSq 3318  := by decide +kernel
private theorem c3318_nof4z : NoF4zChkSq 3318 := by decide +kernel
theorem C'_3318 : C' 3318 :=
  ⟨c3318_sqf, c3318_range, c3318_ell, leafNSq_of_sq c3318_nsq, leafHAr_of_sq c3318_har,
   c3318_r, c3318_e', c3318_f1, leafS2_of_sq c3318_s2, leafS3_of_sq c3318_s3,
   c3318_iso, leafR8_of_sq c3318_nof2 c3318_nof3 c3318_nof4z⟩
theorem not_tile'_3318 (D : CongruentDissection 3318) : False :=
  not_tile_of_conditions' 3318 C'_3318 D

private theorem c3319_sqf   : LeafSqf 3319   := by decide +kernel
private theorem c3319_range : LeafRange 3319  := by decide +kernel
private theorem c3319_ell   : LeafEll 3319    := by decide +kernel
private theorem c3319_nsq   : NSqChkSq 3319   := by decide +kernel
private theorem c3319_har   : HArithChkSq 3319 := by decide +kernel
private theorem c3319_r     : LeafR 3319      := by decide +kernel
private theorem c3319_e'    : LeafE' 3319     := by decide +kernel
private theorem c3319_f1    : LeafF1 3319     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3319_s2    : S2ChkSq 3319    := by decide +kernel
private theorem c3319_s3    : S3ChkSq 3319    := by decide +kernel
private theorem c3319_iso   : LeafIso 3319    := by decide +kernel
private theorem c3319_nof2  : NoF2ChkSq 3319  := by decide +kernel
private theorem c3319_nof3  : NoF3ChkSq 3319  := by decide +kernel
private theorem c3319_nof4z : NoF4zChkSq 3319 := by decide +kernel
theorem C'_3319 : C' 3319 :=
  ⟨c3319_sqf, c3319_range, c3319_ell, leafNSq_of_sq c3319_nsq, leafHAr_of_sq c3319_har,
   c3319_r, c3319_e', c3319_f1, leafS2_of_sq c3319_s2, leafS3_of_sq c3319_s3,
   c3319_iso, leafR8_of_sq c3319_nof2 c3319_nof3 c3319_nof4z⟩
theorem not_tile'_3319 (D : CongruentDissection 3319) : False :=
  not_tile_of_conditions' 3319 C'_3319 D

private theorem c3322_sqf   : LeafSqf 3322   := by decide +kernel
private theorem c3322_range : LeafRange 3322  := by decide +kernel
private theorem c3322_ell   : LeafEll 3322    := by decide +kernel
private theorem c3322_nsq   : NSqChkSq 3322   := by decide +kernel
private theorem c3322_har   : HArithChkSq 3322 := by decide +kernel
private theorem c3322_r     : LeafR 3322      := by decide +kernel
private theorem c3322_e'    : LeafE' 3322     := by decide +kernel
private theorem c3322_f1    : LeafF1 3322     := Or.inl (by decide)
private theorem c3322_s2    : S2ChkSq 3322    := by decide +kernel
private theorem c3322_s3    : S3ChkSq 3322    := by decide +kernel
private theorem c3322_iso   : LeafIso 3322    := by decide +kernel
private theorem c3322_nof2  : NoF2ChkSq 3322  := by decide +kernel
private theorem c3322_nof3  : NoF3ChkSq 3322  := by decide +kernel
private theorem c3322_nof4z : NoF4zChkSq 3322 := by decide +kernel
theorem C'_3322 : C' 3322 :=
  ⟨c3322_sqf, c3322_range, c3322_ell, leafNSq_of_sq c3322_nsq, leafHAr_of_sq c3322_har,
   c3322_r, c3322_e', c3322_f1, leafS2_of_sq c3322_s2, leafS3_of_sq c3322_s3,
   c3322_iso, leafR8_of_sq c3322_nof2 c3322_nof3 c3322_nof4z⟩
theorem not_tile'_3322 (D : CongruentDissection 3322) : False :=
  not_tile_of_conditions' 3322 C'_3322 D

private theorem c3323_sqf   : LeafSqf 3323   := by decide +kernel
private theorem c3323_range : LeafRange 3323  := by decide +kernel
private theorem c3323_ell   : LeafEll 3323    := by decide +kernel
private theorem c3323_nsq   : NSqChkSq 3323   := by decide +kernel
private theorem c3323_har   : HArithChkSq 3323 := by decide +kernel
private theorem c3323_r     : LeafR 3323      := by decide +kernel
private theorem c3323_e'    : LeafE' 3323     := by decide +kernel
private theorem c3323_f1    : LeafF1 3323     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3323_s2    : S2ChkSq 3323    := by decide +kernel
private theorem c3323_s3    : S3ChkSq 3323    := by decide +kernel
private theorem c3323_iso   : LeafIso 3323    := by decide +kernel
private theorem c3323_nof2  : NoF2ChkSq 3323  := by decide +kernel
private theorem c3323_nof3  : NoF3ChkSq 3323  := by decide +kernel
private theorem c3323_nof4z : NoF4zChkSq 3323 := by decide +kernel
theorem C'_3323 : C' 3323 :=
  ⟨c3323_sqf, c3323_range, c3323_ell, leafNSq_of_sq c3323_nsq, leafHAr_of_sq c3323_har,
   c3323_r, c3323_e', c3323_f1, leafS2_of_sq c3323_s2, leafS3_of_sq c3323_s3,
   c3323_iso, leafR8_of_sq c3323_nof2 c3323_nof3 c3323_nof4z⟩
theorem not_tile'_3323 (D : CongruentDissection 3323) : False :=
  not_tile_of_conditions' 3323 C'_3323 D

private theorem c3326_sqf   : LeafSqf 3326   := by decide +kernel
private theorem c3326_range : LeafRange 3326  := by decide +kernel
private theorem c3326_ell   : LeafEll 3326    := by decide +kernel
private theorem c3326_nsq   : NSqChkSq 3326   := by decide +kernel
private theorem c3326_har   : HArithChkSq 3326 := by decide +kernel
private theorem c3326_r     : LeafR 3326      := by decide +kernel
private theorem c3326_e'    : LeafE' 3326     := by decide +kernel
private theorem c3326_f1    : LeafF1 3326     := Or.inl (by decide)
private theorem c3326_s2    : S2ChkSq 3326    := by decide +kernel
private theorem c3326_s3    : S3ChkSq 3326    := by decide +kernel
private theorem c3326_iso   : LeafIso 3326    := by decide +kernel
private theorem c3326_nof2  : NoF2ChkSq 3326  := by decide +kernel
private theorem c3326_nof3  : NoF3ChkSq 3326  := by decide +kernel
private theorem c3326_nof4z : NoF4zChkSq 3326 := by decide +kernel
theorem C'_3326 : C' 3326 :=
  ⟨c3326_sqf, c3326_range, c3326_ell, leafNSq_of_sq c3326_nsq, leafHAr_of_sq c3326_har,
   c3326_r, c3326_e', c3326_f1, leafS2_of_sq c3326_s2, leafS3_of_sq c3326_s3,
   c3326_iso, leafR8_of_sq c3326_nof2 c3326_nof3 c3326_nof4z⟩
theorem not_tile'_3326 (D : CongruentDissection 3326) : False :=
  not_tile_of_conditions' 3326 C'_3326 D

end Erdos634.Draft.AllN2

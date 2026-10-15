/- AllN2Check232: N = 4318, 4319, 4326, 4327, 4331
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4318_sqf   : LeafSqf 4318   := by decide +kernel
private theorem c4318_range : LeafRange 4318  := by decide +kernel
private theorem c4318_ell   : LeafEll 4318    := by decide +kernel
private theorem c4318_nsq   : NSqChkSq 4318   := by decide +kernel
private theorem c4318_har   : HArithChkSq 4318 := by decide +kernel
private theorem c4318_r     : LeafR 4318      := by decide +kernel
private theorem c4318_e'    : LeafE' 4318     := by decide +kernel
private theorem c4318_f1    : LeafF1 4318     := Or.inl (by decide)
private theorem c4318_s2    : S2ChkSq 4318    := by decide +kernel
private theorem c4318_s3    : S3ChkSq 4318    := by decide +kernel
private theorem c4318_iso   : LeafIso 4318    := by decide +kernel
private theorem c4318_nof2  : NoF2ChkSq 4318  := by decide +kernel
private theorem c4318_nof3  : NoF3ChkSq 4318  := by decide +kernel
private theorem c4318_nof4z : NoF4zChkSq 4318 := by decide +kernel
theorem C'_4318 : C' 4318 :=
  ⟨c4318_sqf, c4318_range, c4318_ell, leafNSq_of_sq c4318_nsq, leafHAr_of_sq c4318_har,
   c4318_r, c4318_e', c4318_f1, leafS2_of_sq c4318_s2, leafS3_of_sq c4318_s3,
   c4318_iso, leafR8_of_sq c4318_nof2 c4318_nof3 c4318_nof4z⟩
theorem not_tile'_4318 (D : CongruentDissection 4318) : False :=
  not_tile_of_conditions' 4318 C'_4318 D

private theorem c4319_sqf   : LeafSqf 4319   := by decide +kernel
private theorem c4319_range : LeafRange 4319  := by decide +kernel
private theorem c4319_ell   : LeafEll 4319    := by decide +kernel
private theorem c4319_nsq   : NSqChkSq 4319   := by decide +kernel
private theorem c4319_har   : HArithChkSq 4319 := by decide +kernel
private theorem c4319_r     : LeafR 4319      := by decide +kernel
private theorem c4319_e'    : LeafE' 4319     := by decide +kernel
private theorem c4319_f1    : LeafF1 4319     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4319_s2    : S2ChkSq 4319    := by decide +kernel
private theorem c4319_s3    : S3ChkSq 4319    := by decide +kernel
private theorem c4319_iso   : LeafIso 4319    := by decide +kernel
private theorem c4319_nof2  : NoF2ChkSq 4319  := by decide +kernel
private theorem c4319_nof3  : NoF3ChkSq 4319  := by decide +kernel
private theorem c4319_nof4z : NoF4zChkSq 4319 := by decide +kernel
theorem C'_4319 : C' 4319 :=
  ⟨c4319_sqf, c4319_range, c4319_ell, leafNSq_of_sq c4319_nsq, leafHAr_of_sq c4319_har,
   c4319_r, c4319_e', c4319_f1, leafS2_of_sq c4319_s2, leafS3_of_sq c4319_s3,
   c4319_iso, leafR8_of_sq c4319_nof2 c4319_nof3 c4319_nof4z⟩
theorem not_tile'_4319 (D : CongruentDissection 4319) : False :=
  not_tile_of_conditions' 4319 C'_4319 D

private theorem c4326_sqf   : LeafSqf 4326   := by decide +kernel
private theorem c4326_range : LeafRange 4326  := by decide +kernel
private theorem c4326_ell   : LeafEll 4326    := by decide +kernel
private theorem c4326_nsq   : NSqChkSq 4326   := by decide +kernel
private theorem c4326_har   : HArithChkSq 4326 := by decide +kernel
private theorem c4326_r     : LeafR 4326      := by decide +kernel
private theorem c4326_e'    : LeafE' 4326     := by decide +kernel
private theorem c4326_f1    : LeafF1 4326     := Or.inl (by decide)
private theorem c4326_s2    : S2ChkSq 4326    := by decide +kernel
private theorem c4326_s3    : S3ChkSq 4326    := by decide +kernel
private theorem c4326_iso   : LeafIso 4326    := by decide +kernel
private theorem c4326_nof2  : NoF2ChkSq 4326  := by decide +kernel
private theorem c4326_nof3  : NoF3ChkSq 4326  := by decide +kernel
private theorem c4326_nof4z : NoF4zChkSq 4326 := by decide +kernel
theorem C'_4326 : C' 4326 :=
  ⟨c4326_sqf, c4326_range, c4326_ell, leafNSq_of_sq c4326_nsq, leafHAr_of_sq c4326_har,
   c4326_r, c4326_e', c4326_f1, leafS2_of_sq c4326_s2, leafS3_of_sq c4326_s3,
   c4326_iso, leafR8_of_sq c4326_nof2 c4326_nof3 c4326_nof4z⟩
theorem not_tile'_4326 (D : CongruentDissection 4326) : False :=
  not_tile_of_conditions' 4326 C'_4326 D

private theorem c4327_sqf   : LeafSqf 4327   := by decide +kernel
private theorem c4327_range : LeafRange 4327  := by decide +kernel
private theorem c4327_ell   : LeafEll 4327    := by decide +kernel
private theorem c4327_nsq   : NSqChkSq 4327   := by decide +kernel
private theorem c4327_har   : HArithChkSq 4327 := by decide +kernel
private theorem c4327_r     : LeafR 4327      := by decide +kernel
private theorem c4327_e'    : LeafE' 4327     := by decide +kernel
private theorem c4327_f1    : LeafF1 4327     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4327_s2    : S2ChkSq 4327    := by decide +kernel
private theorem c4327_s3    : S3ChkSq 4327    := by decide +kernel
private theorem c4327_iso   : LeafIso 4327    := by decide +kernel
private theorem c4327_nof2  : NoF2ChkSq 4327  := by decide +kernel
private theorem c4327_nof3  : NoF3ChkSq 4327  := by decide +kernel
private theorem c4327_nof4z : NoF4zChkSq 4327 := by decide +kernel
theorem C'_4327 : C' 4327 :=
  ⟨c4327_sqf, c4327_range, c4327_ell, leafNSq_of_sq c4327_nsq, leafHAr_of_sq c4327_har,
   c4327_r, c4327_e', c4327_f1, leafS2_of_sq c4327_s2, leafS3_of_sq c4327_s3,
   c4327_iso, leafR8_of_sq c4327_nof2 c4327_nof3 c4327_nof4z⟩
theorem not_tile'_4327 (D : CongruentDissection 4327) : False :=
  not_tile_of_conditions' 4327 C'_4327 D

private theorem c4331_sqf   : LeafSqf 4331   := by decide +kernel
private theorem c4331_range : LeafRange 4331  := by decide +kernel
private theorem c4331_ell   : LeafEll 4331    := by decide +kernel
private theorem c4331_nsq   : NSqChkSq 4331   := by decide +kernel
private theorem c4331_har   : HArithChkSq 4331 := by decide +kernel
private theorem c4331_r     : LeafR 4331      := by decide +kernel
private theorem c4331_e'    : LeafE' 4331     := by decide +kernel
private theorem c4331_f1    : LeafF1 4331     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4331_s2    : S2ChkSq 4331    := by decide +kernel
private theorem c4331_s3    : S3ChkSq 4331    := by decide +kernel
private theorem c4331_iso   : LeafIso 4331    := by decide +kernel
private theorem c4331_nof2  : NoF2ChkSq 4331  := by decide +kernel
private theorem c4331_nof3  : NoF3ChkSq 4331  := by decide +kernel
private theorem c4331_nof4z : NoF4zChkSq 4331 := by decide +kernel
theorem C'_4331 : C' 4331 :=
  ⟨c4331_sqf, c4331_range, c4331_ell, leafNSq_of_sq c4331_nsq, leafHAr_of_sq c4331_har,
   c4331_r, c4331_e', c4331_f1, leafS2_of_sq c4331_s2, leafS3_of_sq c4331_s3,
   c4331_iso, leafR8_of_sq c4331_nof2 c4331_nof3 c4331_nof4z⟩
theorem not_tile'_4331 (D : CongruentDissection 4331) : False :=
  not_tile_of_conditions' 4331 C'_4331 D

end Erdos634.Draft.AllN2

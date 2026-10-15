/- AllN2Check76: N = 2319, 2321, 2323, 2326, 2327
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2319_sqf   : LeafSqf 2319   := by decide +kernel
private theorem c2319_range : LeafRange 2319  := by decide +kernel
private theorem c2319_ell   : LeafEll 2319    := by decide +kernel
private theorem c2319_nsq   : NSqChkSq 2319   := by decide +kernel
private theorem c2319_har   : HArithChkSq 2319 := by decide +kernel
private theorem c2319_r     : LeafR 2319      := by decide +kernel
private theorem c2319_e'    : LeafE' 2319     := by decide +kernel
private theorem c2319_f1    : LeafF1 2319     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2319_s2    : S2ChkSq 2319    := by decide +kernel
private theorem c2319_s3    : S3ChkSq 2319    := by decide +kernel
private theorem c2319_iso   : LeafIso 2319    := by decide +kernel
private theorem c2319_nof2  : NoF2ChkSq 2319  := by decide +kernel
private theorem c2319_nof3  : NoF3ChkSq 2319  := by decide +kernel
private theorem c2319_nof4z : NoF4zChkSq 2319 := by decide +kernel
theorem C'_2319 : C' 2319 :=
  ⟨c2319_sqf, c2319_range, c2319_ell, leafNSq_of_sq c2319_nsq, leafHAr_of_sq c2319_har,
   c2319_r, c2319_e', c2319_f1, leafS2_of_sq c2319_s2, leafS3_of_sq c2319_s3,
   c2319_iso, leafR8_of_sq c2319_nof2 c2319_nof3 c2319_nof4z⟩
theorem not_tile'_2319 (D : CongruentDissection 2319) : False :=
  not_tile_of_conditions' 2319 C'_2319 D

private theorem c2321_sqf   : LeafSqf 2321   := by decide +kernel
private theorem c2321_range : LeafRange 2321  := by decide +kernel
private theorem c2321_ell   : LeafEll 2321    := by decide +kernel
private theorem c2321_nsq   : NSqChkSq 2321   := by decide +kernel
private theorem c2321_har   : HArithChkSq 2321 := by decide +kernel
private theorem c2321_r     : LeafR 2321      := by decide +kernel
private theorem c2321_e'    : LeafE' 2321     := by decide +kernel
private theorem c2321_f1    : LeafF1 2321     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2321_s2    : S2ChkSq 2321    := by decide +kernel
private theorem c2321_s3    : S3ChkSq 2321    := by decide +kernel
private theorem c2321_iso   : LeafIso 2321    := by decide +kernel
private theorem c2321_nof2  : NoF2ChkSq 2321  := by decide +kernel
private theorem c2321_nof3  : NoF3ChkSq 2321  := by decide +kernel
private theorem c2321_nof4z : NoF4zChkSq 2321 := by decide +kernel
theorem C'_2321 : C' 2321 :=
  ⟨c2321_sqf, c2321_range, c2321_ell, leafNSq_of_sq c2321_nsq, leafHAr_of_sq c2321_har,
   c2321_r, c2321_e', c2321_f1, leafS2_of_sq c2321_s2, leafS3_of_sq c2321_s3,
   c2321_iso, leafR8_of_sq c2321_nof2 c2321_nof3 c2321_nof4z⟩
theorem not_tile'_2321 (D : CongruentDissection 2321) : False :=
  not_tile_of_conditions' 2321 C'_2321 D

private theorem c2323_sqf   : LeafSqf 2323   := by decide +kernel
private theorem c2323_range : LeafRange 2323  := by decide +kernel
private theorem c2323_ell   : LeafEll 2323    := by decide +kernel
private theorem c2323_nsq   : NSqChkSq 2323   := by decide +kernel
private theorem c2323_har   : HArithChkSq 2323 := by decide +kernel
private theorem c2323_r     : LeafR 2323      := by decide +kernel
private theorem c2323_e'    : LeafE' 2323     := by decide +kernel
private theorem c2323_f1    : LeafF1 2323     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2323_s2    : S2ChkSq 2323    := by decide +kernel
private theorem c2323_s3    : S3ChkSq 2323    := by decide +kernel
private theorem c2323_iso   : LeafIso 2323    := by decide +kernel
private theorem c2323_nof2  : NoF2ChkSq 2323  := by decide +kernel
private theorem c2323_nof3  : NoF3ChkSq 2323  := by decide +kernel
private theorem c2323_nof4z : NoF4zChkSq 2323 := by decide +kernel
theorem C'_2323 : C' 2323 :=
  ⟨c2323_sqf, c2323_range, c2323_ell, leafNSq_of_sq c2323_nsq, leafHAr_of_sq c2323_har,
   c2323_r, c2323_e', c2323_f1, leafS2_of_sq c2323_s2, leafS3_of_sq c2323_s3,
   c2323_iso, leafR8_of_sq c2323_nof2 c2323_nof3 c2323_nof4z⟩
theorem not_tile'_2323 (D : CongruentDissection 2323) : False :=
  not_tile_of_conditions' 2323 C'_2323 D

private theorem c2326_sqf   : LeafSqf 2326   := by decide +kernel
private theorem c2326_range : LeafRange 2326  := by decide +kernel
private theorem c2326_ell   : LeafEll 2326    := by decide +kernel
private theorem c2326_nsq   : NSqChkSq 2326   := by decide +kernel
private theorem c2326_har   : HArithChkSq 2326 := by decide +kernel
private theorem c2326_r     : LeafR 2326      := by decide +kernel
private theorem c2326_e'    : LeafE' 2326     := by decide +kernel
private theorem c2326_f1    : LeafF1 2326     := Or.inl (by decide)
private theorem c2326_s2    : S2ChkSq 2326    := by decide +kernel
private theorem c2326_s3    : S3ChkSq 2326    := by decide +kernel
private theorem c2326_iso   : LeafIso 2326    := by decide +kernel
private theorem c2326_nof2  : NoF2ChkSq 2326  := by decide +kernel
private theorem c2326_nof3  : NoF3ChkSq 2326  := by decide +kernel
private theorem c2326_nof4z : NoF4zChkSq 2326 := by decide +kernel
theorem C'_2326 : C' 2326 :=
  ⟨c2326_sqf, c2326_range, c2326_ell, leafNSq_of_sq c2326_nsq, leafHAr_of_sq c2326_har,
   c2326_r, c2326_e', c2326_f1, leafS2_of_sq c2326_s2, leafS3_of_sq c2326_s3,
   c2326_iso, leafR8_of_sq c2326_nof2 c2326_nof3 c2326_nof4z⟩
theorem not_tile'_2326 (D : CongruentDissection 2326) : False :=
  not_tile_of_conditions' 2326 C'_2326 D

private theorem c2327_sqf   : LeafSqf 2327   := by decide +kernel
private theorem c2327_range : LeafRange 2327  := by decide +kernel
private theorem c2327_ell   : LeafEll 2327    := by decide +kernel
private theorem c2327_nsq   : NSqChkSq 2327   := by decide +kernel
private theorem c2327_har   : HArithChkSq 2327 := by decide +kernel
private theorem c2327_r     : LeafR 2327      := by decide +kernel
private theorem c2327_e'    : LeafE' 2327     := by decide +kernel
private theorem c2327_f1    : LeafF1 2327     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2327_s2    : S2ChkSq 2327    := by decide +kernel
private theorem c2327_s3    : S3ChkSq 2327    := by decide +kernel
private theorem c2327_iso   : LeafIso 2327    := by decide +kernel
private theorem c2327_nof2  : NoF2ChkSq 2327  := by decide +kernel
private theorem c2327_nof3  : NoF3ChkSq 2327  := by decide +kernel
private theorem c2327_nof4z : NoF4zChkSq 2327 := by decide +kernel
theorem C'_2327 : C' 2327 :=
  ⟨c2327_sqf, c2327_range, c2327_ell, leafNSq_of_sq c2327_nsq, leafHAr_of_sq c2327_har,
   c2327_r, c2327_e', c2327_f1, leafS2_of_sq c2327_s2, leafS3_of_sq c2327_s3,
   c2327_iso, leafR8_of_sq c2327_nof2 c2327_nof3 c2327_nof4z⟩
theorem not_tile'_2327 (D : CongruentDissection 2327) : False :=
  not_tile_of_conditions' 2327 C'_2327 D

end Erdos634.Draft.AllN2

/- AllN2Check153: N = 3290, 3291, 3295, 3299, 3302
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3290_sqf   : LeafSqf 3290   := by decide +kernel
private theorem c3290_range : LeafRange 3290  := by decide +kernel
private theorem c3290_ell   : LeafEll 3290    := by decide +kernel
private theorem c3290_nsq   : NSqChkSq 3290   := by decide +kernel
private theorem c3290_har   : HArithChkSq 3290 := by decide +kernel
private theorem c3290_r     : LeafR 3290      := by decide +kernel
private theorem c3290_e'    : LeafE' 3290     := by decide +kernel
private theorem c3290_f1    : LeafF1 3290     := Or.inl (by decide)
private theorem c3290_s2    : S2ChkSq 3290    := by decide +kernel
private theorem c3290_s3    : S3ChkSq 3290    := by decide +kernel
private theorem c3290_iso   : LeafIso 3290    := by decide +kernel
private theorem c3290_nof2  : NoF2ChkSq 3290  := by decide +kernel
private theorem c3290_nof3  : NoF3ChkSq 3290  := by decide +kernel
private theorem c3290_nof4z : NoF4zChkSq 3290 := by decide +kernel
theorem C'_3290 : C' 3290 :=
  ⟨c3290_sqf, c3290_range, c3290_ell, leafNSq_of_sq c3290_nsq, leafHAr_of_sq c3290_har,
   c3290_r, c3290_e', c3290_f1, leafS2_of_sq c3290_s2, leafS3_of_sq c3290_s3,
   c3290_iso, leafR8_of_sq c3290_nof2 c3290_nof3 c3290_nof4z⟩
theorem not_tile'_3290 (D : CongruentDissection 3290) : False :=
  not_tile_of_conditions' 3290 C'_3290 D

private theorem c3291_sqf   : LeafSqf 3291   := by decide +kernel
private theorem c3291_range : LeafRange 3291  := by decide +kernel
private theorem c3291_ell   : LeafEll 3291    := by decide +kernel
private theorem c3291_nsq   : NSqChkSq 3291   := by decide +kernel
private theorem c3291_har   : HArithChkSq 3291 := by decide +kernel
private theorem c3291_r     : LeafR 3291      := by decide +kernel
private theorem c3291_e'    : LeafE' 3291     := by decide +kernel
private theorem c3291_f1    : LeafF1 3291     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3291_s2    : S2ChkSq 3291    := by decide +kernel
private theorem c3291_s3    : S3ChkSq 3291    := by decide +kernel
private theorem c3291_iso   : LeafIso 3291    := by decide +kernel
private theorem c3291_nof2  : NoF2ChkSq 3291  := by decide +kernel
private theorem c3291_nof3  : NoF3ChkSq 3291  := by decide +kernel
private theorem c3291_nof4z : NoF4zChkSq 3291 := by decide +kernel
theorem C'_3291 : C' 3291 :=
  ⟨c3291_sqf, c3291_range, c3291_ell, leafNSq_of_sq c3291_nsq, leafHAr_of_sq c3291_har,
   c3291_r, c3291_e', c3291_f1, leafS2_of_sq c3291_s2, leafS3_of_sq c3291_s3,
   c3291_iso, leafR8_of_sq c3291_nof2 c3291_nof3 c3291_nof4z⟩
theorem not_tile'_3291 (D : CongruentDissection 3291) : False :=
  not_tile_of_conditions' 3291 C'_3291 D

private theorem c3295_sqf   : LeafSqf 3295   := by decide +kernel
private theorem c3295_range : LeafRange 3295  := by decide +kernel
private theorem c3295_ell   : LeafEll 3295    := by decide +kernel
private theorem c3295_nsq   : NSqChkSq 3295   := by decide +kernel
private theorem c3295_har   : HArithChkSq 3295 := by decide +kernel
private theorem c3295_r     : LeafR 3295      := by decide +kernel
private theorem c3295_e'    : LeafE' 3295     := by decide +kernel
private theorem c3295_f1    : LeafF1 3295     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3295_s2    : S2ChkSq 3295    := by decide +kernel
private theorem c3295_s3    : S3ChkSq 3295    := by decide +kernel
private theorem c3295_iso   : LeafIso 3295    := by decide +kernel
private theorem c3295_nof2  : NoF2ChkSq 3295  := by decide +kernel
private theorem c3295_nof3  : NoF3ChkSq 3295  := by decide +kernel
private theorem c3295_nof4z : NoF4zChkSq 3295 := by decide +kernel
theorem C'_3295 : C' 3295 :=
  ⟨c3295_sqf, c3295_range, c3295_ell, leafNSq_of_sq c3295_nsq, leafHAr_of_sq c3295_har,
   c3295_r, c3295_e', c3295_f1, leafS2_of_sq c3295_s2, leafS3_of_sq c3295_s3,
   c3295_iso, leafR8_of_sq c3295_nof2 c3295_nof3 c3295_nof4z⟩
theorem not_tile'_3295 (D : CongruentDissection 3295) : False :=
  not_tile_of_conditions' 3295 C'_3295 D

private theorem c3299_sqf   : LeafSqf 3299   := by decide +kernel
private theorem c3299_range : LeafRange 3299  := by decide +kernel
private theorem c3299_ell   : LeafEll 3299    := by decide +kernel
private theorem c3299_nsq   : NSqChkSq 3299   := by decide +kernel
private theorem c3299_har   : HArithChkSq 3299 := by decide +kernel
private theorem c3299_r     : LeafR 3299      := by decide +kernel
private theorem c3299_e'    : LeafE' 3299     := by decide +kernel
private theorem c3299_f1    : LeafF1 3299     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3299_s2    : S2ChkSq 3299    := by decide +kernel
private theorem c3299_s3    : S3ChkSq 3299    := by decide +kernel
private theorem c3299_iso   : LeafIso 3299    := by decide +kernel
private theorem c3299_nof2  : NoF2ChkSq 3299  := by decide +kernel
private theorem c3299_nof3  : NoF3ChkSq 3299  := by decide +kernel
private theorem c3299_nof4z : NoF4zChkSq 3299 := by decide +kernel
theorem C'_3299 : C' 3299 :=
  ⟨c3299_sqf, c3299_range, c3299_ell, leafNSq_of_sq c3299_nsq, leafHAr_of_sq c3299_har,
   c3299_r, c3299_e', c3299_f1, leafS2_of_sq c3299_s2, leafS3_of_sq c3299_s3,
   c3299_iso, leafR8_of_sq c3299_nof2 c3299_nof3 c3299_nof4z⟩
theorem not_tile'_3299 (D : CongruentDissection 3299) : False :=
  not_tile_of_conditions' 3299 C'_3299 D

private theorem c3302_sqf   : LeafSqf 3302   := by decide +kernel
private theorem c3302_range : LeafRange 3302  := by decide +kernel
private theorem c3302_ell   : LeafEll 3302    := by decide +kernel
private theorem c3302_nsq   : NSqChkSq 3302   := by decide +kernel
private theorem c3302_har   : HArithChkSq 3302 := by decide +kernel
private theorem c3302_r     : LeafR 3302      := by decide +kernel
private theorem c3302_e'    : LeafE' 3302     := by decide +kernel
private theorem c3302_f1    : LeafF1 3302     := Or.inl (by decide)
private theorem c3302_s2    : S2ChkSq 3302    := by decide +kernel
private theorem c3302_s3    : S3ChkSq 3302    := by decide +kernel
private theorem c3302_iso   : LeafIso 3302    := by decide +kernel
private theorem c3302_nof2  : NoF2ChkSq 3302  := by decide +kernel
private theorem c3302_nof3  : NoF3ChkSq 3302  := by decide +kernel
private theorem c3302_nof4z : NoF4zChkSq 3302 := by decide +kernel
theorem C'_3302 : C' 3302 :=
  ⟨c3302_sqf, c3302_range, c3302_ell, leafNSq_of_sq c3302_nsq, leafHAr_of_sq c3302_har,
   c3302_r, c3302_e', c3302_f1, leafS2_of_sq c3302_s2, leafS3_of_sq c3302_s3,
   c3302_iso, leafR8_of_sq c3302_nof2 c3302_nof3 c3302_nof4z⟩
theorem not_tile'_3302 (D : CongruentDissection 3302) : False :=
  not_tile_of_conditions' 3302 C'_3302 D

end Erdos634.Draft.AllN2

/- AllN2Check156: N = 3327, 3331, 3334, 3335, 3337
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3327_sqf   : LeafSqf 3327   := by decide +kernel
private theorem c3327_range : LeafRange 3327  := by decide +kernel
private theorem c3327_ell   : LeafEll 3327    := by decide +kernel
private theorem c3327_nsq   : NSqChkSq 3327   := by decide +kernel
private theorem c3327_har   : HArithChkSq 3327 := by decide +kernel
private theorem c3327_r     : LeafR 3327      := by decide +kernel
private theorem c3327_e'    : LeafE' 3327     := by decide +kernel
private theorem c3327_f1    : LeafF1 3327     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3327_s2    : S2ChkSq 3327    := by decide +kernel
private theorem c3327_s3    : S3ChkSq 3327    := by decide +kernel
private theorem c3327_iso   : LeafIso 3327    := by decide +kernel
private theorem c3327_nof2  : NoF2ChkSq 3327  := by decide +kernel
private theorem c3327_nof3  : NoF3ChkSq 3327  := by decide +kernel
private theorem c3327_nof4z : NoF4zChkSq 3327 := by decide +kernel
theorem C'_3327 : C' 3327 :=
  ⟨c3327_sqf, c3327_range, c3327_ell, leafNSq_of_sq c3327_nsq, leafHAr_of_sq c3327_har,
   c3327_r, c3327_e', c3327_f1, leafS2_of_sq c3327_s2, leafS3_of_sq c3327_s3,
   c3327_iso, leafR8_of_sq c3327_nof2 c3327_nof3 c3327_nof4z⟩
theorem not_tile'_3327 (D : CongruentDissection 3327) : False :=
  not_tile_of_conditions' 3327 C'_3327 D

private theorem c3331_sqf   : LeafSqf 3331   := by decide +kernel
private theorem c3331_range : LeafRange 3331  := by decide +kernel
private theorem c3331_ell   : LeafEll 3331    := by decide +kernel
private theorem c3331_nsq   : NSqChkSq 3331   := by decide +kernel
private theorem c3331_har   : HArithChkSq 3331 := by decide +kernel
private theorem c3331_r     : LeafR 3331      := by decide +kernel
private theorem c3331_e'    : LeafE' 3331     := by decide +kernel
private theorem c3331_f1    : LeafF1 3331     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3331_s2    : S2ChkSq 3331    := by decide +kernel
private theorem c3331_s3    : S3ChkSq 3331    := by decide +kernel
private theorem c3331_iso   : LeafIso 3331    := by decide +kernel
private theorem c3331_nof2  : NoF2ChkSq 3331  := by decide +kernel
private theorem c3331_nof3  : NoF3ChkSq 3331  := by decide +kernel
private theorem c3331_nof4z : NoF4zChkSq 3331 := by decide +kernel
theorem C'_3331 : C' 3331 :=
  ⟨c3331_sqf, c3331_range, c3331_ell, leafNSq_of_sq c3331_nsq, leafHAr_of_sq c3331_har,
   c3331_r, c3331_e', c3331_f1, leafS2_of_sq c3331_s2, leafS3_of_sq c3331_s3,
   c3331_iso, leafR8_of_sq c3331_nof2 c3331_nof3 c3331_nof4z⟩
theorem not_tile'_3331 (D : CongruentDissection 3331) : False :=
  not_tile_of_conditions' 3331 C'_3331 D

private theorem c3334_sqf   : LeafSqf 3334   := by decide +kernel
private theorem c3334_range : LeafRange 3334  := by decide +kernel
private theorem c3334_ell   : LeafEll 3334    := by decide +kernel
private theorem c3334_nsq   : NSqChkSq 3334   := by decide +kernel
private theorem c3334_har   : HArithChkSq 3334 := by decide +kernel
private theorem c3334_r     : LeafR 3334      := by decide +kernel
private theorem c3334_e'    : LeafE' 3334     := by decide +kernel
private theorem c3334_f1    : LeafF1 3334     := Or.inl (by decide)
private theorem c3334_s2    : S2ChkSq 3334    := by decide +kernel
private theorem c3334_s3    : S3ChkSq 3334    := by decide +kernel
private theorem c3334_iso   : LeafIso 3334    := by decide +kernel
private theorem c3334_nof2  : NoF2ChkSq 3334  := by decide +kernel
private theorem c3334_nof3  : NoF3ChkSq 3334  := by decide +kernel
private theorem c3334_nof4z : NoF4zChkSq 3334 := by decide +kernel
theorem C'_3334 : C' 3334 :=
  ⟨c3334_sqf, c3334_range, c3334_ell, leafNSq_of_sq c3334_nsq, leafHAr_of_sq c3334_har,
   c3334_r, c3334_e', c3334_f1, leafS2_of_sq c3334_s2, leafS3_of_sq c3334_s3,
   c3334_iso, leafR8_of_sq c3334_nof2 c3334_nof3 c3334_nof4z⟩
theorem not_tile'_3334 (D : CongruentDissection 3334) : False :=
  not_tile_of_conditions' 3334 C'_3334 D

private theorem c3335_sqf   : LeafSqf 3335   := by decide +kernel
private theorem c3335_range : LeafRange 3335  := by decide +kernel
private theorem c3335_ell   : LeafEll 3335    := by decide +kernel
private theorem c3335_nsq   : NSqChkSq 3335   := by decide +kernel
private theorem c3335_har   : HArithChkSq 3335 := by decide +kernel
private theorem c3335_r     : LeafR 3335      := by decide +kernel
private theorem c3335_e'    : LeafE' 3335     := by decide +kernel
private theorem c3335_f1    : LeafF1 3335     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3335_s2    : S2ChkSq 3335    := by decide +kernel
private theorem c3335_s3    : S3ChkSq 3335    := by decide +kernel
private theorem c3335_iso   : LeafIso 3335    := by decide +kernel
private theorem c3335_nof2  : NoF2ChkSq 3335  := by decide +kernel
private theorem c3335_nof3  : NoF3ChkSq 3335  := by decide +kernel
private theorem c3335_nof4z : NoF4zChkSq 3335 := by decide +kernel
theorem C'_3335 : C' 3335 :=
  ⟨c3335_sqf, c3335_range, c3335_ell, leafNSq_of_sq c3335_nsq, leafHAr_of_sq c3335_har,
   c3335_r, c3335_e', c3335_f1, leafS2_of_sq c3335_s2, leafS3_of_sq c3335_s3,
   c3335_iso, leafR8_of_sq c3335_nof2 c3335_nof3 c3335_nof4z⟩
theorem not_tile'_3335 (D : CongruentDissection 3335) : False :=
  not_tile_of_conditions' 3335 C'_3335 D

private theorem c3337_sqf   : LeafSqf 3337   := by decide +kernel
private theorem c3337_range : LeafRange 3337  := by decide +kernel
private theorem c3337_ell   : LeafEll 3337    := by decide +kernel
private theorem c3337_nsq   : NSqChkSq 3337   := by decide +kernel
private theorem c3337_har   : HArithChkSq 3337 := by decide +kernel
private theorem c3337_r     : LeafR 3337      := by decide +kernel
private theorem c3337_e'    : LeafE' 3337     := by decide +kernel
private theorem c3337_f1    : LeafF1 3337     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3337_s2    : S2ChkSq 3337    := by decide +kernel
private theorem c3337_s3    : S3ChkSq 3337    := by decide +kernel
private theorem c3337_iso   : LeafIso 3337    := by decide +kernel
private theorem c3337_nof2  : NoF2ChkSq 3337  := by decide +kernel
private theorem c3337_nof3  : NoF3ChkSq 3337  := by decide +kernel
private theorem c3337_nof4z : NoF4zChkSq 3337 := by decide +kernel
theorem C'_3337 : C' 3337 :=
  ⟨c3337_sqf, c3337_range, c3337_ell, leafNSq_of_sq c3337_nsq, leafHAr_of_sq c3337_har,
   c3337_r, c3337_e', c3337_f1, leafS2_of_sq c3337_s2, leafS3_of_sq c3337_s3,
   c3337_iso, leafR8_of_sq c3337_nof2 c3337_nof3 c3337_nof4z⟩
theorem not_tile'_3337 (D : CongruentDissection 3337) : False :=
  not_tile_of_conditions' 3337 C'_3337 D

end Erdos634.Draft.AllN2

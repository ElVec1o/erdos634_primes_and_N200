/- AllN2Check191: N = 3787, 3790, 3791, 3794, 3799
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3787_sqf   : LeafSqf 3787   := by decide +kernel
private theorem c3787_range : LeafRange 3787  := by decide +kernel
private theorem c3787_ell   : LeafEll 3787    := by decide +kernel
private theorem c3787_nsq   : NSqChkSq 3787   := by decide +kernel
private theorem c3787_har   : HArithChkSq 3787 := by decide +kernel
private theorem c3787_r     : LeafR 3787      := by decide +kernel
private theorem c3787_e'    : LeafE' 3787     := by decide +kernel
private theorem c3787_f1    : LeafF1 3787     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3787_s2    : S2ChkSq 3787    := by decide +kernel
private theorem c3787_s3    : S3ChkSq 3787    := by decide +kernel
private theorem c3787_iso   : LeafIso 3787    := by decide +kernel
private theorem c3787_nof2  : NoF2ChkSq 3787  := by decide +kernel
private theorem c3787_nof3  : NoF3ChkSq 3787  := by decide +kernel
private theorem c3787_nof4z : NoF4zChkSq 3787 := by decide +kernel
theorem C'_3787 : C' 3787 :=
  ⟨c3787_sqf, c3787_range, c3787_ell, leafNSq_of_sq c3787_nsq, leafHAr_of_sq c3787_har,
   c3787_r, c3787_e', c3787_f1, leafS2_of_sq c3787_s2, leafS3_of_sq c3787_s3,
   c3787_iso, leafR8_of_sq c3787_nof2 c3787_nof3 c3787_nof4z⟩
theorem not_tile'_3787 (D : CongruentDissection 3787) : False :=
  not_tile_of_conditions' 3787 C'_3787 D

private theorem c3790_sqf   : LeafSqf 3790   := by decide +kernel
private theorem c3790_range : LeafRange 3790  := by decide +kernel
private theorem c3790_ell   : LeafEll 3790    := by decide +kernel
private theorem c3790_nsq   : NSqChkSq 3790   := by decide +kernel
private theorem c3790_har   : HArithChkSq 3790 := by decide +kernel
private theorem c3790_r     : LeafR 3790      := by decide +kernel
private theorem c3790_e'    : LeafE' 3790     := by decide +kernel
private theorem c3790_f1    : LeafF1 3790     := Or.inl (by decide)
private theorem c3790_s2    : S2ChkSq 3790    := by decide +kernel
private theorem c3790_s3    : S3ChkSq 3790    := by decide +kernel
private theorem c3790_iso   : LeafIso 3790    := by decide +kernel
private theorem c3790_nof2  : NoF2ChkSq 3790  := by decide +kernel
private theorem c3790_nof3  : NoF3ChkSq 3790  := by decide +kernel
private theorem c3790_nof4z : NoF4zChkSq 3790 := by decide +kernel
theorem C'_3790 : C' 3790 :=
  ⟨c3790_sqf, c3790_range, c3790_ell, leafNSq_of_sq c3790_nsq, leafHAr_of_sq c3790_har,
   c3790_r, c3790_e', c3790_f1, leafS2_of_sq c3790_s2, leafS3_of_sq c3790_s3,
   c3790_iso, leafR8_of_sq c3790_nof2 c3790_nof3 c3790_nof4z⟩
theorem not_tile'_3790 (D : CongruentDissection 3790) : False :=
  not_tile_of_conditions' 3790 C'_3790 D

private theorem c3791_sqf   : LeafSqf 3791   := by decide +kernel
private theorem c3791_range : LeafRange 3791  := by decide +kernel
private theorem c3791_ell   : LeafEll 3791    := by decide +kernel
private theorem c3791_nsq   : NSqChkSq 3791   := by decide +kernel
private theorem c3791_har   : HArithChkSq 3791 := by decide +kernel
private theorem c3791_r     : LeafR 3791      := by decide +kernel
private theorem c3791_e'    : LeafE' 3791     := by decide +kernel
private theorem c3791_f1    : LeafF1 3791     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3791_s2    : S2ChkSq 3791    := by decide +kernel
private theorem c3791_s3    : S3ChkSq 3791    := by decide +kernel
private theorem c3791_iso   : LeafIso 3791    := by decide +kernel
private theorem c3791_nof2  : NoF2ChkSq 3791  := by decide +kernel
private theorem c3791_nof3  : NoF3ChkSq 3791  := by decide +kernel
private theorem c3791_nof4z : NoF4zChkSq 3791 := by decide +kernel
theorem C'_3791 : C' 3791 :=
  ⟨c3791_sqf, c3791_range, c3791_ell, leafNSq_of_sq c3791_nsq, leafHAr_of_sq c3791_har,
   c3791_r, c3791_e', c3791_f1, leafS2_of_sq c3791_s2, leafS3_of_sq c3791_s3,
   c3791_iso, leafR8_of_sq c3791_nof2 c3791_nof3 c3791_nof4z⟩
theorem not_tile'_3791 (D : CongruentDissection 3791) : False :=
  not_tile_of_conditions' 3791 C'_3791 D

private theorem c3794_sqf   : LeafSqf 3794   := by decide +kernel
private theorem c3794_range : LeafRange 3794  := by decide +kernel
private theorem c3794_ell   : LeafEll 3794    := by decide +kernel
private theorem c3794_nsq   : NSqChkSq 3794   := by decide +kernel
private theorem c3794_har   : HArithChkSq 3794 := by decide +kernel
private theorem c3794_r     : LeafR 3794      := by decide +kernel
private theorem c3794_e'    : LeafE' 3794     := by decide +kernel
private theorem c3794_f1    : LeafF1 3794     := Or.inl (by decide)
private theorem c3794_s2    : S2ChkSq 3794    := by decide +kernel
private theorem c3794_s3    : S3ChkSq 3794    := by decide +kernel
private theorem c3794_iso   : LeafIso 3794    := by decide +kernel
private theorem c3794_nof2  : NoF2ChkSq 3794  := by decide +kernel
private theorem c3794_nof3  : NoF3ChkSq 3794  := by decide +kernel
private theorem c3794_nof4z : NoF4zChkSq 3794 := by decide +kernel
theorem C'_3794 : C' 3794 :=
  ⟨c3794_sqf, c3794_range, c3794_ell, leafNSq_of_sq c3794_nsq, leafHAr_of_sq c3794_har,
   c3794_r, c3794_e', c3794_f1, leafS2_of_sq c3794_s2, leafS3_of_sq c3794_s3,
   c3794_iso, leafR8_of_sq c3794_nof2 c3794_nof3 c3794_nof4z⟩
theorem not_tile'_3794 (D : CongruentDissection 3794) : False :=
  not_tile_of_conditions' 3794 C'_3794 D

private theorem c3799_sqf   : LeafSqf 3799   := by decide +kernel
private theorem c3799_range : LeafRange 3799  := by decide +kernel
private theorem c3799_ell   : LeafEll 3799    := by decide +kernel
private theorem c3799_nsq   : NSqChkSq 3799   := by decide +kernel
private theorem c3799_har   : HArithChkSq 3799 := by decide +kernel
private theorem c3799_r     : LeafR 3799      := by decide +kernel
private theorem c3799_e'    : LeafE' 3799     := by decide +kernel
private theorem c3799_f1    : LeafF1 3799     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3799_s2    : S2ChkSq 3799    := by decide +kernel
private theorem c3799_s3    : S3ChkSq 3799    := by decide +kernel
private theorem c3799_iso   : LeafIso 3799    := by decide +kernel
private theorem c3799_nof2  : NoF2ChkSq 3799  := by decide +kernel
private theorem c3799_nof3  : NoF3ChkSq 3799  := by decide +kernel
private theorem c3799_nof4z : NoF4zChkSq 3799 := by decide +kernel
theorem C'_3799 : C' 3799 :=
  ⟨c3799_sqf, c3799_range, c3799_ell, leafNSq_of_sq c3799_nsq, leafHAr_of_sq c3799_har,
   c3799_r, c3799_e', c3799_f1, leafS2_of_sq c3799_s2, leafS3_of_sq c3799_s3,
   c3799_iso, leafR8_of_sq c3799_nof2 c3799_nof3 c3799_nof4z⟩
theorem not_tile'_3799 (D : CongruentDissection 3799) : False :=
  not_tile_of_conditions' 3799 C'_3799 D

end Erdos634.Draft.AllN2

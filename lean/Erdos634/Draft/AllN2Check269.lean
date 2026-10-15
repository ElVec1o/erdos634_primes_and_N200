/- AllN2Check269: N = 4782, 4783, 4787, 4790, 4791
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4782_sqf   : LeafSqf 4782   := by decide +kernel
private theorem c4782_range : LeafRange 4782  := by decide +kernel
private theorem c4782_ell   : LeafEll 4782    := by decide +kernel
private theorem c4782_nsq   : NSqChkSq 4782   := by decide +kernel
private theorem c4782_har   : HArithChkSq 4782 := by decide +kernel
private theorem c4782_r     : LeafR 4782      := by decide +kernel
private theorem c4782_e'    : LeafE' 4782     := by decide +kernel
private theorem c4782_f1    : LeafF1 4782     := Or.inl (by decide)
private theorem c4782_s2    : S2ChkSq 4782    := by decide +kernel
private theorem c4782_s3    : S3ChkSq 4782    := by decide +kernel
private theorem c4782_iso   : LeafIso 4782    := by decide +kernel
private theorem c4782_nof2  : NoF2ChkSq 4782  := by decide +kernel
private theorem c4782_nof3  : NoF3ChkSq 4782  := by decide +kernel
private theorem c4782_nof4z : NoF4zChkSq 4782 := by decide +kernel
theorem C'_4782 : C' 4782 :=
  ⟨c4782_sqf, c4782_range, c4782_ell, leafNSq_of_sq c4782_nsq, leafHAr_of_sq c4782_har,
   c4782_r, c4782_e', c4782_f1, leafS2_of_sq c4782_s2, leafS3_of_sq c4782_s3,
   c4782_iso, leafR8_of_sq c4782_nof2 c4782_nof3 c4782_nof4z⟩
theorem not_tile'_4782 (D : CongruentDissection 4782) : False :=
  not_tile_of_conditions' 4782 C'_4782 D

private theorem c4783_sqf   : LeafSqf 4783   := by decide +kernel
private theorem c4783_range : LeafRange 4783  := by decide +kernel
private theorem c4783_ell   : LeafEll 4783    := by decide +kernel
private theorem c4783_nsq   : NSqChkSq 4783   := by decide +kernel
private theorem c4783_har   : HArithChkSq 4783 := by decide +kernel
private theorem c4783_r     : LeafR 4783      := by decide +kernel
private theorem c4783_e'    : LeafE' 4783     := by decide +kernel
private theorem c4783_f1    : LeafF1 4783     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4783_s2    : S2ChkSq 4783    := by decide +kernel
private theorem c4783_s3    : S3ChkSq 4783    := by decide +kernel
private theorem c4783_iso   : LeafIso 4783    := by decide +kernel
private theorem c4783_nof2  : NoF2ChkSq 4783  := by decide +kernel
private theorem c4783_nof3  : NoF3ChkSq 4783  := by decide +kernel
private theorem c4783_nof4z : NoF4zChkSq 4783 := by decide +kernel
theorem C'_4783 : C' 4783 :=
  ⟨c4783_sqf, c4783_range, c4783_ell, leafNSq_of_sq c4783_nsq, leafHAr_of_sq c4783_har,
   c4783_r, c4783_e', c4783_f1, leafS2_of_sq c4783_s2, leafS3_of_sq c4783_s3,
   c4783_iso, leafR8_of_sq c4783_nof2 c4783_nof3 c4783_nof4z⟩
theorem not_tile'_4783 (D : CongruentDissection 4783) : False :=
  not_tile_of_conditions' 4783 C'_4783 D

private theorem c4787_sqf   : LeafSqf 4787   := by decide +kernel
private theorem c4787_range : LeafRange 4787  := by decide +kernel
private theorem c4787_ell   : LeafEll 4787    := by decide +kernel
private theorem c4787_nsq   : NSqChkSq 4787   := by decide +kernel
private theorem c4787_har   : HArithChkSq 4787 := by decide +kernel
private theorem c4787_r     : LeafR 4787      := by decide +kernel
private theorem c4787_e'    : LeafE' 4787     := by decide +kernel
private theorem c4787_f1    : LeafF1 4787     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4787_s2    : S2ChkSq 4787    := by decide +kernel
private theorem c4787_s3    : S3ChkSq 4787    := by decide +kernel
private theorem c4787_iso   : LeafIso 4787    := by decide +kernel
private theorem c4787_nof2  : NoF2ChkSq 4787  := by decide +kernel
private theorem c4787_nof3  : NoF3ChkSq 4787  := by decide +kernel
private theorem c4787_nof4z : NoF4zChkSq 4787 := by decide +kernel
theorem C'_4787 : C' 4787 :=
  ⟨c4787_sqf, c4787_range, c4787_ell, leafNSq_of_sq c4787_nsq, leafHAr_of_sq c4787_har,
   c4787_r, c4787_e', c4787_f1, leafS2_of_sq c4787_s2, leafS3_of_sq c4787_s3,
   c4787_iso, leafR8_of_sq c4787_nof2 c4787_nof3 c4787_nof4z⟩
theorem not_tile'_4787 (D : CongruentDissection 4787) : False :=
  not_tile_of_conditions' 4787 C'_4787 D

private theorem c4790_sqf   : LeafSqf 4790   := by decide +kernel
private theorem c4790_range : LeafRange 4790  := by decide +kernel
private theorem c4790_ell   : LeafEll 4790    := by decide +kernel
private theorem c4790_nsq   : NSqChkSq 4790   := by decide +kernel
private theorem c4790_har   : HArithChkSq 4790 := by decide +kernel
private theorem c4790_r     : LeafR 4790      := by decide +kernel
private theorem c4790_e'    : LeafE' 4790     := by decide +kernel
private theorem c4790_f1    : LeafF1 4790     := Or.inl (by decide)
private theorem c4790_s2    : S2ChkSq 4790    := by decide +kernel
private theorem c4790_s3    : S3ChkSq 4790    := by decide +kernel
private theorem c4790_iso   : LeafIso 4790    := by decide +kernel
private theorem c4790_nof2  : NoF2ChkSq 4790  := by decide +kernel
private theorem c4790_nof3  : NoF3ChkSq 4790  := by decide +kernel
private theorem c4790_nof4z : NoF4zChkSq 4790 := by decide +kernel
theorem C'_4790 : C' 4790 :=
  ⟨c4790_sqf, c4790_range, c4790_ell, leafNSq_of_sq c4790_nsq, leafHAr_of_sq c4790_har,
   c4790_r, c4790_e', c4790_f1, leafS2_of_sq c4790_s2, leafS3_of_sq c4790_s3,
   c4790_iso, leafR8_of_sq c4790_nof2 c4790_nof3 c4790_nof4z⟩
theorem not_tile'_4790 (D : CongruentDissection 4790) : False :=
  not_tile_of_conditions' 4790 C'_4790 D

private theorem c4791_sqf   : LeafSqf 4791   := by decide +kernel
private theorem c4791_range : LeafRange 4791  := by decide +kernel
private theorem c4791_ell   : LeafEll 4791    := by decide +kernel
private theorem c4791_nsq   : NSqChkSq 4791   := by decide +kernel
private theorem c4791_har   : HArithChkSq 4791 := by decide +kernel
private theorem c4791_r     : LeafR 4791      := by decide +kernel
private theorem c4791_e'    : LeafE' 4791     := by decide +kernel
private theorem c4791_f1    : LeafF1 4791     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4791_s2    : S2ChkSq 4791    := by decide +kernel
private theorem c4791_s3    : S3ChkSq 4791    := by decide +kernel
private theorem c4791_iso   : LeafIso 4791    := by decide +kernel
private theorem c4791_nof2  : NoF2ChkSq 4791  := by decide +kernel
private theorem c4791_nof3  : NoF3ChkSq 4791  := by decide +kernel
private theorem c4791_nof4z : NoF4zChkSq 4791 := by decide +kernel
theorem C'_4791 : C' 4791 :=
  ⟨c4791_sqf, c4791_range, c4791_ell, leafNSq_of_sq c4791_nsq, leafHAr_of_sq c4791_har,
   c4791_r, c4791_e', c4791_f1, leafS2_of_sq c4791_s2, leafS3_of_sq c4791_s3,
   c4791_iso, leafR8_of_sq c4791_nof2 c4791_nof3 c4791_nof4z⟩
theorem not_tile'_4791 (D : CongruentDissection 4791) : False :=
  not_tile_of_conditions' 4791 C'_4791 D

end Erdos634.Draft.AllN2

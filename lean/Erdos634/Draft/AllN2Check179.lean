/- AllN2Check179: N = 3635, 3638, 3639, 3641, 3642
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3635_sqf   : LeafSqf 3635   := by decide +kernel
private theorem c3635_range : LeafRange 3635  := by decide +kernel
private theorem c3635_ell   : LeafEll 3635    := by decide +kernel
private theorem c3635_nsq   : NSqChkSq 3635   := by decide +kernel
private theorem c3635_har   : HArithChkSq 3635 := by decide +kernel
private theorem c3635_r     : LeafR 3635      := by decide +kernel
private theorem c3635_e'    : LeafE' 3635     := by decide +kernel
private theorem c3635_f1    : LeafF1 3635     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3635_s2    : S2ChkSq 3635    := by decide +kernel
private theorem c3635_s3    : S3ChkSq 3635    := by decide +kernel
private theorem c3635_iso   : LeafIso 3635    := by decide +kernel
private theorem c3635_nof2  : NoF2ChkSq 3635  := by decide +kernel
private theorem c3635_nof3  : NoF3ChkSq 3635  := by decide +kernel
private theorem c3635_nof4z : NoF4zChkSq 3635 := by decide +kernel
theorem C'_3635 : C' 3635 :=
  ⟨c3635_sqf, c3635_range, c3635_ell, leafNSq_of_sq c3635_nsq, leafHAr_of_sq c3635_har,
   c3635_r, c3635_e', c3635_f1, leafS2_of_sq c3635_s2, leafS3_of_sq c3635_s3,
   c3635_iso, leafR8_of_sq c3635_nof2 c3635_nof3 c3635_nof4z⟩
theorem not_tile'_3635 (D : CongruentDissection 3635) : False :=
  not_tile_of_conditions' 3635 C'_3635 D

private theorem c3638_sqf   : LeafSqf 3638   := by decide +kernel
private theorem c3638_range : LeafRange 3638  := by decide +kernel
private theorem c3638_ell   : LeafEll 3638    := by decide +kernel
private theorem c3638_nsq   : NSqChkSq 3638   := by decide +kernel
private theorem c3638_har   : HArithChkSq 3638 := by decide +kernel
private theorem c3638_r     : LeafR 3638      := by decide +kernel
private theorem c3638_e'    : LeafE' 3638     := by decide +kernel
private theorem c3638_f1    : LeafF1 3638     := Or.inl (by decide)
private theorem c3638_s2    : S2ChkSq 3638    := by decide +kernel
private theorem c3638_s3    : S3ChkSq 3638    := by decide +kernel
private theorem c3638_iso   : LeafIso 3638    := by decide +kernel
private theorem c3638_nof2  : NoF2ChkSq 3638  := by decide +kernel
private theorem c3638_nof3  : NoF3ChkSq 3638  := by decide +kernel
private theorem c3638_nof4z : NoF4zChkSq 3638 := by decide +kernel
theorem C'_3638 : C' 3638 :=
  ⟨c3638_sqf, c3638_range, c3638_ell, leafNSq_of_sq c3638_nsq, leafHAr_of_sq c3638_har,
   c3638_r, c3638_e', c3638_f1, leafS2_of_sq c3638_s2, leafS3_of_sq c3638_s3,
   c3638_iso, leafR8_of_sq c3638_nof2 c3638_nof3 c3638_nof4z⟩
theorem not_tile'_3638 (D : CongruentDissection 3638) : False :=
  not_tile_of_conditions' 3638 C'_3638 D

private theorem c3639_sqf   : LeafSqf 3639   := by decide +kernel
private theorem c3639_range : LeafRange 3639  := by decide +kernel
private theorem c3639_ell   : LeafEll 3639    := by decide +kernel
private theorem c3639_nsq   : NSqChkSq 3639   := by decide +kernel
private theorem c3639_har   : HArithChkSq 3639 := by decide +kernel
private theorem c3639_r     : LeafR 3639      := by decide +kernel
private theorem c3639_e'    : LeafE' 3639     := by decide +kernel
private theorem c3639_f1    : LeafF1 3639     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3639_s2    : S2ChkSq 3639    := by decide +kernel
private theorem c3639_s3    : S3ChkSq 3639    := by decide +kernel
private theorem c3639_iso   : LeafIso 3639    := by decide +kernel
private theorem c3639_nof2  : NoF2ChkSq 3639  := by decide +kernel
private theorem c3639_nof3  : NoF3ChkSq 3639  := by decide +kernel
private theorem c3639_nof4z : NoF4zChkSq 3639 := by decide +kernel
theorem C'_3639 : C' 3639 :=
  ⟨c3639_sqf, c3639_range, c3639_ell, leafNSq_of_sq c3639_nsq, leafHAr_of_sq c3639_har,
   c3639_r, c3639_e', c3639_f1, leafS2_of_sq c3639_s2, leafS3_of_sq c3639_s3,
   c3639_iso, leafR8_of_sq c3639_nof2 c3639_nof3 c3639_nof4z⟩
theorem not_tile'_3639 (D : CongruentDissection 3639) : False :=
  not_tile_of_conditions' 3639 C'_3639 D

private theorem c3641_sqf   : LeafSqf 3641   := by decide +kernel
private theorem c3641_range : LeafRange 3641  := by decide +kernel
private theorem c3641_ell   : LeafEll 3641    := by decide +kernel
private theorem c3641_nsq   : NSqChkSq 3641   := by decide +kernel
private theorem c3641_har   : HArithChkSq 3641 := by decide +kernel
private theorem c3641_r     : LeafR 3641      := by decide +kernel
private theorem c3641_e'    : LeafE' 3641     := by decide +kernel
private theorem c3641_f1    : LeafF1 3641     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3641_s2    : S2ChkSq 3641    := by decide +kernel
private theorem c3641_s3    : S3ChkSq 3641    := by decide +kernel
private theorem c3641_iso   : LeafIso 3641    := by decide +kernel
private theorem c3641_nof2  : NoF2ChkSq 3641  := by decide +kernel
private theorem c3641_nof3  : NoF3ChkSq 3641  := by decide +kernel
private theorem c3641_nof4z : NoF4zChkSq 3641 := by decide +kernel
theorem C'_3641 : C' 3641 :=
  ⟨c3641_sqf, c3641_range, c3641_ell, leafNSq_of_sq c3641_nsq, leafHAr_of_sq c3641_har,
   c3641_r, c3641_e', c3641_f1, leafS2_of_sq c3641_s2, leafS3_of_sq c3641_s3,
   c3641_iso, leafR8_of_sq c3641_nof2 c3641_nof3 c3641_nof4z⟩
theorem not_tile'_3641 (D : CongruentDissection 3641) : False :=
  not_tile_of_conditions' 3641 C'_3641 D

private theorem c3642_sqf   : LeafSqf 3642   := by decide +kernel
private theorem c3642_range : LeafRange 3642  := by decide +kernel
private theorem c3642_ell   : LeafEll 3642    := by decide +kernel
private theorem c3642_nsq   : NSqChkSq 3642   := by decide +kernel
private theorem c3642_har   : HArithChkSq 3642 := by decide +kernel
private theorem c3642_r     : LeafR 3642      := by decide +kernel
private theorem c3642_e'    : LeafE' 3642     := by decide +kernel
private theorem c3642_f1    : LeafF1 3642     := Or.inl (by decide)
private theorem c3642_s2    : S2ChkSq 3642    := by decide +kernel
private theorem c3642_s3    : S3ChkSq 3642    := by decide +kernel
private theorem c3642_iso   : LeafIso 3642    := by decide +kernel
private theorem c3642_nof2  : NoF2ChkSq 3642  := by decide +kernel
private theorem c3642_nof3  : NoF3ChkSq 3642  := by decide +kernel
private theorem c3642_nof4z : NoF4zChkSq 3642 := by decide +kernel
theorem C'_3642 : C' 3642 :=
  ⟨c3642_sqf, c3642_range, c3642_ell, leafNSq_of_sq c3642_nsq, leafHAr_of_sq c3642_har,
   c3642_r, c3642_e', c3642_f1, leafS2_of_sq c3642_s2, leafS3_of_sq c3642_s3,
   c3642_iso, leafR8_of_sq c3642_nof2 c3642_nof3 c3642_nof4z⟩
theorem not_tile'_3642 (D : CongruentDissection 3642) : False :=
  not_tile_of_conditions' 3642 C'_3642 D

end Erdos634.Draft.AllN2

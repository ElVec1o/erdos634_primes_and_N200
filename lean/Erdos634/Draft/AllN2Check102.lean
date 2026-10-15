/- AllN2Check102: N = 2635, 2638, 2639, 2641, 2643
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2635_sqf   : LeafSqf 2635   := by decide +kernel
private theorem c2635_range : LeafRange 2635  := by decide +kernel
private theorem c2635_ell   : LeafEll 2635    := by decide +kernel
private theorem c2635_nsq   : NSqChkSq 2635   := by decide +kernel
private theorem c2635_har   : HArithChkSq 2635 := by decide +kernel
private theorem c2635_r     : LeafR 2635      := by decide +kernel
private theorem c2635_e'    : LeafE' 2635     := by decide +kernel
private theorem c2635_f1    : LeafF1 2635     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2635_s2    : S2ChkSq 2635    := by decide +kernel
private theorem c2635_s3    : S3ChkSq 2635    := by decide +kernel
private theorem c2635_iso   : LeafIso 2635    := by decide +kernel
private theorem c2635_nof2  : NoF2ChkSq 2635  := by decide +kernel
private theorem c2635_nof3  : NoF3ChkSq 2635  := by decide +kernel
private theorem c2635_nof4z : NoF4zChkSq 2635 := by decide +kernel
theorem C'_2635 : C' 2635 :=
  ⟨c2635_sqf, c2635_range, c2635_ell, leafNSq_of_sq c2635_nsq, leafHAr_of_sq c2635_har,
   c2635_r, c2635_e', c2635_f1, leafS2_of_sq c2635_s2, leafS3_of_sq c2635_s3,
   c2635_iso, leafR8_of_sq c2635_nof2 c2635_nof3 c2635_nof4z⟩
theorem not_tile'_2635 (D : CongruentDissection 2635) : False :=
  not_tile_of_conditions' 2635 C'_2635 D

private theorem c2638_sqf   : LeafSqf 2638   := by decide +kernel
private theorem c2638_range : LeafRange 2638  := by decide +kernel
private theorem c2638_ell   : LeafEll 2638    := by decide +kernel
private theorem c2638_nsq   : NSqChkSq 2638   := by decide +kernel
private theorem c2638_har   : HArithChkSq 2638 := by decide +kernel
private theorem c2638_r     : LeafR 2638      := by decide +kernel
private theorem c2638_e'    : LeafE' 2638     := by decide +kernel
private theorem c2638_f1    : LeafF1 2638     := Or.inl (by decide)
private theorem c2638_s2    : S2ChkSq 2638    := by decide +kernel
private theorem c2638_s3    : S3ChkSq 2638    := by decide +kernel
private theorem c2638_iso   : LeafIso 2638    := by decide +kernel
private theorem c2638_nof2  : NoF2ChkSq 2638  := by decide +kernel
private theorem c2638_nof3  : NoF3ChkSq 2638  := by decide +kernel
private theorem c2638_nof4z : NoF4zChkSq 2638 := by decide +kernel
theorem C'_2638 : C' 2638 :=
  ⟨c2638_sqf, c2638_range, c2638_ell, leafNSq_of_sq c2638_nsq, leafHAr_of_sq c2638_har,
   c2638_r, c2638_e', c2638_f1, leafS2_of_sq c2638_s2, leafS3_of_sq c2638_s3,
   c2638_iso, leafR8_of_sq c2638_nof2 c2638_nof3 c2638_nof4z⟩
theorem not_tile'_2638 (D : CongruentDissection 2638) : False :=
  not_tile_of_conditions' 2638 C'_2638 D

private theorem c2639_sqf   : LeafSqf 2639   := by decide +kernel
private theorem c2639_range : LeafRange 2639  := by decide +kernel
private theorem c2639_ell   : LeafEll 2639    := by decide +kernel
private theorem c2639_nsq   : NSqChkSq 2639   := by decide +kernel
private theorem c2639_har   : HArithChkSq 2639 := by decide +kernel
private theorem c2639_r     : LeafR 2639      := by decide +kernel
private theorem c2639_e'    : LeafE' 2639     := by decide +kernel
private theorem c2639_f1    : LeafF1 2639     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2639_s2    : S2ChkSq 2639    := by decide +kernel
private theorem c2639_s3    : S3ChkSq 2639    := by decide +kernel
private theorem c2639_iso   : LeafIso 2639    := by decide +kernel
private theorem c2639_nof2  : NoF2ChkSq 2639  := by decide +kernel
private theorem c2639_nof3  : NoF3ChkSq 2639  := by decide +kernel
private theorem c2639_nof4z : NoF4zChkSq 2639 := by decide +kernel
theorem C'_2639 : C' 2639 :=
  ⟨c2639_sqf, c2639_range, c2639_ell, leafNSq_of_sq c2639_nsq, leafHAr_of_sq c2639_har,
   c2639_r, c2639_e', c2639_f1, leafS2_of_sq c2639_s2, leafS3_of_sq c2639_s3,
   c2639_iso, leafR8_of_sq c2639_nof2 c2639_nof3 c2639_nof4z⟩
theorem not_tile'_2639 (D : CongruentDissection 2639) : False :=
  not_tile_of_conditions' 2639 C'_2639 D

private theorem c2641_sqf   : LeafSqf 2641   := by decide +kernel
private theorem c2641_range : LeafRange 2641  := by decide +kernel
private theorem c2641_ell   : LeafEll 2641    := by decide +kernel
private theorem c2641_nsq   : NSqChkSq 2641   := by decide +kernel
private theorem c2641_har   : HArithChkSq 2641 := by decide +kernel
private theorem c2641_r     : LeafR 2641      := by decide +kernel
private theorem c2641_e'    : LeafE' 2641     := by decide +kernel
private theorem c2641_f1    : LeafF1 2641     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2641_s2    : S2ChkSq 2641    := by decide +kernel
private theorem c2641_s3    : S3ChkSq 2641    := by decide +kernel
private theorem c2641_iso   : LeafIso 2641    := by decide +kernel
private theorem c2641_nof2  : NoF2ChkSq 2641  := by decide +kernel
private theorem c2641_nof3  : NoF3ChkSq 2641  := by decide +kernel
private theorem c2641_nof4z : NoF4zChkSq 2641 := by decide +kernel
theorem C'_2641 : C' 2641 :=
  ⟨c2641_sqf, c2641_range, c2641_ell, leafNSq_of_sq c2641_nsq, leafHAr_of_sq c2641_har,
   c2641_r, c2641_e', c2641_f1, leafS2_of_sq c2641_s2, leafS3_of_sq c2641_s3,
   c2641_iso, leafR8_of_sq c2641_nof2 c2641_nof3 c2641_nof4z⟩
theorem not_tile'_2641 (D : CongruentDissection 2641) : False :=
  not_tile_of_conditions' 2641 C'_2641 D

private theorem c2643_sqf   : LeafSqf 2643   := by decide +kernel
private theorem c2643_range : LeafRange 2643  := by decide +kernel
private theorem c2643_ell   : LeafEll 2643    := by decide +kernel
private theorem c2643_nsq   : NSqChkSq 2643   := by decide +kernel
private theorem c2643_har   : HArithChkSq 2643 := by decide +kernel
private theorem c2643_r     : LeafR 2643      := by decide +kernel
private theorem c2643_e'    : LeafE' 2643     := by decide +kernel
private theorem c2643_f1    : LeafF1 2643     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2643_s2    : S2ChkSq 2643    := by decide +kernel
private theorem c2643_s3    : S3ChkSq 2643    := by decide +kernel
private theorem c2643_iso   : LeafIso 2643    := by decide +kernel
private theorem c2643_nof2  : NoF2ChkSq 2643  := by decide +kernel
private theorem c2643_nof3  : NoF3ChkSq 2643  := by decide +kernel
private theorem c2643_nof4z : NoF4zChkSq 2643 := by decide +kernel
theorem C'_2643 : C' 2643 :=
  ⟨c2643_sqf, c2643_range, c2643_ell, leafNSq_of_sq c2643_nsq, leafHAr_of_sq c2643_har,
   c2643_r, c2643_e', c2643_f1, leafS2_of_sq c2643_s2, leafS3_of_sq c2643_s3,
   c2643_iso, leafR8_of_sq c2643_nof2 c2643_nof3 c2643_nof4z⟩
theorem not_tile'_2643 (D : CongruentDissection 2643) : False :=
  not_tile_of_conditions' 2643 C'_2643 D

end Erdos634.Draft.AllN2

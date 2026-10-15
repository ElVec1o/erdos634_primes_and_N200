/- AllN2Check185: N = 3694, 3695, 3702, 3707, 3710
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3694_sqf   : LeafSqf 3694   := by decide +kernel
private theorem c3694_range : LeafRange 3694  := by decide +kernel
private theorem c3694_ell   : LeafEll 3694    := by decide +kernel
private theorem c3694_nsq   : NSqChkSq 3694   := by decide +kernel
private theorem c3694_har   : HArithChkSq 3694 := by decide +kernel
private theorem c3694_r     : LeafR 3694      := by decide +kernel
private theorem c3694_e'    : LeafE' 3694     := by decide +kernel
private theorem c3694_f1    : LeafF1 3694     := Or.inl (by decide)
private theorem c3694_s2    : S2ChkSq 3694    := by decide +kernel
private theorem c3694_s3    : S3ChkSq 3694    := by decide +kernel
private theorem c3694_iso   : LeafIso 3694    := by decide +kernel
private theorem c3694_nof2  : NoF2ChkSq 3694  := by decide +kernel
private theorem c3694_nof3  : NoF3ChkSq 3694  := by decide +kernel
private theorem c3694_nof4z : NoF4zChkSq 3694 := by decide +kernel
theorem C'_3694 : C' 3694 :=
  ⟨c3694_sqf, c3694_range, c3694_ell, leafNSq_of_sq c3694_nsq, leafHAr_of_sq c3694_har,
   c3694_r, c3694_e', c3694_f1, leafS2_of_sq c3694_s2, leafS3_of_sq c3694_s3,
   c3694_iso, leafR8_of_sq c3694_nof2 c3694_nof3 c3694_nof4z⟩
theorem not_tile'_3694 (D : CongruentDissection 3694) : False :=
  not_tile_of_conditions' 3694 C'_3694 D

private theorem c3695_sqf   : LeafSqf 3695   := by decide +kernel
private theorem c3695_range : LeafRange 3695  := by decide +kernel
private theorem c3695_ell   : LeafEll 3695    := by decide +kernel
private theorem c3695_nsq   : NSqChkSq 3695   := by decide +kernel
private theorem c3695_har   : HArithChkSq 3695 := by decide +kernel
private theorem c3695_r     : LeafR 3695      := by decide +kernel
private theorem c3695_e'    : LeafE' 3695     := by decide +kernel
private theorem c3695_f1    : LeafF1 3695     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3695_s2    : S2ChkSq 3695    := by decide +kernel
private theorem c3695_s3    : S3ChkSq 3695    := by decide +kernel
private theorem c3695_iso   : LeafIso 3695    := by decide +kernel
private theorem c3695_nof2  : NoF2ChkSq 3695  := by decide +kernel
private theorem c3695_nof3  : NoF3ChkSq 3695  := by decide +kernel
private theorem c3695_nof4z : NoF4zChkSq 3695 := by decide +kernel
theorem C'_3695 : C' 3695 :=
  ⟨c3695_sqf, c3695_range, c3695_ell, leafNSq_of_sq c3695_nsq, leafHAr_of_sq c3695_har,
   c3695_r, c3695_e', c3695_f1, leafS2_of_sq c3695_s2, leafS3_of_sq c3695_s3,
   c3695_iso, leafR8_of_sq c3695_nof2 c3695_nof3 c3695_nof4z⟩
theorem not_tile'_3695 (D : CongruentDissection 3695) : False :=
  not_tile_of_conditions' 3695 C'_3695 D

private theorem c3702_sqf   : LeafSqf 3702   := by decide +kernel
private theorem c3702_range : LeafRange 3702  := by decide +kernel
private theorem c3702_ell   : LeafEll 3702    := by decide +kernel
private theorem c3702_nsq   : NSqChkSq 3702   := by decide +kernel
private theorem c3702_har   : HArithChkSq 3702 := by decide +kernel
private theorem c3702_r     : LeafR 3702      := by decide +kernel
private theorem c3702_e'    : LeafE' 3702     := by decide +kernel
private theorem c3702_f1    : LeafF1 3702     := Or.inl (by decide)
private theorem c3702_s2    : S2ChkSq 3702    := by decide +kernel
private theorem c3702_s3    : S3ChkSq 3702    := by decide +kernel
private theorem c3702_iso   : LeafIso 3702    := by decide +kernel
private theorem c3702_nof2  : NoF2ChkSq 3702  := by decide +kernel
private theorem c3702_nof3  : NoF3ChkSq 3702  := by decide +kernel
private theorem c3702_nof4z : NoF4zChkSq 3702 := by decide +kernel
theorem C'_3702 : C' 3702 :=
  ⟨c3702_sqf, c3702_range, c3702_ell, leafNSq_of_sq c3702_nsq, leafHAr_of_sq c3702_har,
   c3702_r, c3702_e', c3702_f1, leafS2_of_sq c3702_s2, leafS3_of_sq c3702_s3,
   c3702_iso, leafR8_of_sq c3702_nof2 c3702_nof3 c3702_nof4z⟩
theorem not_tile'_3702 (D : CongruentDissection 3702) : False :=
  not_tile_of_conditions' 3702 C'_3702 D

private theorem c3707_sqf   : LeafSqf 3707   := by decide +kernel
private theorem c3707_range : LeafRange 3707  := by decide +kernel
private theorem c3707_ell   : LeafEll 3707    := by decide +kernel
private theorem c3707_nsq   : NSqChkSq 3707   := by decide +kernel
private theorem c3707_har   : HArithChkSq 3707 := by decide +kernel
private theorem c3707_r     : LeafR 3707      := by decide +kernel
private theorem c3707_e'    : LeafE' 3707     := by decide +kernel
private theorem c3707_f1    : LeafF1 3707     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3707_s2    : S2ChkSq 3707    := by decide +kernel
private theorem c3707_s3    : S3ChkSq 3707    := by decide +kernel
private theorem c3707_iso   : LeafIso 3707    := by decide +kernel
private theorem c3707_nof2  : NoF2ChkSq 3707  := by decide +kernel
private theorem c3707_nof3  : NoF3ChkSq 3707  := by decide +kernel
private theorem c3707_nof4z : NoF4zChkSq 3707 := by decide +kernel
theorem C'_3707 : C' 3707 :=
  ⟨c3707_sqf, c3707_range, c3707_ell, leafNSq_of_sq c3707_nsq, leafHAr_of_sq c3707_har,
   c3707_r, c3707_e', c3707_f1, leafS2_of_sq c3707_s2, leafS3_of_sq c3707_s3,
   c3707_iso, leafR8_of_sq c3707_nof2 c3707_nof3 c3707_nof4z⟩
theorem not_tile'_3707 (D : CongruentDissection 3707) : False :=
  not_tile_of_conditions' 3707 C'_3707 D

private theorem c3710_sqf   : LeafSqf 3710   := by decide +kernel
private theorem c3710_range : LeafRange 3710  := by decide +kernel
private theorem c3710_ell   : LeafEll 3710    := by decide +kernel
private theorem c3710_nsq   : NSqChkSq 3710   := by decide +kernel
private theorem c3710_har   : HArithChkSq 3710 := by decide +kernel
private theorem c3710_r     : LeafR 3710      := by decide +kernel
private theorem c3710_e'    : LeafE' 3710     := by decide +kernel
private theorem c3710_f1    : LeafF1 3710     := Or.inl (by decide)
private theorem c3710_s2    : S2ChkSq 3710    := by decide +kernel
private theorem c3710_s3    : S3ChkSq 3710    := by decide +kernel
private theorem c3710_iso   : LeafIso 3710    := by decide +kernel
private theorem c3710_nof2  : NoF2ChkSq 3710  := by decide +kernel
private theorem c3710_nof3  : NoF3ChkSq 3710  := by decide +kernel
private theorem c3710_nof4z : NoF4zChkSq 3710 := by decide +kernel
theorem C'_3710 : C' 3710 :=
  ⟨c3710_sqf, c3710_range, c3710_ell, leafNSq_of_sq c3710_nsq, leafHAr_of_sq c3710_har,
   c3710_r, c3710_e', c3710_f1, leafS2_of_sq c3710_s2, leafS3_of_sq c3710_s3,
   c3710_iso, leafR8_of_sq c3710_nof2 c3710_nof3 c3710_nof4z⟩
theorem not_tile'_3710 (D : CongruentDissection 3710) : False :=
  not_tile_of_conditions' 3710 C'_3710 D

end Erdos634.Draft.AllN2

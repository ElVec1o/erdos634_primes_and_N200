/- AllN2Check109: N = 2726, 2731, 2733, 2734, 2735
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2726_sqf   : LeafSqf 2726   := by decide +kernel
private theorem c2726_range : LeafRange 2726  := by decide +kernel
private theorem c2726_ell   : LeafEll 2726    := by decide +kernel
private theorem c2726_nsq   : NSqChkSq 2726   := by decide +kernel
private theorem c2726_har   : HArithChkSq 2726 := by decide +kernel
private theorem c2726_r     : LeafR 2726      := by decide +kernel
private theorem c2726_e'    : LeafE' 2726     := by decide +kernel
private theorem c2726_f1    : LeafF1 2726     := Or.inl (by decide)
private theorem c2726_s2    : S2ChkSq 2726    := by decide +kernel
private theorem c2726_s3    : S3ChkSq 2726    := by decide +kernel
private theorem c2726_iso   : LeafIso 2726    := by decide +kernel
private theorem c2726_nof2  : NoF2ChkSq 2726  := by decide +kernel
private theorem c2726_nof3  : NoF3ChkSq 2726  := by decide +kernel
private theorem c2726_nof4z : NoF4zChkSq 2726 := by decide +kernel
theorem C'_2726 : C' 2726 :=
  ⟨c2726_sqf, c2726_range, c2726_ell, leafNSq_of_sq c2726_nsq, leafHAr_of_sq c2726_har,
   c2726_r, c2726_e', c2726_f1, leafS2_of_sq c2726_s2, leafS3_of_sq c2726_s3,
   c2726_iso, leafR8_of_sq c2726_nof2 c2726_nof3 c2726_nof4z⟩
theorem not_tile'_2726 (D : CongruentDissection 2726) : False :=
  not_tile_of_conditions' 2726 C'_2726 D

private theorem c2731_sqf   : LeafSqf 2731   := by decide +kernel
private theorem c2731_range : LeafRange 2731  := by decide +kernel
private theorem c2731_ell   : LeafEll 2731    := by decide +kernel
private theorem c2731_nsq   : NSqChkSq 2731   := by decide +kernel
private theorem c2731_har   : HArithChkSq 2731 := by decide +kernel
private theorem c2731_r     : LeafR 2731      := by decide +kernel
private theorem c2731_e'    : LeafE' 2731     := by decide +kernel
private theorem c2731_f1    : LeafF1 2731     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2731_s2    : S2ChkSq 2731    := by decide +kernel
private theorem c2731_s3    : S3ChkSq 2731    := by decide +kernel
private theorem c2731_iso   : LeafIso 2731    := by decide +kernel
private theorem c2731_nof2  : NoF2ChkSq 2731  := by decide +kernel
private theorem c2731_nof3  : NoF3ChkSq 2731  := by decide +kernel
private theorem c2731_nof4z : NoF4zChkSq 2731 := by decide +kernel
theorem C'_2731 : C' 2731 :=
  ⟨c2731_sqf, c2731_range, c2731_ell, leafNSq_of_sq c2731_nsq, leafHAr_of_sq c2731_har,
   c2731_r, c2731_e', c2731_f1, leafS2_of_sq c2731_s2, leafS3_of_sq c2731_s3,
   c2731_iso, leafR8_of_sq c2731_nof2 c2731_nof3 c2731_nof4z⟩
theorem not_tile'_2731 (D : CongruentDissection 2731) : False :=
  not_tile_of_conditions' 2731 C'_2731 D

private theorem c2733_sqf   : LeafSqf 2733   := by decide +kernel
private theorem c2733_range : LeafRange 2733  := by decide +kernel
private theorem c2733_ell   : LeafEll 2733    := by decide +kernel
private theorem c2733_nsq   : NSqChkSq 2733   := by decide +kernel
private theorem c2733_har   : HArithChkSq 2733 := by decide +kernel
private theorem c2733_r     : LeafR 2733      := by decide +kernel
private theorem c2733_e'    : LeafE' 2733     := by decide +kernel
private theorem c2733_f1    : LeafF1 2733     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2733_s2    : S2ChkSq 2733    := by decide +kernel
private theorem c2733_s3    : S3ChkSq 2733    := by decide +kernel
private theorem c2733_iso   : LeafIso 2733    := by decide +kernel
private theorem c2733_nof2  : NoF2ChkSq 2733  := by decide +kernel
private theorem c2733_nof3  : NoF3ChkSq 2733  := by decide +kernel
private theorem c2733_nof4z : NoF4zChkSq 2733 := by decide +kernel
theorem C'_2733 : C' 2733 :=
  ⟨c2733_sqf, c2733_range, c2733_ell, leafNSq_of_sq c2733_nsq, leafHAr_of_sq c2733_har,
   c2733_r, c2733_e', c2733_f1, leafS2_of_sq c2733_s2, leafS3_of_sq c2733_s3,
   c2733_iso, leafR8_of_sq c2733_nof2 c2733_nof3 c2733_nof4z⟩
theorem not_tile'_2733 (D : CongruentDissection 2733) : False :=
  not_tile_of_conditions' 2733 C'_2733 D

private theorem c2734_sqf   : LeafSqf 2734   := by decide +kernel
private theorem c2734_range : LeafRange 2734  := by decide +kernel
private theorem c2734_ell   : LeafEll 2734    := by decide +kernel
private theorem c2734_nsq   : NSqChkSq 2734   := by decide +kernel
private theorem c2734_har   : HArithChkSq 2734 := by decide +kernel
private theorem c2734_r     : LeafR 2734      := by decide +kernel
private theorem c2734_e'    : LeafE' 2734     := by decide +kernel
private theorem c2734_f1    : LeafF1 2734     := Or.inl (by decide)
private theorem c2734_s2    : S2ChkSq 2734    := by decide +kernel
private theorem c2734_s3    : S3ChkSq 2734    := by decide +kernel
private theorem c2734_iso   : LeafIso 2734    := by decide +kernel
private theorem c2734_nof2  : NoF2ChkSq 2734  := by decide +kernel
private theorem c2734_nof3  : NoF3ChkSq 2734  := by decide +kernel
private theorem c2734_nof4z : NoF4zChkSq 2734 := by decide +kernel
theorem C'_2734 : C' 2734 :=
  ⟨c2734_sqf, c2734_range, c2734_ell, leafNSq_of_sq c2734_nsq, leafHAr_of_sq c2734_har,
   c2734_r, c2734_e', c2734_f1, leafS2_of_sq c2734_s2, leafS3_of_sq c2734_s3,
   c2734_iso, leafR8_of_sq c2734_nof2 c2734_nof3 c2734_nof4z⟩
theorem not_tile'_2734 (D : CongruentDissection 2734) : False :=
  not_tile_of_conditions' 2734 C'_2734 D

private theorem c2735_sqf   : LeafSqf 2735   := by decide +kernel
private theorem c2735_range : LeafRange 2735  := by decide +kernel
private theorem c2735_ell   : LeafEll 2735    := by decide +kernel
private theorem c2735_nsq   : NSqChkSq 2735   := by decide +kernel
private theorem c2735_har   : HArithChkSq 2735 := by decide +kernel
private theorem c2735_r     : LeafR 2735      := by decide +kernel
private theorem c2735_e'    : LeafE' 2735     := by decide +kernel
private theorem c2735_f1    : LeafF1 2735     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2735_s2    : S2ChkSq 2735    := by decide +kernel
private theorem c2735_s3    : S3ChkSq 2735    := by decide +kernel
private theorem c2735_iso   : LeafIso 2735    := by decide +kernel
private theorem c2735_nof2  : NoF2ChkSq 2735  := by decide +kernel
private theorem c2735_nof3  : NoF3ChkSq 2735  := by decide +kernel
private theorem c2735_nof4z : NoF4zChkSq 2735 := by decide +kernel
theorem C'_2735 : C' 2735 :=
  ⟨c2735_sqf, c2735_range, c2735_ell, leafNSq_of_sq c2735_nsq, leafHAr_of_sq c2735_har,
   c2735_r, c2735_e', c2735_f1, leafS2_of_sq c2735_s2, leafS3_of_sq c2735_s3,
   c2735_iso, leafR8_of_sq c2735_nof2 c2735_nof3 c2735_nof4z⟩
theorem not_tile'_2735 (D : CongruentDissection 2735) : False :=
  not_tile_of_conditions' 2735 C'_2735 D

end Erdos634.Draft.AllN2

/- AllN2Check258: N = 4642, 4643, 4646, 4647, 4651
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4642_sqf   : LeafSqf 4642   := by decide +kernel
private theorem c4642_range : LeafRange 4642  := by decide +kernel
private theorem c4642_ell   : LeafEll 4642    := by decide +kernel
private theorem c4642_nsq   : NSqChkSq 4642   := by decide +kernel
private theorem c4642_har   : HArithChkSq 4642 := by decide +kernel
private theorem c4642_r     : LeafR 4642      := by decide +kernel
private theorem c4642_e'    : LeafE' 4642     := by decide +kernel
private theorem c4642_f1    : LeafF1 4642     := Or.inl (by decide)
private theorem c4642_s2    : S2ChkSq 4642    := by decide +kernel
private theorem c4642_s3    : S3ChkSq 4642    := by decide +kernel
private theorem c4642_iso   : LeafIso 4642    := by decide +kernel
private theorem c4642_nof2  : NoF2ChkSq 4642  := by decide +kernel
private theorem c4642_nof3  : NoF3ChkSq 4642  := by decide +kernel
private theorem c4642_nof4z : NoF4zChkSq 4642 := by decide +kernel
theorem C'_4642 : C' 4642 :=
  ⟨c4642_sqf, c4642_range, c4642_ell, leafNSq_of_sq c4642_nsq, leafHAr_of_sq c4642_har,
   c4642_r, c4642_e', c4642_f1, leafS2_of_sq c4642_s2, leafS3_of_sq c4642_s3,
   c4642_iso, leafR8_of_sq c4642_nof2 c4642_nof3 c4642_nof4z⟩
theorem not_tile'_4642 (D : CongruentDissection 4642) : False :=
  not_tile_of_conditions' 4642 C'_4642 D

private theorem c4643_sqf   : LeafSqf 4643   := by decide +kernel
private theorem c4643_range : LeafRange 4643  := by decide +kernel
private theorem c4643_ell   : LeafEll 4643    := by decide +kernel
private theorem c4643_nsq   : NSqChkSq 4643   := by decide +kernel
private theorem c4643_har   : HArithChkSq 4643 := by decide +kernel
private theorem c4643_r     : LeafR 4643      := by decide +kernel
private theorem c4643_e'    : LeafE' 4643     := by decide +kernel
private theorem c4643_f1    : LeafF1 4643     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4643_s2    : S2ChkSq 4643    := by decide +kernel
private theorem c4643_s3    : S3ChkSq 4643    := by decide +kernel
private theorem c4643_iso   : LeafIso 4643    := by decide +kernel
private theorem c4643_nof2  : NoF2ChkSq 4643  := by decide +kernel
private theorem c4643_nof3  : NoF3ChkSq 4643  := by decide +kernel
private theorem c4643_nof4z : NoF4zChkSq 4643 := by decide +kernel
theorem C'_4643 : C' 4643 :=
  ⟨c4643_sqf, c4643_range, c4643_ell, leafNSq_of_sq c4643_nsq, leafHAr_of_sq c4643_har,
   c4643_r, c4643_e', c4643_f1, leafS2_of_sq c4643_s2, leafS3_of_sq c4643_s3,
   c4643_iso, leafR8_of_sq c4643_nof2 c4643_nof3 c4643_nof4z⟩
theorem not_tile'_4643 (D : CongruentDissection 4643) : False :=
  not_tile_of_conditions' 4643 C'_4643 D

private theorem c4646_sqf   : LeafSqf 4646   := by decide +kernel
private theorem c4646_range : LeafRange 4646  := by decide +kernel
private theorem c4646_ell   : LeafEll 4646    := by decide +kernel
private theorem c4646_nsq   : NSqChkSq 4646   := by decide +kernel
private theorem c4646_har   : HArithChkSq 4646 := by decide +kernel
private theorem c4646_r     : LeafR 4646      := by decide +kernel
private theorem c4646_e'    : LeafE' 4646     := by decide +kernel
private theorem c4646_f1    : LeafF1 4646     := Or.inl (by decide)
private theorem c4646_s2    : S2ChkSq 4646    := by decide +kernel
private theorem c4646_s3    : S3ChkSq 4646    := by decide +kernel
private theorem c4646_iso   : LeafIso 4646    := by decide +kernel
private theorem c4646_nof2  : NoF2ChkSq 4646  := by decide +kernel
private theorem c4646_nof3  : NoF3ChkSq 4646  := by decide +kernel
private theorem c4646_nof4z : NoF4zChkSq 4646 := by decide +kernel
theorem C'_4646 : C' 4646 :=
  ⟨c4646_sqf, c4646_range, c4646_ell, leafNSq_of_sq c4646_nsq, leafHAr_of_sq c4646_har,
   c4646_r, c4646_e', c4646_f1, leafS2_of_sq c4646_s2, leafS3_of_sq c4646_s3,
   c4646_iso, leafR8_of_sq c4646_nof2 c4646_nof3 c4646_nof4z⟩
theorem not_tile'_4646 (D : CongruentDissection 4646) : False :=
  not_tile_of_conditions' 4646 C'_4646 D

private theorem c4647_sqf   : LeafSqf 4647   := by decide +kernel
private theorem c4647_range : LeafRange 4647  := by decide +kernel
private theorem c4647_ell   : LeafEll 4647    := by decide +kernel
private theorem c4647_nsq   : NSqChkSq 4647   := by decide +kernel
private theorem c4647_har   : HArithChkSq 4647 := by decide +kernel
private theorem c4647_r     : LeafR 4647      := by decide +kernel
private theorem c4647_e'    : LeafE' 4647     := by decide +kernel
private theorem c4647_f1    : LeafF1 4647     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4647_s2    : S2ChkSq 4647    := by decide +kernel
private theorem c4647_s3    : S3ChkSq 4647    := by decide +kernel
private theorem c4647_iso   : LeafIso 4647    := by decide +kernel
private theorem c4647_nof2  : NoF2ChkSq 4647  := by decide +kernel
private theorem c4647_nof3  : NoF3ChkSq 4647  := by decide +kernel
private theorem c4647_nof4z : NoF4zChkSq 4647 := by decide +kernel
theorem C'_4647 : C' 4647 :=
  ⟨c4647_sqf, c4647_range, c4647_ell, leafNSq_of_sq c4647_nsq, leafHAr_of_sq c4647_har,
   c4647_r, c4647_e', c4647_f1, leafS2_of_sq c4647_s2, leafS3_of_sq c4647_s3,
   c4647_iso, leafR8_of_sq c4647_nof2 c4647_nof3 c4647_nof4z⟩
theorem not_tile'_4647 (D : CongruentDissection 4647) : False :=
  not_tile_of_conditions' 4647 C'_4647 D

private theorem c4651_sqf   : LeafSqf 4651   := by decide +kernel
private theorem c4651_range : LeafRange 4651  := by decide +kernel
private theorem c4651_ell   : LeafEll 4651    := by decide +kernel
private theorem c4651_nsq   : NSqChkSq 4651   := by decide +kernel
private theorem c4651_har   : HArithChkSq 4651 := by decide +kernel
private theorem c4651_r     : LeafR 4651      := by decide +kernel
private theorem c4651_e'    : LeafE' 4651     := by decide +kernel
private theorem c4651_f1    : LeafF1 4651     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4651_s2    : S2ChkSq 4651    := by decide +kernel
private theorem c4651_s3    : S3ChkSq 4651    := by decide +kernel
private theorem c4651_iso   : LeafIso 4651    := by decide +kernel
private theorem c4651_nof2  : NoF2ChkSq 4651  := by decide +kernel
private theorem c4651_nof3  : NoF3ChkSq 4651  := by decide +kernel
private theorem c4651_nof4z : NoF4zChkSq 4651 := by decide +kernel
theorem C'_4651 : C' 4651 :=
  ⟨c4651_sqf, c4651_range, c4651_ell, leafNSq_of_sq c4651_nsq, leafHAr_of_sq c4651_har,
   c4651_r, c4651_e', c4651_f1, leafS2_of_sq c4651_s2, leafS3_of_sq c4651_s3,
   c4651_iso, leafR8_of_sq c4651_nof2 c4651_nof3 c4651_nof4z⟩
theorem not_tile'_4651 (D : CongruentDissection 4651) : False :=
  not_tile_of_conditions' 4651 C'_4651 D

end Erdos634.Draft.AllN2

/- AllN2Check176: N = 3595, 3598, 3599, 3603, 3605
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3595_sqf   : LeafSqf 3595   := by decide +kernel
private theorem c3595_range : LeafRange 3595  := by decide +kernel
private theorem c3595_ell   : LeafEll 3595    := by decide +kernel
private theorem c3595_nsq   : NSqChkSq 3595   := by decide +kernel
private theorem c3595_har   : HArithChkSq 3595 := by decide +kernel
private theorem c3595_r     : LeafR 3595      := by decide +kernel
private theorem c3595_e'    : LeafE' 3595     := by decide +kernel
private theorem c3595_f1    : LeafF1 3595     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3595_s2    : S2ChkSq 3595    := by decide +kernel
private theorem c3595_s3    : S3ChkSq 3595    := by decide +kernel
private theorem c3595_iso   : LeafIso 3595    := by decide +kernel
private theorem c3595_nof2  : NoF2ChkSq 3595  := by decide +kernel
private theorem c3595_nof3  : NoF3ChkSq 3595  := by decide +kernel
private theorem c3595_nof4z : NoF4zChkSq 3595 := by decide +kernel
theorem C'_3595 : C' 3595 :=
  ⟨c3595_sqf, c3595_range, c3595_ell, leafNSq_of_sq c3595_nsq, leafHAr_of_sq c3595_har,
   c3595_r, c3595_e', c3595_f1, leafS2_of_sq c3595_s2, leafS3_of_sq c3595_s3,
   c3595_iso, leafR8_of_sq c3595_nof2 c3595_nof3 c3595_nof4z⟩
theorem not_tile'_3595 (D : CongruentDissection 3595) : False :=
  not_tile_of_conditions' 3595 C'_3595 D

private theorem c3598_sqf   : LeafSqf 3598   := by decide +kernel
private theorem c3598_range : LeafRange 3598  := by decide +kernel
private theorem c3598_ell   : LeafEll 3598    := by decide +kernel
private theorem c3598_nsq   : NSqChkSq 3598   := by decide +kernel
private theorem c3598_har   : HArithChkSq 3598 := by decide +kernel
private theorem c3598_r     : LeafR 3598      := by decide +kernel
private theorem c3598_e'    : LeafE' 3598     := by decide +kernel
private theorem c3598_f1    : LeafF1 3598     := Or.inl (by decide)
private theorem c3598_s2    : S2ChkSq 3598    := by decide +kernel
private theorem c3598_s3    : S3ChkSq 3598    := by decide +kernel
private theorem c3598_iso   : LeafIso 3598    := by decide +kernel
private theorem c3598_nof2  : NoF2ChkSq 3598  := by decide +kernel
private theorem c3598_nof3  : NoF3ChkSq 3598  := by decide +kernel
private theorem c3598_nof4z : NoF4zChkSq 3598 := by decide +kernel
theorem C'_3598 : C' 3598 :=
  ⟨c3598_sqf, c3598_range, c3598_ell, leafNSq_of_sq c3598_nsq, leafHAr_of_sq c3598_har,
   c3598_r, c3598_e', c3598_f1, leafS2_of_sq c3598_s2, leafS3_of_sq c3598_s3,
   c3598_iso, leafR8_of_sq c3598_nof2 c3598_nof3 c3598_nof4z⟩
theorem not_tile'_3598 (D : CongruentDissection 3598) : False :=
  not_tile_of_conditions' 3598 C'_3598 D

private theorem c3599_sqf   : LeafSqf 3599   := by decide +kernel
private theorem c3599_range : LeafRange 3599  := by decide +kernel
private theorem c3599_ell   : LeafEll 3599    := by decide +kernel
private theorem c3599_nsq   : NSqChkSq 3599   := by decide +kernel
private theorem c3599_har   : HArithChkSq 3599 := by decide +kernel
private theorem c3599_r     : LeafR 3599      := by decide +kernel
private theorem c3599_e'    : LeafE' 3599     := by decide +kernel
private theorem c3599_f1    : LeafF1 3599     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3599_s2    : S2ChkSq 3599    := by decide +kernel
private theorem c3599_s3    : S3ChkSq 3599    := by decide +kernel
private theorem c3599_iso   : LeafIso 3599    := by decide +kernel
private theorem c3599_nof2  : NoF2ChkSq 3599  := by decide +kernel
private theorem c3599_nof3  : NoF3ChkSq 3599  := by decide +kernel
private theorem c3599_nof4z : NoF4zChkSq 3599 := by decide +kernel
theorem C'_3599 : C' 3599 :=
  ⟨c3599_sqf, c3599_range, c3599_ell, leafNSq_of_sq c3599_nsq, leafHAr_of_sq c3599_har,
   c3599_r, c3599_e', c3599_f1, leafS2_of_sq c3599_s2, leafS3_of_sq c3599_s3,
   c3599_iso, leafR8_of_sq c3599_nof2 c3599_nof3 c3599_nof4z⟩
theorem not_tile'_3599 (D : CongruentDissection 3599) : False :=
  not_tile_of_conditions' 3599 C'_3599 D

private theorem c3603_sqf   : LeafSqf 3603   := by decide +kernel
private theorem c3603_range : LeafRange 3603  := by decide +kernel
private theorem c3603_ell   : LeafEll 3603    := by decide +kernel
private theorem c3603_nsq   : NSqChkSq 3603   := by decide +kernel
private theorem c3603_har   : HArithChkSq 3603 := by decide +kernel
private theorem c3603_r     : LeafR 3603      := by decide +kernel
private theorem c3603_e'    : LeafE' 3603     := by decide +kernel
private theorem c3603_f1    : LeafF1 3603     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3603_s2    : S2ChkSq 3603    := by decide +kernel
private theorem c3603_s3    : S3ChkSq 3603    := by decide +kernel
private theorem c3603_iso   : LeafIso 3603    := by decide +kernel
private theorem c3603_nof2  : NoF2ChkSq 3603  := by decide +kernel
private theorem c3603_nof3  : NoF3ChkSq 3603  := by decide +kernel
private theorem c3603_nof4z : NoF4zChkSq 3603 := by decide +kernel
theorem C'_3603 : C' 3603 :=
  ⟨c3603_sqf, c3603_range, c3603_ell, leafNSq_of_sq c3603_nsq, leafHAr_of_sq c3603_har,
   c3603_r, c3603_e', c3603_f1, leafS2_of_sq c3603_s2, leafS3_of_sq c3603_s3,
   c3603_iso, leafR8_of_sq c3603_nof2 c3603_nof3 c3603_nof4z⟩
theorem not_tile'_3603 (D : CongruentDissection 3603) : False :=
  not_tile_of_conditions' 3603 C'_3603 D

private theorem c3605_sqf   : LeafSqf 3605   := by decide +kernel
private theorem c3605_range : LeafRange 3605  := by decide +kernel
private theorem c3605_ell   : LeafEll 3605    := by decide +kernel
private theorem c3605_nsq   : NSqChkSq 3605   := by decide +kernel
private theorem c3605_har   : HArithChkSq 3605 := by decide +kernel
private theorem c3605_r     : LeafR 3605      := by decide +kernel
private theorem c3605_e'    : LeafE' 3605     := by decide +kernel
private theorem c3605_f1    : LeafF1 3605     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3605_s2    : S2ChkSq 3605    := by decide +kernel
private theorem c3605_s3    : S3ChkSq 3605    := by decide +kernel
private theorem c3605_iso   : LeafIso 3605    := by decide +kernel
private theorem c3605_nof2  : NoF2ChkSq 3605  := by decide +kernel
private theorem c3605_nof3  : NoF3ChkSq 3605  := by decide +kernel
private theorem c3605_nof4z : NoF4zChkSq 3605 := by decide +kernel
theorem C'_3605 : C' 3605 :=
  ⟨c3605_sqf, c3605_range, c3605_ell, leafNSq_of_sq c3605_nsq, leafHAr_of_sq c3605_har,
   c3605_r, c3605_e', c3605_f1, leafS2_of_sq c3605_s2, leafS3_of_sq c3605_s3,
   c3605_iso, leafR8_of_sq c3605_nof2 c3605_nof3 c3605_nof4z⟩
theorem not_tile'_3605 (D : CongruentDissection 3605) : False :=
  not_tile_of_conditions' 3605 C'_3605 D

end Erdos634.Draft.AllN2

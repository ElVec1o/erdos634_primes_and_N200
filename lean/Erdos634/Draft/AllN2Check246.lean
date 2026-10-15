/- AllN2Check246: N = 4494, 4495, 4497, 4499, 4501
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4494_sqf   : LeafSqf 4494   := by decide +kernel
private theorem c4494_range : LeafRange 4494  := by decide +kernel
private theorem c4494_ell   : LeafEll 4494    := by decide +kernel
private theorem c4494_nsq   : NSqChkSq 4494   := by decide +kernel
private theorem c4494_har   : HArithChkSq 4494 := by decide +kernel
private theorem c4494_r     : LeafR 4494      := by decide +kernel
private theorem c4494_e'    : LeafE' 4494     := by decide +kernel
private theorem c4494_f1    : LeafF1 4494     := Or.inl (by decide)
private theorem c4494_s2    : S2ChkSq 4494    := by decide +kernel
private theorem c4494_s3    : S3ChkSq 4494    := by decide +kernel
private theorem c4494_iso   : LeafIso 4494    := by decide +kernel
private theorem c4494_nof2  : NoF2ChkSq 4494  := by decide +kernel
private theorem c4494_nof3  : NoF3ChkSq 4494  := by decide +kernel
private theorem c4494_nof4z : NoF4zChkSq 4494 := by decide +kernel
theorem C'_4494 : C' 4494 :=
  ⟨c4494_sqf, c4494_range, c4494_ell, leafNSq_of_sq c4494_nsq, leafHAr_of_sq c4494_har,
   c4494_r, c4494_e', c4494_f1, leafS2_of_sq c4494_s2, leafS3_of_sq c4494_s3,
   c4494_iso, leafR8_of_sq c4494_nof2 c4494_nof3 c4494_nof4z⟩
theorem not_tile'_4494 (D : CongruentDissection 4494) : False :=
  not_tile_of_conditions' 4494 C'_4494 D

private theorem c4495_sqf   : LeafSqf 4495   := by decide +kernel
private theorem c4495_range : LeafRange 4495  := by decide +kernel
private theorem c4495_ell   : LeafEll 4495    := by decide +kernel
private theorem c4495_nsq   : NSqChkSq 4495   := by decide +kernel
private theorem c4495_har   : HArithChkSq 4495 := by decide +kernel
private theorem c4495_r     : LeafR 4495      := by decide +kernel
private theorem c4495_e'    : LeafE' 4495     := by decide +kernel
private theorem c4495_f1    : LeafF1 4495     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4495_s2    : S2ChkSq 4495    := by decide +kernel
private theorem c4495_s3    : S3ChkSq 4495    := by decide +kernel
private theorem c4495_iso   : LeafIso 4495    := by decide +kernel
private theorem c4495_nof2  : NoF2ChkSq 4495  := by decide +kernel
private theorem c4495_nof3  : NoF3ChkSq 4495  := by decide +kernel
private theorem c4495_nof4z : NoF4zChkSq 4495 := by decide +kernel
theorem C'_4495 : C' 4495 :=
  ⟨c4495_sqf, c4495_range, c4495_ell, leafNSq_of_sq c4495_nsq, leafHAr_of_sq c4495_har,
   c4495_r, c4495_e', c4495_f1, leafS2_of_sq c4495_s2, leafS3_of_sq c4495_s3,
   c4495_iso, leafR8_of_sq c4495_nof2 c4495_nof3 c4495_nof4z⟩
theorem not_tile'_4495 (D : CongruentDissection 4495) : False :=
  not_tile_of_conditions' 4495 C'_4495 D

private theorem c4497_sqf   : LeafSqf 4497   := by decide +kernel
private theorem c4497_range : LeafRange 4497  := by decide +kernel
private theorem c4497_ell   : LeafEll 4497    := by decide +kernel
private theorem c4497_nsq   : NSqChkSq 4497   := by decide +kernel
private theorem c4497_har   : HArithChkSq 4497 := by decide +kernel
private theorem c4497_r     : LeafR 4497      := by decide +kernel
private theorem c4497_e'    : LeafE' 4497     := by decide +kernel
private theorem c4497_f1    : LeafF1 4497     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4497_s2    : S2ChkSq 4497    := by decide +kernel
private theorem c4497_s3    : S3ChkSq 4497    := by decide +kernel
private theorem c4497_iso   : LeafIso 4497    := by decide +kernel
private theorem c4497_nof2  : NoF2ChkSq 4497  := by decide +kernel
private theorem c4497_nof3  : NoF3ChkSq 4497  := by decide +kernel
private theorem c4497_nof4z : NoF4zChkSq 4497 := by decide +kernel
theorem C'_4497 : C' 4497 :=
  ⟨c4497_sqf, c4497_range, c4497_ell, leafNSq_of_sq c4497_nsq, leafHAr_of_sq c4497_har,
   c4497_r, c4497_e', c4497_f1, leafS2_of_sq c4497_s2, leafS3_of_sq c4497_s3,
   c4497_iso, leafR8_of_sq c4497_nof2 c4497_nof3 c4497_nof4z⟩
theorem not_tile'_4497 (D : CongruentDissection 4497) : False :=
  not_tile_of_conditions' 4497 C'_4497 D

private theorem c4499_sqf   : LeafSqf 4499   := by decide +kernel
private theorem c4499_range : LeafRange 4499  := by decide +kernel
private theorem c4499_ell   : LeafEll 4499    := by decide +kernel
private theorem c4499_nsq   : NSqChkSq 4499   := by decide +kernel
private theorem c4499_har   : HArithChkSq 4499 := by decide +kernel
private theorem c4499_r     : LeafR 4499      := by decide +kernel
private theorem c4499_e'    : LeafE' 4499     := by decide +kernel
private theorem c4499_f1    : LeafF1 4499     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4499_s2    : S2ChkSq 4499    := by decide +kernel
private theorem c4499_s3    : S3ChkSq 4499    := by decide +kernel
private theorem c4499_iso   : LeafIso 4499    := by decide +kernel
private theorem c4499_nof2  : NoF2ChkSq 4499  := by decide +kernel
private theorem c4499_nof3  : NoF3ChkSq 4499  := by decide +kernel
private theorem c4499_nof4z : NoF4zChkSq 4499 := by decide +kernel
theorem C'_4499 : C' 4499 :=
  ⟨c4499_sqf, c4499_range, c4499_ell, leafNSq_of_sq c4499_nsq, leafHAr_of_sq c4499_har,
   c4499_r, c4499_e', c4499_f1, leafS2_of_sq c4499_s2, leafS3_of_sq c4499_s3,
   c4499_iso, leafR8_of_sq c4499_nof2 c4499_nof3 c4499_nof4z⟩
theorem not_tile'_4499 (D : CongruentDissection 4499) : False :=
  not_tile_of_conditions' 4499 C'_4499 D

private theorem c4501_sqf   : LeafSqf 4501   := by decide +kernel
private theorem c4501_range : LeafRange 4501  := by decide +kernel
private theorem c4501_ell   : LeafEll 4501    := by decide +kernel
private theorem c4501_nsq   : NSqChkSq 4501   := by decide +kernel
private theorem c4501_har   : HArithChkSq 4501 := by decide +kernel
private theorem c4501_r     : LeafR 4501      := by decide +kernel
private theorem c4501_e'    : LeafE' 4501     := by decide +kernel
private theorem c4501_f1    : LeafF1 4501     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4501_s2    : S2ChkSq 4501    := by decide +kernel
private theorem c4501_s3    : S3ChkSq 4501    := by decide +kernel
private theorem c4501_iso   : LeafIso 4501    := by decide +kernel
private theorem c4501_nof2  : NoF2ChkSq 4501  := by decide +kernel
private theorem c4501_nof3  : NoF3ChkSq 4501  := by decide +kernel
private theorem c4501_nof4z : NoF4zChkSq 4501 := by decide +kernel
theorem C'_4501 : C' 4501 :=
  ⟨c4501_sqf, c4501_range, c4501_ell, leafNSq_of_sq c4501_nsq, leafHAr_of_sq c4501_har,
   c4501_r, c4501_e', c4501_f1, leafS2_of_sq c4501_s2, leafS3_of_sq c4501_s3,
   c4501_iso, leafR8_of_sq c4501_nof2 c4501_nof3 c4501_nof4z⟩
theorem not_tile'_4501 (D : CongruentDissection 4501) : False :=
  not_tile_of_conditions' 4501 C'_4501 D

end Erdos634.Draft.AllN2

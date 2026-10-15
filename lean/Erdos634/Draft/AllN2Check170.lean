/- AllN2Check170: N = 3514, 3515, 3518, 3521, 3522
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3514_sqf   : LeafSqf 3514   := by decide +kernel
private theorem c3514_range : LeafRange 3514  := by decide +kernel
private theorem c3514_ell   : LeafEll 3514    := by decide +kernel
private theorem c3514_nsq   : NSqChkSq 3514   := by decide +kernel
private theorem c3514_har   : HArithChkSq 3514 := by decide +kernel
private theorem c3514_r     : LeafR 3514      := by decide +kernel
private theorem c3514_e'    : LeafE' 3514     := by decide +kernel
private theorem c3514_f1    : LeafF1 3514     := Or.inl (by decide)
private theorem c3514_s2    : S2ChkSq 3514    := by decide +kernel
private theorem c3514_s3    : S3ChkSq 3514    := by decide +kernel
private theorem c3514_iso   : LeafIso 3514    := by decide +kernel
private theorem c3514_nof2  : NoF2ChkSq 3514  := by decide +kernel
private theorem c3514_nof3  : NoF3ChkSq 3514  := by decide +kernel
private theorem c3514_nof4z : NoF4zChkSq 3514 := by decide +kernel
theorem C'_3514 : C' 3514 :=
  ⟨c3514_sqf, c3514_range, c3514_ell, leafNSq_of_sq c3514_nsq, leafHAr_of_sq c3514_har,
   c3514_r, c3514_e', c3514_f1, leafS2_of_sq c3514_s2, leafS3_of_sq c3514_s3,
   c3514_iso, leafR8_of_sq c3514_nof2 c3514_nof3 c3514_nof4z⟩
theorem not_tile'_3514 (D : CongruentDissection 3514) : False :=
  not_tile_of_conditions' 3514 C'_3514 D

private theorem c3515_sqf   : LeafSqf 3515   := by decide +kernel
private theorem c3515_range : LeafRange 3515  := by decide +kernel
private theorem c3515_ell   : LeafEll 3515    := by decide +kernel
private theorem c3515_nsq   : NSqChkSq 3515   := by decide +kernel
private theorem c3515_har   : HArithChkSq 3515 := by decide +kernel
private theorem c3515_r     : LeafR 3515      := by decide +kernel
private theorem c3515_e'    : LeafE' 3515     := by decide +kernel
private theorem c3515_f1    : LeafF1 3515     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3515_s2    : S2ChkSq 3515    := by decide +kernel
private theorem c3515_s3    : S3ChkSq 3515    := by decide +kernel
private theorem c3515_iso   : LeafIso 3515    := by decide +kernel
private theorem c3515_nof2  : NoF2ChkSq 3515  := by decide +kernel
private theorem c3515_nof3  : NoF3ChkSq 3515  := by decide +kernel
private theorem c3515_nof4z : NoF4zChkSq 3515 := by decide +kernel
theorem C'_3515 : C' 3515 :=
  ⟨c3515_sqf, c3515_range, c3515_ell, leafNSq_of_sq c3515_nsq, leafHAr_of_sq c3515_har,
   c3515_r, c3515_e', c3515_f1, leafS2_of_sq c3515_s2, leafS3_of_sq c3515_s3,
   c3515_iso, leafR8_of_sq c3515_nof2 c3515_nof3 c3515_nof4z⟩
theorem not_tile'_3515 (D : CongruentDissection 3515) : False :=
  not_tile_of_conditions' 3515 C'_3515 D

private theorem c3518_sqf   : LeafSqf 3518   := by decide +kernel
private theorem c3518_range : LeafRange 3518  := by decide +kernel
private theorem c3518_ell   : LeafEll 3518    := by decide +kernel
private theorem c3518_nsq   : NSqChkSq 3518   := by decide +kernel
private theorem c3518_har   : HArithChkSq 3518 := by decide +kernel
private theorem c3518_r     : LeafR 3518      := by decide +kernel
private theorem c3518_e'    : LeafE' 3518     := by decide +kernel
private theorem c3518_f1    : LeafF1 3518     := Or.inl (by decide)
private theorem c3518_s2    : S2ChkSq 3518    := by decide +kernel
private theorem c3518_s3    : S3ChkSq 3518    := by decide +kernel
private theorem c3518_iso   : LeafIso 3518    := by decide +kernel
private theorem c3518_nof2  : NoF2ChkSq 3518  := by decide +kernel
private theorem c3518_nof3  : NoF3ChkSq 3518  := by decide +kernel
private theorem c3518_nof4z : NoF4zChkSq 3518 := by decide +kernel
theorem C'_3518 : C' 3518 :=
  ⟨c3518_sqf, c3518_range, c3518_ell, leafNSq_of_sq c3518_nsq, leafHAr_of_sq c3518_har,
   c3518_r, c3518_e', c3518_f1, leafS2_of_sq c3518_s2, leafS3_of_sq c3518_s3,
   c3518_iso, leafR8_of_sq c3518_nof2 c3518_nof3 c3518_nof4z⟩
theorem not_tile'_3518 (D : CongruentDissection 3518) : False :=
  not_tile_of_conditions' 3518 C'_3518 D

private theorem c3521_sqf   : LeafSqf 3521   := by decide +kernel
private theorem c3521_range : LeafRange 3521  := by decide +kernel
private theorem c3521_ell   : LeafEll 3521    := by decide +kernel
private theorem c3521_nsq   : NSqChkSq 3521   := by decide +kernel
private theorem c3521_har   : HArithChkSq 3521 := by decide +kernel
private theorem c3521_r     : LeafR 3521      := by decide +kernel
private theorem c3521_e'    : LeafE' 3521     := by decide +kernel
private theorem c3521_f1    : LeafF1 3521     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3521_s2    : S2ChkSq 3521    := by decide +kernel
private theorem c3521_s3    : S3ChkSq 3521    := by decide +kernel
private theorem c3521_iso   : LeafIso 3521    := by decide +kernel
private theorem c3521_nof2  : NoF2ChkSq 3521  := by decide +kernel
private theorem c3521_nof3  : NoF3ChkSq 3521  := by decide +kernel
private theorem c3521_nof4z : NoF4zChkSq 3521 := by decide +kernel
theorem C'_3521 : C' 3521 :=
  ⟨c3521_sqf, c3521_range, c3521_ell, leafNSq_of_sq c3521_nsq, leafHAr_of_sq c3521_har,
   c3521_r, c3521_e', c3521_f1, leafS2_of_sq c3521_s2, leafS3_of_sq c3521_s3,
   c3521_iso, leafR8_of_sq c3521_nof2 c3521_nof3 c3521_nof4z⟩
theorem not_tile'_3521 (D : CongruentDissection 3521) : False :=
  not_tile_of_conditions' 3521 C'_3521 D

private theorem c3522_sqf   : LeafSqf 3522   := by decide +kernel
private theorem c3522_range : LeafRange 3522  := by decide +kernel
private theorem c3522_ell   : LeafEll 3522    := by decide +kernel
private theorem c3522_nsq   : NSqChkSq 3522   := by decide +kernel
private theorem c3522_har   : HArithChkSq 3522 := by decide +kernel
private theorem c3522_r     : LeafR 3522      := by decide +kernel
private theorem c3522_e'    : LeafE' 3522     := by decide +kernel
private theorem c3522_f1    : LeafF1 3522     := Or.inl (by decide)
private theorem c3522_s2    : S2ChkSq 3522    := by decide +kernel
private theorem c3522_s3    : S3ChkSq 3522    := by decide +kernel
private theorem c3522_iso   : LeafIso 3522    := by decide +kernel
private theorem c3522_nof2  : NoF2ChkSq 3522  := by decide +kernel
private theorem c3522_nof3  : NoF3ChkSq 3522  := by decide +kernel
private theorem c3522_nof4z : NoF4zChkSq 3522 := by decide +kernel
theorem C'_3522 : C' 3522 :=
  ⟨c3522_sqf, c3522_range, c3522_ell, leafNSq_of_sq c3522_nsq, leafHAr_of_sq c3522_har,
   c3522_r, c3522_e', c3522_f1, leafS2_of_sq c3522_s2, leafS3_of_sq c3522_s3,
   c3522_iso, leafR8_of_sq c3522_nof2 c3522_nof3 c3522_nof4z⟩
theorem not_tile'_3522 (D : CongruentDissection 3522) : False :=
  not_tile_of_conditions' 3522 C'_3522 D

end Erdos634.Draft.AllN2

/- AllN2Check173: N = 3558, 3559, 3561, 3563, 3565
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3558_sqf   : LeafSqf 3558   := by decide +kernel
private theorem c3558_range : LeafRange 3558  := by decide +kernel
private theorem c3558_ell   : LeafEll 3558    := by decide +kernel
private theorem c3558_nsq   : NSqChkSq 3558   := by decide +kernel
private theorem c3558_har   : HArithChkSq 3558 := by decide +kernel
private theorem c3558_r     : LeafR 3558      := by decide +kernel
private theorem c3558_e'    : LeafE' 3558     := by decide +kernel
private theorem c3558_f1    : LeafF1 3558     := Or.inl (by decide)
private theorem c3558_s2    : S2ChkSq 3558    := by decide +kernel
private theorem c3558_s3    : S3ChkSq 3558    := by decide +kernel
private theorem c3558_iso   : LeafIso 3558    := by decide +kernel
private theorem c3558_nof2  : NoF2ChkSq 3558  := by decide +kernel
private theorem c3558_nof3  : NoF3ChkSq 3558  := by decide +kernel
private theorem c3558_nof4z : NoF4zChkSq 3558 := by decide +kernel
theorem C'_3558 : C' 3558 :=
  ⟨c3558_sqf, c3558_range, c3558_ell, leafNSq_of_sq c3558_nsq, leafHAr_of_sq c3558_har,
   c3558_r, c3558_e', c3558_f1, leafS2_of_sq c3558_s2, leafS3_of_sq c3558_s3,
   c3558_iso, leafR8_of_sq c3558_nof2 c3558_nof3 c3558_nof4z⟩
theorem not_tile'_3558 (D : CongruentDissection 3558) : False :=
  not_tile_of_conditions' 3558 C'_3558 D

private theorem c3559_sqf   : LeafSqf 3559   := by decide +kernel
private theorem c3559_range : LeafRange 3559  := by decide +kernel
private theorem c3559_ell   : LeafEll 3559    := by decide +kernel
private theorem c3559_nsq   : NSqChkSq 3559   := by decide +kernel
private theorem c3559_har   : HArithChkSq 3559 := by decide +kernel
private theorem c3559_r     : LeafR 3559      := by decide +kernel
private theorem c3559_e'    : LeafE' 3559     := by decide +kernel
private theorem c3559_f1    : LeafF1 3559     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3559_s2    : S2ChkSq 3559    := by decide +kernel
private theorem c3559_s3    : S3ChkSq 3559    := by decide +kernel
private theorem c3559_iso   : LeafIso 3559    := by decide +kernel
private theorem c3559_nof2  : NoF2ChkSq 3559  := by decide +kernel
private theorem c3559_nof3  : NoF3ChkSq 3559  := by decide +kernel
private theorem c3559_nof4z : NoF4zChkSq 3559 := by decide +kernel
theorem C'_3559 : C' 3559 :=
  ⟨c3559_sqf, c3559_range, c3559_ell, leafNSq_of_sq c3559_nsq, leafHAr_of_sq c3559_har,
   c3559_r, c3559_e', c3559_f1, leafS2_of_sq c3559_s2, leafS3_of_sq c3559_s3,
   c3559_iso, leafR8_of_sq c3559_nof2 c3559_nof3 c3559_nof4z⟩
theorem not_tile'_3559 (D : CongruentDissection 3559) : False :=
  not_tile_of_conditions' 3559 C'_3559 D

private theorem c3561_sqf   : LeafSqf 3561   := by decide +kernel
private theorem c3561_range : LeafRange 3561  := by decide +kernel
private theorem c3561_ell   : LeafEll 3561    := by decide +kernel
private theorem c3561_nsq   : NSqChkSq 3561   := by decide +kernel
private theorem c3561_har   : HArithChkSq 3561 := by decide +kernel
private theorem c3561_r     : LeafR 3561      := by decide +kernel
private theorem c3561_e'    : LeafE' 3561     := by decide +kernel
private theorem c3561_f1    : LeafF1 3561     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3561_s2    : S2ChkSq 3561    := by decide +kernel
private theorem c3561_s3    : S3ChkSq 3561    := by decide +kernel
private theorem c3561_iso   : LeafIso 3561    := by decide +kernel
private theorem c3561_nof2  : NoF2ChkSq 3561  := by decide +kernel
private theorem c3561_nof3  : NoF3ChkSq 3561  := by decide +kernel
private theorem c3561_nof4z : NoF4zChkSq 3561 := by decide +kernel
theorem C'_3561 : C' 3561 :=
  ⟨c3561_sqf, c3561_range, c3561_ell, leafNSq_of_sq c3561_nsq, leafHAr_of_sq c3561_har,
   c3561_r, c3561_e', c3561_f1, leafS2_of_sq c3561_s2, leafS3_of_sq c3561_s3,
   c3561_iso, leafR8_of_sq c3561_nof2 c3561_nof3 c3561_nof4z⟩
theorem not_tile'_3561 (D : CongruentDissection 3561) : False :=
  not_tile_of_conditions' 3561 C'_3561 D

private theorem c3563_sqf   : LeafSqf 3563   := by decide +kernel
private theorem c3563_range : LeafRange 3563  := by decide +kernel
private theorem c3563_ell   : LeafEll 3563    := by decide +kernel
private theorem c3563_nsq   : NSqChkSq 3563   := by decide +kernel
private theorem c3563_har   : HArithChkSq 3563 := by decide +kernel
private theorem c3563_r     : LeafR 3563      := by decide +kernel
private theorem c3563_e'    : LeafE' 3563     := by decide +kernel
private theorem c3563_f1    : LeafF1 3563     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3563_s2    : S2ChkSq 3563    := by decide +kernel
private theorem c3563_s3    : S3ChkSq 3563    := by decide +kernel
private theorem c3563_iso   : LeafIso 3563    := by decide +kernel
private theorem c3563_nof2  : NoF2ChkSq 3563  := by decide +kernel
private theorem c3563_nof3  : NoF3ChkSq 3563  := by decide +kernel
private theorem c3563_nof4z : NoF4zChkSq 3563 := by decide +kernel
theorem C'_3563 : C' 3563 :=
  ⟨c3563_sqf, c3563_range, c3563_ell, leafNSq_of_sq c3563_nsq, leafHAr_of_sq c3563_har,
   c3563_r, c3563_e', c3563_f1, leafS2_of_sq c3563_s2, leafS3_of_sq c3563_s3,
   c3563_iso, leafR8_of_sq c3563_nof2 c3563_nof3 c3563_nof4z⟩
theorem not_tile'_3563 (D : CongruentDissection 3563) : False :=
  not_tile_of_conditions' 3563 C'_3563 D

private theorem c3565_sqf   : LeafSqf 3565   := by decide +kernel
private theorem c3565_range : LeafRange 3565  := by decide +kernel
private theorem c3565_ell   : LeafEll 3565    := by decide +kernel
private theorem c3565_nsq   : NSqChkSq 3565   := by decide +kernel
private theorem c3565_har   : HArithChkSq 3565 := by decide +kernel
private theorem c3565_r     : LeafR 3565      := by decide +kernel
private theorem c3565_e'    : LeafE' 3565     := by decide +kernel
private theorem c3565_f1    : LeafF1 3565     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3565_s2    : S2ChkSq 3565    := by decide +kernel
private theorem c3565_s3    : S3ChkSq 3565    := by decide +kernel
private theorem c3565_iso   : LeafIso 3565    := by decide +kernel
private theorem c3565_nof2  : NoF2ChkSq 3565  := by decide +kernel
private theorem c3565_nof3  : NoF3ChkSq 3565  := by decide +kernel
private theorem c3565_nof4z : NoF4zChkSq 3565 := by decide +kernel
theorem C'_3565 : C' 3565 :=
  ⟨c3565_sqf, c3565_range, c3565_ell, leafNSq_of_sq c3565_nsq, leafHAr_of_sq c3565_har,
   c3565_r, c3565_e', c3565_f1, leafS2_of_sq c3565_s2, leafS3_of_sq c3565_s3,
   c3565_iso, leafR8_of_sq c3565_nof2 c3565_nof3 c3565_nof4z⟩
theorem not_tile'_3565 (D : CongruentDissection 3565) : False :=
  not_tile_of_conditions' 3565 C'_3565 D

end Erdos634.Draft.AllN2

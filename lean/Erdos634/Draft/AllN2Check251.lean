/- AllN2Check251: N = 4558, 4559, 4565, 4566, 4567
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4558_sqf   : LeafSqf 4558   := by decide +kernel
private theorem c4558_range : LeafRange 4558  := by decide +kernel
private theorem c4558_ell   : LeafEll 4558    := by decide +kernel
private theorem c4558_nsq   : NSqChkSq 4558   := by decide +kernel
private theorem c4558_har   : HArithChkSq 4558 := by decide +kernel
private theorem c4558_r     : LeafR 4558      := by decide +kernel
private theorem c4558_e'    : LeafE' 4558     := by decide +kernel
private theorem c4558_f1    : LeafF1 4558     := Or.inl (by decide)
private theorem c4558_s2    : S2ChkSq 4558    := by decide +kernel
private theorem c4558_s3    : S3ChkSq 4558    := by decide +kernel
private theorem c4558_iso   : LeafIso 4558    := by decide +kernel
private theorem c4558_nof2  : NoF2ChkSq 4558  := by decide +kernel
private theorem c4558_nof3  : NoF3ChkSq 4558  := by decide +kernel
private theorem c4558_nof4z : NoF4zChkSq 4558 := by decide +kernel
theorem C'_4558 : C' 4558 :=
  ⟨c4558_sqf, c4558_range, c4558_ell, leafNSq_of_sq c4558_nsq, leafHAr_of_sq c4558_har,
   c4558_r, c4558_e', c4558_f1, leafS2_of_sq c4558_s2, leafS3_of_sq c4558_s3,
   c4558_iso, leafR8_of_sq c4558_nof2 c4558_nof3 c4558_nof4z⟩
theorem not_tile'_4558 (D : CongruentDissection 4558) : False :=
  not_tile_of_conditions' 4558 C'_4558 D

private theorem c4559_sqf   : LeafSqf 4559   := by decide +kernel
private theorem c4559_range : LeafRange 4559  := by decide +kernel
private theorem c4559_ell   : LeafEll 4559    := by decide +kernel
private theorem c4559_nsq   : NSqChkSq 4559   := by decide +kernel
private theorem c4559_har   : HArithChkSq 4559 := by decide +kernel
private theorem c4559_r     : LeafR 4559      := by decide +kernel
private theorem c4559_e'    : LeafE' 4559     := by decide +kernel
private theorem c4559_f1    : LeafF1 4559     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4559_s2    : S2ChkSq 4559    := by decide +kernel
private theorem c4559_s3    : S3ChkSq 4559    := by decide +kernel
private theorem c4559_iso   : LeafIso 4559    := by decide +kernel
private theorem c4559_nof2  : NoF2ChkSq 4559  := by decide +kernel
private theorem c4559_nof3  : NoF3ChkSq 4559  := by decide +kernel
private theorem c4559_nof4z : NoF4zChkSq 4559 := by decide +kernel
theorem C'_4559 : C' 4559 :=
  ⟨c4559_sqf, c4559_range, c4559_ell, leafNSq_of_sq c4559_nsq, leafHAr_of_sq c4559_har,
   c4559_r, c4559_e', c4559_f1, leafS2_of_sq c4559_s2, leafS3_of_sq c4559_s3,
   c4559_iso, leafR8_of_sq c4559_nof2 c4559_nof3 c4559_nof4z⟩
theorem not_tile'_4559 (D : CongruentDissection 4559) : False :=
  not_tile_of_conditions' 4559 C'_4559 D

private theorem c4565_sqf   : LeafSqf 4565   := by decide +kernel
private theorem c4565_range : LeafRange 4565  := by decide +kernel
private theorem c4565_ell   : LeafEll 4565    := by decide +kernel
private theorem c4565_nsq   : NSqChkSq 4565   := by decide +kernel
private theorem c4565_har   : HArithChkSq 4565 := by decide +kernel
private theorem c4565_r     : LeafR 4565      := by decide +kernel
private theorem c4565_e'    : LeafE' 4565     := by decide +kernel
private theorem c4565_f1    : LeafF1 4565     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4565_s2    : S2ChkSq 4565    := by decide +kernel
private theorem c4565_s3    : S3ChkSq 4565    := by decide +kernel
private theorem c4565_iso   : LeafIso 4565    := by decide +kernel
private theorem c4565_nof2  : NoF2ChkSq 4565  := by decide +kernel
private theorem c4565_nof3  : NoF3ChkSq 4565  := by decide +kernel
private theorem c4565_nof4z : NoF4zChkSq 4565 := by decide +kernel
theorem C'_4565 : C' 4565 :=
  ⟨c4565_sqf, c4565_range, c4565_ell, leafNSq_of_sq c4565_nsq, leafHAr_of_sq c4565_har,
   c4565_r, c4565_e', c4565_f1, leafS2_of_sq c4565_s2, leafS3_of_sq c4565_s3,
   c4565_iso, leafR8_of_sq c4565_nof2 c4565_nof3 c4565_nof4z⟩
theorem not_tile'_4565 (D : CongruentDissection 4565) : False :=
  not_tile_of_conditions' 4565 C'_4565 D

private theorem c4566_sqf   : LeafSqf 4566   := by decide +kernel
private theorem c4566_range : LeafRange 4566  := by decide +kernel
private theorem c4566_ell   : LeafEll 4566    := by decide +kernel
private theorem c4566_nsq   : NSqChkSq 4566   := by decide +kernel
private theorem c4566_har   : HArithChkSq 4566 := by decide +kernel
private theorem c4566_r     : LeafR 4566      := by decide +kernel
private theorem c4566_e'    : LeafE' 4566     := by decide +kernel
private theorem c4566_f1    : LeafF1 4566     := Or.inl (by decide)
private theorem c4566_s2    : S2ChkSq 4566    := by decide +kernel
private theorem c4566_s3    : S3ChkSq 4566    := by decide +kernel
private theorem c4566_iso   : LeafIso 4566    := by decide +kernel
private theorem c4566_nof2  : NoF2ChkSq 4566  := by decide +kernel
private theorem c4566_nof3  : NoF3ChkSq 4566  := by decide +kernel
private theorem c4566_nof4z : NoF4zChkSq 4566 := by decide +kernel
theorem C'_4566 : C' 4566 :=
  ⟨c4566_sqf, c4566_range, c4566_ell, leafNSq_of_sq c4566_nsq, leafHAr_of_sq c4566_har,
   c4566_r, c4566_e', c4566_f1, leafS2_of_sq c4566_s2, leafS3_of_sq c4566_s3,
   c4566_iso, leafR8_of_sq c4566_nof2 c4566_nof3 c4566_nof4z⟩
theorem not_tile'_4566 (D : CongruentDissection 4566) : False :=
  not_tile_of_conditions' 4566 C'_4566 D

private theorem c4567_sqf   : LeafSqf 4567   := by decide +kernel
private theorem c4567_range : LeafRange 4567  := by decide +kernel
private theorem c4567_ell   : LeafEll 4567    := by decide +kernel
private theorem c4567_nsq   : NSqChkSq 4567   := by decide +kernel
private theorem c4567_har   : HArithChkSq 4567 := by decide +kernel
private theorem c4567_r     : LeafR 4567      := by decide +kernel
private theorem c4567_e'    : LeafE' 4567     := by decide +kernel
private theorem c4567_f1    : LeafF1 4567     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4567_s2    : S2ChkSq 4567    := by decide +kernel
private theorem c4567_s3    : S3ChkSq 4567    := by decide +kernel
private theorem c4567_iso   : LeafIso 4567    := by decide +kernel
private theorem c4567_nof2  : NoF2ChkSq 4567  := by decide +kernel
private theorem c4567_nof3  : NoF3ChkSq 4567  := by decide +kernel
private theorem c4567_nof4z : NoF4zChkSq 4567 := by decide +kernel
theorem C'_4567 : C' 4567 :=
  ⟨c4567_sqf, c4567_range, c4567_ell, leafNSq_of_sq c4567_nsq, leafHAr_of_sq c4567_har,
   c4567_r, c4567_e', c4567_f1, leafS2_of_sq c4567_s2, leafS3_of_sq c4567_s3,
   c4567_iso, leafR8_of_sq c4567_nof2 c4567_nof3 c4567_nof4z⟩
theorem not_tile'_4567 (D : CongruentDissection 4567) : False :=
  not_tile_of_conditions' 4567 C'_4567 D

end Erdos634.Draft.AllN2

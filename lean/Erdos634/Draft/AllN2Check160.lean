/- AllN2Check160: N = 3379, 3382, 3383, 3387, 3390
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3379_sqf   : LeafSqf 3379   := by decide +kernel
private theorem c3379_range : LeafRange 3379  := by decide +kernel
private theorem c3379_ell   : LeafEll 3379    := by decide +kernel
private theorem c3379_nsq   : NSqChkSq 3379   := by decide +kernel
private theorem c3379_har   : HArithChkSq 3379 := by decide +kernel
private theorem c3379_r     : LeafR 3379      := by decide +kernel
private theorem c3379_e'    : LeafE' 3379     := by decide +kernel
private theorem c3379_f1    : LeafF1 3379     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3379_s2    : S2ChkSq 3379    := by decide +kernel
private theorem c3379_s3    : S3ChkSq 3379    := by decide +kernel
private theorem c3379_iso   : LeafIso 3379    := by decide +kernel
private theorem c3379_nof2  : NoF2ChkSq 3379  := by decide +kernel
private theorem c3379_nof3  : NoF3ChkSq 3379  := by decide +kernel
private theorem c3379_nof4z : NoF4zChkSq 3379 := by decide +kernel
theorem C'_3379 : C' 3379 :=
  ⟨c3379_sqf, c3379_range, c3379_ell, leafNSq_of_sq c3379_nsq, leafHAr_of_sq c3379_har,
   c3379_r, c3379_e', c3379_f1, leafS2_of_sq c3379_s2, leafS3_of_sq c3379_s3,
   c3379_iso, leafR8_of_sq c3379_nof2 c3379_nof3 c3379_nof4z⟩
theorem not_tile'_3379 (D : CongruentDissection 3379) : False :=
  not_tile_of_conditions' 3379 C'_3379 D

private theorem c3382_sqf   : LeafSqf 3382   := by decide +kernel
private theorem c3382_range : LeafRange 3382  := by decide +kernel
private theorem c3382_ell   : LeafEll 3382    := by decide +kernel
private theorem c3382_nsq   : NSqChkSq 3382   := by decide +kernel
private theorem c3382_har   : HArithChkSq 3382 := by decide +kernel
private theorem c3382_r     : LeafR 3382      := by decide +kernel
private theorem c3382_e'    : LeafE' 3382     := by decide +kernel
private theorem c3382_f1    : LeafF1 3382     := Or.inl (by decide)
private theorem c3382_s2    : S2ChkSq 3382    := by decide +kernel
private theorem c3382_s3    : S3ChkSq 3382    := by decide +kernel
private theorem c3382_iso   : LeafIso 3382    := by decide +kernel
private theorem c3382_nof2  : NoF2ChkSq 3382  := by decide +kernel
private theorem c3382_nof3  : NoF3ChkSq 3382  := by decide +kernel
private theorem c3382_nof4z : NoF4zChkSq 3382 := by decide +kernel
theorem C'_3382 : C' 3382 :=
  ⟨c3382_sqf, c3382_range, c3382_ell, leafNSq_of_sq c3382_nsq, leafHAr_of_sq c3382_har,
   c3382_r, c3382_e', c3382_f1, leafS2_of_sq c3382_s2, leafS3_of_sq c3382_s3,
   c3382_iso, leafR8_of_sq c3382_nof2 c3382_nof3 c3382_nof4z⟩
theorem not_tile'_3382 (D : CongruentDissection 3382) : False :=
  not_tile_of_conditions' 3382 C'_3382 D

private theorem c3383_sqf   : LeafSqf 3383   := by decide +kernel
private theorem c3383_range : LeafRange 3383  := by decide +kernel
private theorem c3383_ell   : LeafEll 3383    := by decide +kernel
private theorem c3383_nsq   : NSqChkSq 3383   := by decide +kernel
private theorem c3383_har   : HArithChkSq 3383 := by decide +kernel
private theorem c3383_r     : LeafR 3383      := by decide +kernel
private theorem c3383_e'    : LeafE' 3383     := by decide +kernel
private theorem c3383_f1    : LeafF1 3383     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3383_s2    : S2ChkSq 3383    := by decide +kernel
private theorem c3383_s3    : S3ChkSq 3383    := by decide +kernel
private theorem c3383_iso   : LeafIso 3383    := by decide +kernel
private theorem c3383_nof2  : NoF2ChkSq 3383  := by decide +kernel
private theorem c3383_nof3  : NoF3ChkSq 3383  := by decide +kernel
private theorem c3383_nof4z : NoF4zChkSq 3383 := by decide +kernel
theorem C'_3383 : C' 3383 :=
  ⟨c3383_sqf, c3383_range, c3383_ell, leafNSq_of_sq c3383_nsq, leafHAr_of_sq c3383_har,
   c3383_r, c3383_e', c3383_f1, leafS2_of_sq c3383_s2, leafS3_of_sq c3383_s3,
   c3383_iso, leafR8_of_sq c3383_nof2 c3383_nof3 c3383_nof4z⟩
theorem not_tile'_3383 (D : CongruentDissection 3383) : False :=
  not_tile_of_conditions' 3383 C'_3383 D

private theorem c3387_sqf   : LeafSqf 3387   := by decide +kernel
private theorem c3387_range : LeafRange 3387  := by decide +kernel
private theorem c3387_ell   : LeafEll 3387    := by decide +kernel
private theorem c3387_nsq   : NSqChkSq 3387   := by decide +kernel
private theorem c3387_har   : HArithChkSq 3387 := by decide +kernel
private theorem c3387_r     : LeafR 3387      := by decide +kernel
private theorem c3387_e'    : LeafE' 3387     := by decide +kernel
private theorem c3387_f1    : LeafF1 3387     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3387_s2    : S2ChkSq 3387    := by decide +kernel
private theorem c3387_s3    : S3ChkSq 3387    := by decide +kernel
private theorem c3387_iso   : LeafIso 3387    := by decide +kernel
private theorem c3387_nof2  : NoF2ChkSq 3387  := by decide +kernel
private theorem c3387_nof3  : NoF3ChkSq 3387  := by decide +kernel
private theorem c3387_nof4z : NoF4zChkSq 3387 := by decide +kernel
theorem C'_3387 : C' 3387 :=
  ⟨c3387_sqf, c3387_range, c3387_ell, leafNSq_of_sq c3387_nsq, leafHAr_of_sq c3387_har,
   c3387_r, c3387_e', c3387_f1, leafS2_of_sq c3387_s2, leafS3_of_sq c3387_s3,
   c3387_iso, leafR8_of_sq c3387_nof2 c3387_nof3 c3387_nof4z⟩
theorem not_tile'_3387 (D : CongruentDissection 3387) : False :=
  not_tile_of_conditions' 3387 C'_3387 D

private theorem c3390_sqf   : LeafSqf 3390   := by decide +kernel
private theorem c3390_range : LeafRange 3390  := by decide +kernel
private theorem c3390_ell   : LeafEll 3390    := by decide +kernel
private theorem c3390_nsq   : NSqChkSq 3390   := by decide +kernel
private theorem c3390_har   : HArithChkSq 3390 := by decide +kernel
private theorem c3390_r     : LeafR 3390      := by decide +kernel
private theorem c3390_e'    : LeafE' 3390     := by decide +kernel
private theorem c3390_f1    : LeafF1 3390     := Or.inl (by decide)
private theorem c3390_s2    : S2ChkSq 3390    := by decide +kernel
private theorem c3390_s3    : S3ChkSq 3390    := by decide +kernel
private theorem c3390_iso   : LeafIso 3390    := by decide +kernel
private theorem c3390_nof2  : NoF2ChkSq 3390  := by decide +kernel
private theorem c3390_nof3  : NoF3ChkSq 3390  := by decide +kernel
private theorem c3390_nof4z : NoF4zChkSq 3390 := by decide +kernel
theorem C'_3390 : C' 3390 :=
  ⟨c3390_sqf, c3390_range, c3390_ell, leafNSq_of_sq c3390_nsq, leafHAr_of_sq c3390_har,
   c3390_r, c3390_e', c3390_f1, leafS2_of_sq c3390_s2, leafS3_of_sq c3390_s3,
   c3390_iso, leafR8_of_sq c3390_nof2 c3390_nof3 c3390_nof4z⟩
theorem not_tile'_3390 (D : CongruentDissection 3390) : False :=
  not_tile_of_conditions' 3390 C'_3390 D

end Erdos634.Draft.AllN2

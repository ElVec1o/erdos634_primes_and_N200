/- AllN2Check249: N = 4530, 4531, 4533, 4534, 4535
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4530_sqf   : LeafSqf 4530   := by decide +kernel
private theorem c4530_range : LeafRange 4530  := by decide +kernel
private theorem c4530_ell   : LeafEll 4530    := by decide +kernel
private theorem c4530_nsq   : NSqChkSq 4530   := by decide +kernel
private theorem c4530_har   : HArithChkSq 4530 := by decide +kernel
private theorem c4530_r     : LeafR 4530      := by decide +kernel
private theorem c4530_e'    : LeafE' 4530     := by decide +kernel
private theorem c4530_f1    : LeafF1 4530     := Or.inl (by decide)
private theorem c4530_s2    : S2ChkSq 4530    := by decide +kernel
private theorem c4530_s3    : S3ChkSq 4530    := by decide +kernel
private theorem c4530_iso   : LeafIso 4530    := by decide +kernel
private theorem c4530_nof2  : NoF2ChkSq 4530  := by decide +kernel
private theorem c4530_nof3  : NoF3ChkSq 4530  := by decide +kernel
private theorem c4530_nof4z : NoF4zChkSq 4530 := by decide +kernel
theorem C'_4530 : C' 4530 :=
  ⟨c4530_sqf, c4530_range, c4530_ell, leafNSq_of_sq c4530_nsq, leafHAr_of_sq c4530_har,
   c4530_r, c4530_e', c4530_f1, leafS2_of_sq c4530_s2, leafS3_of_sq c4530_s3,
   c4530_iso, leafR8_of_sq c4530_nof2 c4530_nof3 c4530_nof4z⟩
theorem not_tile'_4530 (D : CongruentDissection 4530) : False :=
  not_tile_of_conditions' 4530 C'_4530 D

private theorem c4531_sqf   : LeafSqf 4531   := by decide +kernel
private theorem c4531_range : LeafRange 4531  := by decide +kernel
private theorem c4531_ell   : LeafEll 4531    := by decide +kernel
private theorem c4531_nsq   : NSqChkSq 4531   := by decide +kernel
private theorem c4531_har   : HArithChkSq 4531 := by decide +kernel
private theorem c4531_r     : LeafR 4531      := by decide +kernel
private theorem c4531_e'    : LeafE' 4531     := by decide +kernel
private theorem c4531_f1    : LeafF1 4531     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4531_s2    : S2ChkSq 4531    := by decide +kernel
private theorem c4531_s3    : S3ChkSq 4531    := by decide +kernel
private theorem c4531_iso   : LeafIso 4531    := by decide +kernel
private theorem c4531_nof2  : NoF2ChkSq 4531  := by decide +kernel
private theorem c4531_nof3  : NoF3ChkSq 4531  := by decide +kernel
private theorem c4531_nof4z : NoF4zChkSq 4531 := by decide +kernel
theorem C'_4531 : C' 4531 :=
  ⟨c4531_sqf, c4531_range, c4531_ell, leafNSq_of_sq c4531_nsq, leafHAr_of_sq c4531_har,
   c4531_r, c4531_e', c4531_f1, leafS2_of_sq c4531_s2, leafS3_of_sq c4531_s3,
   c4531_iso, leafR8_of_sq c4531_nof2 c4531_nof3 c4531_nof4z⟩
theorem not_tile'_4531 (D : CongruentDissection 4531) : False :=
  not_tile_of_conditions' 4531 C'_4531 D

private theorem c4533_sqf   : LeafSqf 4533   := by decide +kernel
private theorem c4533_range : LeafRange 4533  := by decide +kernel
private theorem c4533_ell   : LeafEll 4533    := by decide +kernel
private theorem c4533_nsq   : NSqChkSq 4533   := by decide +kernel
private theorem c4533_har   : HArithChkSq 4533 := by decide +kernel
private theorem c4533_r     : LeafR 4533      := by decide +kernel
private theorem c4533_e'    : LeafE' 4533     := by decide +kernel
private theorem c4533_f1    : LeafF1 4533     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4533_s2    : S2ChkSq 4533    := by decide +kernel
private theorem c4533_s3    : S3ChkSq 4533    := by decide +kernel
private theorem c4533_iso   : LeafIso 4533    := by decide +kernel
private theorem c4533_nof2  : NoF2ChkSq 4533  := by decide +kernel
private theorem c4533_nof3  : NoF3ChkSq 4533  := by decide +kernel
private theorem c4533_nof4z : NoF4zChkSq 4533 := by decide +kernel
theorem C'_4533 : C' 4533 :=
  ⟨c4533_sqf, c4533_range, c4533_ell, leafNSq_of_sq c4533_nsq, leafHAr_of_sq c4533_har,
   c4533_r, c4533_e', c4533_f1, leafS2_of_sq c4533_s2, leafS3_of_sq c4533_s3,
   c4533_iso, leafR8_of_sq c4533_nof2 c4533_nof3 c4533_nof4z⟩
theorem not_tile'_4533 (D : CongruentDissection 4533) : False :=
  not_tile_of_conditions' 4533 C'_4533 D

private theorem c4534_sqf   : LeafSqf 4534   := by decide +kernel
private theorem c4534_range : LeafRange 4534  := by decide +kernel
private theorem c4534_ell   : LeafEll 4534    := by decide +kernel
private theorem c4534_nsq   : NSqChkSq 4534   := by decide +kernel
private theorem c4534_har   : HArithChkSq 4534 := by decide +kernel
private theorem c4534_r     : LeafR 4534      := by decide +kernel
private theorem c4534_e'    : LeafE' 4534     := by decide +kernel
private theorem c4534_f1    : LeafF1 4534     := Or.inl (by decide)
private theorem c4534_s2    : S2ChkSq 4534    := by decide +kernel
private theorem c4534_s3    : S3ChkSq 4534    := by decide +kernel
private theorem c4534_iso   : LeafIso 4534    := by decide +kernel
private theorem c4534_nof2  : NoF2ChkSq 4534  := by decide +kernel
private theorem c4534_nof3  : NoF3ChkSq 4534  := by decide +kernel
private theorem c4534_nof4z : NoF4zChkSq 4534 := by decide +kernel
theorem C'_4534 : C' 4534 :=
  ⟨c4534_sqf, c4534_range, c4534_ell, leafNSq_of_sq c4534_nsq, leafHAr_of_sq c4534_har,
   c4534_r, c4534_e', c4534_f1, leafS2_of_sq c4534_s2, leafS3_of_sq c4534_s3,
   c4534_iso, leafR8_of_sq c4534_nof2 c4534_nof3 c4534_nof4z⟩
theorem not_tile'_4534 (D : CongruentDissection 4534) : False :=
  not_tile_of_conditions' 4534 C'_4534 D

private theorem c4535_sqf   : LeafSqf 4535   := by decide +kernel
private theorem c4535_range : LeafRange 4535  := by decide +kernel
private theorem c4535_ell   : LeafEll 4535    := by decide +kernel
private theorem c4535_nsq   : NSqChkSq 4535   := by decide +kernel
private theorem c4535_har   : HArithChkSq 4535 := by decide +kernel
private theorem c4535_r     : LeafR 4535      := by decide +kernel
private theorem c4535_e'    : LeafE' 4535     := by decide +kernel
private theorem c4535_f1    : LeafF1 4535     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4535_s2    : S2ChkSq 4535    := by decide +kernel
private theorem c4535_s3    : S3ChkSq 4535    := by decide +kernel
private theorem c4535_iso   : LeafIso 4535    := by decide +kernel
private theorem c4535_nof2  : NoF2ChkSq 4535  := by decide +kernel
private theorem c4535_nof3  : NoF3ChkSq 4535  := by decide +kernel
private theorem c4535_nof4z : NoF4zChkSq 4535 := by decide +kernel
theorem C'_4535 : C' 4535 :=
  ⟨c4535_sqf, c4535_range, c4535_ell, leafNSq_of_sq c4535_nsq, leafHAr_of_sq c4535_har,
   c4535_r, c4535_e', c4535_f1, leafS2_of_sq c4535_s2, leafS3_of_sq c4535_s3,
   c4535_iso, leafR8_of_sq c4535_nof2 c4535_nof3 c4535_nof4z⟩
theorem not_tile'_4535 (D : CongruentDissection 4535) : False :=
  not_tile_of_conditions' 4535 C'_4535 D

end Erdos634.Draft.AllN2

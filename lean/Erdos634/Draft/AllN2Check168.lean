/- AllN2Check168: N = 3489, 3491, 3493, 3494, 3498
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3489_sqf   : LeafSqf 3489   := by decide +kernel
private theorem c3489_range : LeafRange 3489  := by decide +kernel
private theorem c3489_ell   : LeafEll 3489    := by decide +kernel
private theorem c3489_nsq   : NSqChkSq 3489   := by decide +kernel
private theorem c3489_har   : HArithChkSq 3489 := by decide +kernel
private theorem c3489_r     : LeafR 3489      := by decide +kernel
private theorem c3489_e'    : LeafE' 3489     := by decide +kernel
private theorem c3489_f1    : LeafF1 3489     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3489_s2    : S2ChkSq 3489    := by decide +kernel
private theorem c3489_s3    : S3ChkSq 3489    := by decide +kernel
private theorem c3489_iso   : LeafIso 3489    := by decide +kernel
private theorem c3489_nof2  : NoF2ChkSq 3489  := by decide +kernel
private theorem c3489_nof3  : NoF3ChkSq 3489  := by decide +kernel
private theorem c3489_nof4z : NoF4zChkSq 3489 := by decide +kernel
theorem C'_3489 : C' 3489 :=
  ⟨c3489_sqf, c3489_range, c3489_ell, leafNSq_of_sq c3489_nsq, leafHAr_of_sq c3489_har,
   c3489_r, c3489_e', c3489_f1, leafS2_of_sq c3489_s2, leafS3_of_sq c3489_s3,
   c3489_iso, leafR8_of_sq c3489_nof2 c3489_nof3 c3489_nof4z⟩
theorem not_tile'_3489 (D : CongruentDissection 3489) : False :=
  not_tile_of_conditions' 3489 C'_3489 D

private theorem c3491_sqf   : LeafSqf 3491   := by decide +kernel
private theorem c3491_range : LeafRange 3491  := by decide +kernel
private theorem c3491_ell   : LeafEll 3491    := by decide +kernel
private theorem c3491_nsq   : NSqChkSq 3491   := by decide +kernel
private theorem c3491_har   : HArithChkSq 3491 := by decide +kernel
private theorem c3491_r     : LeafR 3491      := by decide +kernel
private theorem c3491_e'    : LeafE' 3491     := by decide +kernel
private theorem c3491_f1    : LeafF1 3491     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3491_s2    : S2ChkSq 3491    := by decide +kernel
private theorem c3491_s3    : S3ChkSq 3491    := by decide +kernel
private theorem c3491_iso   : LeafIso 3491    := by decide +kernel
private theorem c3491_nof2  : NoF2ChkSq 3491  := by decide +kernel
private theorem c3491_nof3  : NoF3ChkSq 3491  := by decide +kernel
private theorem c3491_nof4z : NoF4zChkSq 3491 := by decide +kernel
theorem C'_3491 : C' 3491 :=
  ⟨c3491_sqf, c3491_range, c3491_ell, leafNSq_of_sq c3491_nsq, leafHAr_of_sq c3491_har,
   c3491_r, c3491_e', c3491_f1, leafS2_of_sq c3491_s2, leafS3_of_sq c3491_s3,
   c3491_iso, leafR8_of_sq c3491_nof2 c3491_nof3 c3491_nof4z⟩
theorem not_tile'_3491 (D : CongruentDissection 3491) : False :=
  not_tile_of_conditions' 3491 C'_3491 D

private theorem c3493_sqf   : LeafSqf 3493   := by decide +kernel
private theorem c3493_range : LeafRange 3493  := by decide +kernel
private theorem c3493_ell   : LeafEll 3493    := by decide +kernel
private theorem c3493_nsq   : NSqChkSq 3493   := by decide +kernel
private theorem c3493_har   : HArithChkSq 3493 := by decide +kernel
private theorem c3493_r     : LeafR 3493      := by decide +kernel
private theorem c3493_e'    : LeafE' 3493     := by decide +kernel
private theorem c3493_f1    : LeafF1 3493     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3493_s2    : S2ChkSq 3493    := by decide +kernel
private theorem c3493_s3    : S3ChkSq 3493    := by decide +kernel
private theorem c3493_iso   : LeafIso 3493    := by decide +kernel
private theorem c3493_nof2  : NoF2ChkSq 3493  := by decide +kernel
private theorem c3493_nof3  : NoF3ChkSq 3493  := by decide +kernel
private theorem c3493_nof4z : NoF4zChkSq 3493 := by decide +kernel
theorem C'_3493 : C' 3493 :=
  ⟨c3493_sqf, c3493_range, c3493_ell, leafNSq_of_sq c3493_nsq, leafHAr_of_sq c3493_har,
   c3493_r, c3493_e', c3493_f1, leafS2_of_sq c3493_s2, leafS3_of_sq c3493_s3,
   c3493_iso, leafR8_of_sq c3493_nof2 c3493_nof3 c3493_nof4z⟩
theorem not_tile'_3493 (D : CongruentDissection 3493) : False :=
  not_tile_of_conditions' 3493 C'_3493 D

private theorem c3494_sqf   : LeafSqf 3494   := by decide +kernel
private theorem c3494_range : LeafRange 3494  := by decide +kernel
private theorem c3494_ell   : LeafEll 3494    := by decide +kernel
private theorem c3494_nsq   : NSqChkSq 3494   := by decide +kernel
private theorem c3494_har   : HArithChkSq 3494 := by decide +kernel
private theorem c3494_r     : LeafR 3494      := by decide +kernel
private theorem c3494_e'    : LeafE' 3494     := by decide +kernel
private theorem c3494_f1    : LeafF1 3494     := Or.inl (by decide)
private theorem c3494_s2    : S2ChkSq 3494    := by decide +kernel
private theorem c3494_s3    : S3ChkSq 3494    := by decide +kernel
private theorem c3494_iso   : LeafIso 3494    := by decide +kernel
private theorem c3494_nof2  : NoF2ChkSq 3494  := by decide +kernel
private theorem c3494_nof3  : NoF3ChkSq 3494  := by decide +kernel
private theorem c3494_nof4z : NoF4zChkSq 3494 := by decide +kernel
theorem C'_3494 : C' 3494 :=
  ⟨c3494_sqf, c3494_range, c3494_ell, leafNSq_of_sq c3494_nsq, leafHAr_of_sq c3494_har,
   c3494_r, c3494_e', c3494_f1, leafS2_of_sq c3494_s2, leafS3_of_sq c3494_s3,
   c3494_iso, leafR8_of_sq c3494_nof2 c3494_nof3 c3494_nof4z⟩
theorem not_tile'_3494 (D : CongruentDissection 3494) : False :=
  not_tile_of_conditions' 3494 C'_3494 D

private theorem c3498_sqf   : LeafSqf 3498   := by decide +kernel
private theorem c3498_range : LeafRange 3498  := by decide +kernel
private theorem c3498_ell   : LeafEll 3498    := by decide +kernel
private theorem c3498_nsq   : NSqChkSq 3498   := by decide +kernel
private theorem c3498_har   : HArithChkSq 3498 := by decide +kernel
private theorem c3498_r     : LeafR 3498      := by decide +kernel
private theorem c3498_e'    : LeafE' 3498     := by decide +kernel
private theorem c3498_f1    : LeafF1 3498     := Or.inl (by decide)
private theorem c3498_s2    : S2ChkSq 3498    := by decide +kernel
private theorem c3498_s3    : S3ChkSq 3498    := by decide +kernel
private theorem c3498_iso   : LeafIso 3498    := by decide +kernel
private theorem c3498_nof2  : NoF2ChkSq 3498  := by decide +kernel
private theorem c3498_nof3  : NoF3ChkSq 3498  := by decide +kernel
private theorem c3498_nof4z : NoF4zChkSq 3498 := by decide +kernel
theorem C'_3498 : C' 3498 :=
  ⟨c3498_sqf, c3498_range, c3498_ell, leafNSq_of_sq c3498_nsq, leafHAr_of_sq c3498_har,
   c3498_r, c3498_e', c3498_f1, leafS2_of_sq c3498_s2, leafS3_of_sq c3498_s3,
   c3498_iso, leafR8_of_sq c3498_nof2 c3498_nof3 c3498_nof4z⟩
theorem not_tile'_3498 (D : CongruentDissection 3498) : False :=
  not_tile_of_conditions' 3498 C'_3498 D

end Erdos634.Draft.AllN2

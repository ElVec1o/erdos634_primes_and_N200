/- AllN2Check236: N = 4366, 4367, 4370, 4377, 4378
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4366_sqf   : LeafSqf 4366   := by decide +kernel
private theorem c4366_range : LeafRange 4366  := by decide +kernel
private theorem c4366_ell   : LeafEll 4366    := by decide +kernel
private theorem c4366_nsq   : NSqChkSq 4366   := by decide +kernel
private theorem c4366_har   : HArithChkSq 4366 := by decide +kernel
private theorem c4366_r     : LeafR 4366      := by decide +kernel
private theorem c4366_e'    : LeafE' 4366     := by decide +kernel
private theorem c4366_f1    : LeafF1 4366     := Or.inl (by decide)
private theorem c4366_s2    : S2ChkSq 4366    := by decide +kernel
private theorem c4366_s3    : S3ChkSq 4366    := by decide +kernel
private theorem c4366_iso   : LeafIso 4366    := by decide +kernel
private theorem c4366_nof2  : NoF2ChkSq 4366  := by decide +kernel
private theorem c4366_nof3  : NoF3ChkSq 4366  := by decide +kernel
private theorem c4366_nof4z : NoF4zChkSq 4366 := by decide +kernel
theorem C'_4366 : C' 4366 :=
  ⟨c4366_sqf, c4366_range, c4366_ell, leafNSq_of_sq c4366_nsq, leafHAr_of_sq c4366_har,
   c4366_r, c4366_e', c4366_f1, leafS2_of_sq c4366_s2, leafS3_of_sq c4366_s3,
   c4366_iso, leafR8_of_sq c4366_nof2 c4366_nof3 c4366_nof4z⟩
theorem not_tile'_4366 (D : CongruentDissection 4366) : False :=
  not_tile_of_conditions' 4366 C'_4366 D

private theorem c4367_sqf   : LeafSqf 4367   := by decide +kernel
private theorem c4367_range : LeafRange 4367  := by decide +kernel
private theorem c4367_ell   : LeafEll 4367    := by decide +kernel
private theorem c4367_nsq   : NSqChkSq 4367   := by decide +kernel
private theorem c4367_har   : HArithChkSq 4367 := by decide +kernel
private theorem c4367_r     : LeafR 4367      := by decide +kernel
private theorem c4367_e'    : LeafE' 4367     := by decide +kernel
private theorem c4367_f1    : LeafF1 4367     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4367_s2    : S2ChkSq 4367    := by decide +kernel
private theorem c4367_s3    : S3ChkSq 4367    := by decide +kernel
private theorem c4367_iso   : LeafIso 4367    := by decide +kernel
private theorem c4367_nof2  : NoF2ChkSq 4367  := by decide +kernel
private theorem c4367_nof3  : NoF3ChkSq 4367  := by decide +kernel
private theorem c4367_nof4z : NoF4zChkSq 4367 := by decide +kernel
theorem C'_4367 : C' 4367 :=
  ⟨c4367_sqf, c4367_range, c4367_ell, leafNSq_of_sq c4367_nsq, leafHAr_of_sq c4367_har,
   c4367_r, c4367_e', c4367_f1, leafS2_of_sq c4367_s2, leafS3_of_sq c4367_s3,
   c4367_iso, leafR8_of_sq c4367_nof2 c4367_nof3 c4367_nof4z⟩
theorem not_tile'_4367 (D : CongruentDissection 4367) : False :=
  not_tile_of_conditions' 4367 C'_4367 D

private theorem c4370_sqf   : LeafSqf 4370   := by decide +kernel
private theorem c4370_range : LeafRange 4370  := by decide +kernel
private theorem c4370_ell   : LeafEll 4370    := by decide +kernel
private theorem c4370_nsq   : NSqChkSq 4370   := by decide +kernel
private theorem c4370_har   : HArithChkSq 4370 := by decide +kernel
private theorem c4370_r     : LeafR 4370      := by decide +kernel
private theorem c4370_e'    : LeafE' 4370     := by decide +kernel
private theorem c4370_f1    : LeafF1 4370     := Or.inl (by decide)
private theorem c4370_s2    : S2ChkSq 4370    := by decide +kernel
private theorem c4370_s3    : S3ChkSq 4370    := by decide +kernel
private theorem c4370_iso   : LeafIso 4370    := by decide +kernel
private theorem c4370_nof2  : NoF2ChkSq 4370  := by decide +kernel
private theorem c4370_nof3  : NoF3ChkSq 4370  := by decide +kernel
private theorem c4370_nof4z : NoF4zChkSq 4370 := by decide +kernel
theorem C'_4370 : C' 4370 :=
  ⟨c4370_sqf, c4370_range, c4370_ell, leafNSq_of_sq c4370_nsq, leafHAr_of_sq c4370_har,
   c4370_r, c4370_e', c4370_f1, leafS2_of_sq c4370_s2, leafS3_of_sq c4370_s3,
   c4370_iso, leafR8_of_sq c4370_nof2 c4370_nof3 c4370_nof4z⟩
theorem not_tile'_4370 (D : CongruentDissection 4370) : False :=
  not_tile_of_conditions' 4370 C'_4370 D

private theorem c4377_sqf   : LeafSqf 4377   := by decide +kernel
private theorem c4377_range : LeafRange 4377  := by decide +kernel
private theorem c4377_ell   : LeafEll 4377    := by decide +kernel
private theorem c4377_nsq   : NSqChkSq 4377   := by decide +kernel
private theorem c4377_har   : HArithChkSq 4377 := by decide +kernel
private theorem c4377_r     : LeafR 4377      := by decide +kernel
private theorem c4377_e'    : LeafE' 4377     := by decide +kernel
private theorem c4377_f1    : LeafF1 4377     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4377_s2    : S2ChkSq 4377    := by decide +kernel
private theorem c4377_s3    : S3ChkSq 4377    := by decide +kernel
private theorem c4377_iso   : LeafIso 4377    := by decide +kernel
private theorem c4377_nof2  : NoF2ChkSq 4377  := by decide +kernel
private theorem c4377_nof3  : NoF3ChkSq 4377  := by decide +kernel
private theorem c4377_nof4z : NoF4zChkSq 4377 := by decide +kernel
theorem C'_4377 : C' 4377 :=
  ⟨c4377_sqf, c4377_range, c4377_ell, leafNSq_of_sq c4377_nsq, leafHAr_of_sq c4377_har,
   c4377_r, c4377_e', c4377_f1, leafS2_of_sq c4377_s2, leafS3_of_sq c4377_s3,
   c4377_iso, leafR8_of_sq c4377_nof2 c4377_nof3 c4377_nof4z⟩
theorem not_tile'_4377 (D : CongruentDissection 4377) : False :=
  not_tile_of_conditions' 4377 C'_4377 D

private theorem c4378_sqf   : LeafSqf 4378   := by decide +kernel
private theorem c4378_range : LeafRange 4378  := by decide +kernel
private theorem c4378_ell   : LeafEll 4378    := by decide +kernel
private theorem c4378_nsq   : NSqChkSq 4378   := by decide +kernel
private theorem c4378_har   : HArithChkSq 4378 := by decide +kernel
private theorem c4378_r     : LeafR 4378      := by decide +kernel
private theorem c4378_e'    : LeafE' 4378     := by decide +kernel
private theorem c4378_f1    : LeafF1 4378     := Or.inl (by decide)
private theorem c4378_s2    : S2ChkSq 4378    := by decide +kernel
private theorem c4378_s3    : S3ChkSq 4378    := by decide +kernel
private theorem c4378_iso   : LeafIso 4378    := by decide +kernel
private theorem c4378_nof2  : NoF2ChkSq 4378  := by decide +kernel
private theorem c4378_nof3  : NoF3ChkSq 4378  := by decide +kernel
private theorem c4378_nof4z : NoF4zChkSq 4378 := by decide +kernel
theorem C'_4378 : C' 4378 :=
  ⟨c4378_sqf, c4378_range, c4378_ell, leafNSq_of_sq c4378_nsq, leafHAr_of_sq c4378_har,
   c4378_r, c4378_e', c4378_f1, leafS2_of_sq c4378_s2, leafS3_of_sq c4378_s3,
   c4378_iso, leafR8_of_sq c4378_nof2 c4378_nof3 c4378_nof4z⟩
theorem not_tile'_4378 (D : CongruentDissection 4378) : False :=
  not_tile_of_conditions' 4378 C'_4378 D

end Erdos634.Draft.AllN2

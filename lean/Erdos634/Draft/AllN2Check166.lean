/- AllN2Check166: N = 3458, 3459, 3462, 3463, 3467
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3458_sqf   : LeafSqf 3458   := by decide +kernel
private theorem c3458_range : LeafRange 3458  := by decide +kernel
private theorem c3458_ell   : LeafEll 3458    := by decide +kernel
private theorem c3458_nsq   : NSqChkSq 3458   := by decide +kernel
private theorem c3458_har   : HArithChkSq 3458 := by decide +kernel
private theorem c3458_r     : LeafR 3458      := by decide +kernel
private theorem c3458_e'    : LeafE' 3458     := by decide +kernel
private theorem c3458_f1    : LeafF1 3458     := Or.inl (by decide)
private theorem c3458_s2    : S2ChkSq 3458    := by decide +kernel
private theorem c3458_s3    : S3ChkSq 3458    := by decide +kernel
private theorem c3458_iso   : LeafIso 3458    := by decide +kernel
private theorem c3458_nof2  : NoF2ChkSq 3458  := by decide +kernel
private theorem c3458_nof3  : NoF3ChkSq 3458  := by decide +kernel
private theorem c3458_nof4z : NoF4zChkSq 3458 := by decide +kernel
theorem C'_3458 : C' 3458 :=
  ⟨c3458_sqf, c3458_range, c3458_ell, leafNSq_of_sq c3458_nsq, leafHAr_of_sq c3458_har,
   c3458_r, c3458_e', c3458_f1, leafS2_of_sq c3458_s2, leafS3_of_sq c3458_s3,
   c3458_iso, leafR8_of_sq c3458_nof2 c3458_nof3 c3458_nof4z⟩
theorem not_tile'_3458 (D : CongruentDissection 3458) : False :=
  not_tile_of_conditions' 3458 C'_3458 D

private theorem c3459_sqf   : LeafSqf 3459   := by decide +kernel
private theorem c3459_range : LeafRange 3459  := by decide +kernel
private theorem c3459_ell   : LeafEll 3459    := by decide +kernel
private theorem c3459_nsq   : NSqChkSq 3459   := by decide +kernel
private theorem c3459_har   : HArithChkSq 3459 := by decide +kernel
private theorem c3459_r     : LeafR 3459      := by decide +kernel
private theorem c3459_e'    : LeafE' 3459     := by decide +kernel
private theorem c3459_f1    : LeafF1 3459     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3459_s2    : S2ChkSq 3459    := by decide +kernel
private theorem c3459_s3    : S3ChkSq 3459    := by decide +kernel
private theorem c3459_iso   : LeafIso 3459    := by decide +kernel
private theorem c3459_nof2  : NoF2ChkSq 3459  := by decide +kernel
private theorem c3459_nof3  : NoF3ChkSq 3459  := by decide +kernel
private theorem c3459_nof4z : NoF4zChkSq 3459 := by decide +kernel
theorem C'_3459 : C' 3459 :=
  ⟨c3459_sqf, c3459_range, c3459_ell, leafNSq_of_sq c3459_nsq, leafHAr_of_sq c3459_har,
   c3459_r, c3459_e', c3459_f1, leafS2_of_sq c3459_s2, leafS3_of_sq c3459_s3,
   c3459_iso, leafR8_of_sq c3459_nof2 c3459_nof3 c3459_nof4z⟩
theorem not_tile'_3459 (D : CongruentDissection 3459) : False :=
  not_tile_of_conditions' 3459 C'_3459 D

private theorem c3462_sqf   : LeafSqf 3462   := by decide +kernel
private theorem c3462_range : LeafRange 3462  := by decide +kernel
private theorem c3462_ell   : LeafEll 3462    := by decide +kernel
private theorem c3462_nsq   : NSqChkSq 3462   := by decide +kernel
private theorem c3462_har   : HArithChkSq 3462 := by decide +kernel
private theorem c3462_r     : LeafR 3462      := by decide +kernel
private theorem c3462_e'    : LeafE' 3462     := by decide +kernel
private theorem c3462_f1    : LeafF1 3462     := Or.inl (by decide)
private theorem c3462_s2    : S2ChkSq 3462    := by decide +kernel
private theorem c3462_s3    : S3ChkSq 3462    := by decide +kernel
private theorem c3462_iso   : LeafIso 3462    := by decide +kernel
private theorem c3462_nof2  : NoF2ChkSq 3462  := by decide +kernel
private theorem c3462_nof3  : NoF3ChkSq 3462  := by decide +kernel
private theorem c3462_nof4z : NoF4zChkSq 3462 := by decide +kernel
theorem C'_3462 : C' 3462 :=
  ⟨c3462_sqf, c3462_range, c3462_ell, leafNSq_of_sq c3462_nsq, leafHAr_of_sq c3462_har,
   c3462_r, c3462_e', c3462_f1, leafS2_of_sq c3462_s2, leafS3_of_sq c3462_s3,
   c3462_iso, leafR8_of_sq c3462_nof2 c3462_nof3 c3462_nof4z⟩
theorem not_tile'_3462 (D : CongruentDissection 3462) : False :=
  not_tile_of_conditions' 3462 C'_3462 D

private theorem c3463_sqf   : LeafSqf 3463   := by decide +kernel
private theorem c3463_range : LeafRange 3463  := by decide +kernel
private theorem c3463_ell   : LeafEll 3463    := by decide +kernel
private theorem c3463_nsq   : NSqChkSq 3463   := by decide +kernel
private theorem c3463_har   : HArithChkSq 3463 := by decide +kernel
private theorem c3463_r     : LeafR 3463      := by decide +kernel
private theorem c3463_e'    : LeafE' 3463     := by decide +kernel
private theorem c3463_f1    : LeafF1 3463     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3463_s2    : S2ChkSq 3463    := by decide +kernel
private theorem c3463_s3    : S3ChkSq 3463    := by decide +kernel
private theorem c3463_iso   : LeafIso 3463    := by decide +kernel
private theorem c3463_nof2  : NoF2ChkSq 3463  := by decide +kernel
private theorem c3463_nof3  : NoF3ChkSq 3463  := by decide +kernel
private theorem c3463_nof4z : NoF4zChkSq 3463 := by decide +kernel
theorem C'_3463 : C' 3463 :=
  ⟨c3463_sqf, c3463_range, c3463_ell, leafNSq_of_sq c3463_nsq, leafHAr_of_sq c3463_har,
   c3463_r, c3463_e', c3463_f1, leafS2_of_sq c3463_s2, leafS3_of_sq c3463_s3,
   c3463_iso, leafR8_of_sq c3463_nof2 c3463_nof3 c3463_nof4z⟩
theorem not_tile'_3463 (D : CongruentDissection 3463) : False :=
  not_tile_of_conditions' 3463 C'_3463 D

private theorem c3467_sqf   : LeafSqf 3467   := by decide +kernel
private theorem c3467_range : LeafRange 3467  := by decide +kernel
private theorem c3467_ell   : LeafEll 3467    := by decide +kernel
private theorem c3467_nsq   : NSqChkSq 3467   := by decide +kernel
private theorem c3467_har   : HArithChkSq 3467 := by decide +kernel
private theorem c3467_r     : LeafR 3467      := by decide +kernel
private theorem c3467_e'    : LeafE' 3467     := by decide +kernel
private theorem c3467_f1    : LeafF1 3467     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3467_s2    : S2ChkSq 3467    := by decide +kernel
private theorem c3467_s3    : S3ChkSq 3467    := by decide +kernel
private theorem c3467_iso   : LeafIso 3467    := by decide +kernel
private theorem c3467_nof2  : NoF2ChkSq 3467  := by decide +kernel
private theorem c3467_nof3  : NoF3ChkSq 3467  := by decide +kernel
private theorem c3467_nof4z : NoF4zChkSq 3467 := by decide +kernel
theorem C'_3467 : C' 3467 :=
  ⟨c3467_sqf, c3467_range, c3467_ell, leafNSq_of_sq c3467_nsq, leafHAr_of_sq c3467_har,
   c3467_r, c3467_e', c3467_f1, leafS2_of_sq c3467_s2, leafS3_of_sq c3467_s3,
   c3467_iso, leafR8_of_sq c3467_nof2 c3467_nof3 c3467_nof4z⟩
theorem not_tile'_3467 (D : CongruentDissection 3467) : False :=
  not_tile_of_conditions' 3467 C'_3467 D

end Erdos634.Draft.AllN2

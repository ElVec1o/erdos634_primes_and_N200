/- AllN2Check243: N = 4454, 4458, 4461, 4462, 4463
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4454_sqf   : LeafSqf 4454   := by decide +kernel
private theorem c4454_range : LeafRange 4454  := by decide +kernel
private theorem c4454_ell   : LeafEll 4454    := by decide +kernel
private theorem c4454_nsq   : NSqChkSq 4454   := by decide +kernel
private theorem c4454_har   : HArithChkSq 4454 := by decide +kernel
private theorem c4454_r     : LeafR 4454      := by decide +kernel
private theorem c4454_e'    : LeafE' 4454     := by decide +kernel
private theorem c4454_f1    : LeafF1 4454     := Or.inl (by decide)
private theorem c4454_s2    : S2ChkSq 4454    := by decide +kernel
private theorem c4454_s3    : S3ChkSq 4454    := by decide +kernel
private theorem c4454_iso   : LeafIso 4454    := by decide +kernel
private theorem c4454_nof2  : NoF2ChkSq 4454  := by decide +kernel
private theorem c4454_nof3  : NoF3ChkSq 4454  := by decide +kernel
private theorem c4454_nof4z : NoF4zChkSq 4454 := by decide +kernel
theorem C'_4454 : C' 4454 :=
  ⟨c4454_sqf, c4454_range, c4454_ell, leafNSq_of_sq c4454_nsq, leafHAr_of_sq c4454_har,
   c4454_r, c4454_e', c4454_f1, leafS2_of_sq c4454_s2, leafS3_of_sq c4454_s3,
   c4454_iso, leafR8_of_sq c4454_nof2 c4454_nof3 c4454_nof4z⟩
theorem not_tile'_4454 (D : CongruentDissection 4454) : False :=
  not_tile_of_conditions' 4454 C'_4454 D

private theorem c4458_sqf   : LeafSqf 4458   := by decide +kernel
private theorem c4458_range : LeafRange 4458  := by decide +kernel
private theorem c4458_ell   : LeafEll 4458    := by decide +kernel
private theorem c4458_nsq   : NSqChkSq 4458   := by decide +kernel
private theorem c4458_har   : HArithChkSq 4458 := by decide +kernel
private theorem c4458_r     : LeafR 4458      := by decide +kernel
private theorem c4458_e'    : LeafE' 4458     := by decide +kernel
private theorem c4458_f1    : LeafF1 4458     := Or.inl (by decide)
private theorem c4458_s2    : S2ChkSq 4458    := by decide +kernel
private theorem c4458_s3    : S3ChkSq 4458    := by decide +kernel
private theorem c4458_iso   : LeafIso 4458    := by decide +kernel
private theorem c4458_nof2  : NoF2ChkSq 4458  := by decide +kernel
private theorem c4458_nof3  : NoF3ChkSq 4458  := by decide +kernel
private theorem c4458_nof4z : NoF4zChkSq 4458 := by decide +kernel
theorem C'_4458 : C' 4458 :=
  ⟨c4458_sqf, c4458_range, c4458_ell, leafNSq_of_sq c4458_nsq, leafHAr_of_sq c4458_har,
   c4458_r, c4458_e', c4458_f1, leafS2_of_sq c4458_s2, leafS3_of_sq c4458_s3,
   c4458_iso, leafR8_of_sq c4458_nof2 c4458_nof3 c4458_nof4z⟩
theorem not_tile'_4458 (D : CongruentDissection 4458) : False :=
  not_tile_of_conditions' 4458 C'_4458 D

private theorem c4461_sqf   : LeafSqf 4461   := by decide +kernel
private theorem c4461_range : LeafRange 4461  := by decide +kernel
private theorem c4461_ell   : LeafEll 4461    := by decide +kernel
private theorem c4461_nsq   : NSqChkSq 4461   := by decide +kernel
private theorem c4461_har   : HArithChkSq 4461 := by decide +kernel
private theorem c4461_r     : LeafR 4461      := by decide +kernel
private theorem c4461_e'    : LeafE' 4461     := by decide +kernel
private theorem c4461_f1    : LeafF1 4461     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4461_s2    : S2ChkSq 4461    := by decide +kernel
private theorem c4461_s3    : S3ChkSq 4461    := by decide +kernel
private theorem c4461_iso   : LeafIso 4461    := by decide +kernel
private theorem c4461_nof2  : NoF2ChkSq 4461  := by decide +kernel
private theorem c4461_nof3  : NoF3ChkSq 4461  := by decide +kernel
private theorem c4461_nof4z : NoF4zChkSq 4461 := by decide +kernel
theorem C'_4461 : C' 4461 :=
  ⟨c4461_sqf, c4461_range, c4461_ell, leafNSq_of_sq c4461_nsq, leafHAr_of_sq c4461_har,
   c4461_r, c4461_e', c4461_f1, leafS2_of_sq c4461_s2, leafS3_of_sq c4461_s3,
   c4461_iso, leafR8_of_sq c4461_nof2 c4461_nof3 c4461_nof4z⟩
theorem not_tile'_4461 (D : CongruentDissection 4461) : False :=
  not_tile_of_conditions' 4461 C'_4461 D

private theorem c4462_sqf   : LeafSqf 4462   := by decide +kernel
private theorem c4462_range : LeafRange 4462  := by decide +kernel
private theorem c4462_ell   : LeafEll 4462    := by decide +kernel
private theorem c4462_nsq   : NSqChkSq 4462   := by decide +kernel
private theorem c4462_har   : HArithChkSq 4462 := by decide +kernel
private theorem c4462_r     : LeafR 4462      := by decide +kernel
private theorem c4462_e'    : LeafE' 4462     := by decide +kernel
private theorem c4462_f1    : LeafF1 4462     := Or.inl (by decide)
private theorem c4462_s2    : S2ChkSq 4462    := by decide +kernel
private theorem c4462_s3    : S3ChkSq 4462    := by decide +kernel
private theorem c4462_iso   : LeafIso 4462    := by decide +kernel
private theorem c4462_nof2  : NoF2ChkSq 4462  := by decide +kernel
private theorem c4462_nof3  : NoF3ChkSq 4462  := by decide +kernel
private theorem c4462_nof4z : NoF4zChkSq 4462 := by decide +kernel
theorem C'_4462 : C' 4462 :=
  ⟨c4462_sqf, c4462_range, c4462_ell, leafNSq_of_sq c4462_nsq, leafHAr_of_sq c4462_har,
   c4462_r, c4462_e', c4462_f1, leafS2_of_sq c4462_s2, leafS3_of_sq c4462_s3,
   c4462_iso, leafR8_of_sq c4462_nof2 c4462_nof3 c4462_nof4z⟩
theorem not_tile'_4462 (D : CongruentDissection 4462) : False :=
  not_tile_of_conditions' 4462 C'_4462 D

private theorem c4463_sqf   : LeafSqf 4463   := by decide +kernel
private theorem c4463_range : LeafRange 4463  := by decide +kernel
private theorem c4463_ell   : LeafEll 4463    := by decide +kernel
private theorem c4463_nsq   : NSqChkSq 4463   := by decide +kernel
private theorem c4463_har   : HArithChkSq 4463 := by decide +kernel
private theorem c4463_r     : LeafR 4463      := by decide +kernel
private theorem c4463_e'    : LeafE' 4463     := by decide +kernel
private theorem c4463_f1    : LeafF1 4463     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4463_s2    : S2ChkSq 4463    := by decide +kernel
private theorem c4463_s3    : S3ChkSq 4463    := by decide +kernel
private theorem c4463_iso   : LeafIso 4463    := by decide +kernel
private theorem c4463_nof2  : NoF2ChkSq 4463  := by decide +kernel
private theorem c4463_nof3  : NoF3ChkSq 4463  := by decide +kernel
private theorem c4463_nof4z : NoF4zChkSq 4463 := by decide +kernel
theorem C'_4463 : C' 4463 :=
  ⟨c4463_sqf, c4463_range, c4463_ell, leafNSq_of_sq c4463_nsq, leafHAr_of_sq c4463_har,
   c4463_r, c4463_e', c4463_f1, leafS2_of_sq c4463_s2, leafS3_of_sq c4463_s3,
   c4463_iso, leafR8_of_sq c4463_nof2 c4463_nof3 c4463_nof4z⟩
theorem not_tile'_4463 (D : CongruentDissection 4463) : False :=
  not_tile_of_conditions' 4463 C'_4463 D

end Erdos634.Draft.AllN2

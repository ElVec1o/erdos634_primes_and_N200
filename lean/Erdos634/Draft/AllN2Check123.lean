/- AllN2Check123: N = 2913, 2914, 2915, 2918, 2921
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2913_sqf   : LeafSqf 2913   := by decide +kernel
private theorem c2913_range : LeafRange 2913  := by decide +kernel
private theorem c2913_ell   : LeafEll 2913    := by decide +kernel
private theorem c2913_nsq   : NSqChkSq 2913   := by decide +kernel
private theorem c2913_har   : HArithChkSq 2913 := by decide +kernel
private theorem c2913_r     : LeafR 2913      := by decide +kernel
private theorem c2913_e'    : LeafE' 2913     := by decide +kernel
private theorem c2913_f1    : LeafF1 2913     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2913_s2    : S2ChkSq 2913    := by decide +kernel
private theorem c2913_s3    : S3ChkSq 2913    := by decide +kernel
private theorem c2913_iso   : LeafIso 2913    := by decide +kernel
private theorem c2913_nof2  : NoF2ChkSq 2913  := by decide +kernel
private theorem c2913_nof3  : NoF3ChkSq 2913  := by decide +kernel
private theorem c2913_nof4z : NoF4zChkSq 2913 := by decide +kernel
theorem C'_2913 : C' 2913 :=
  ⟨c2913_sqf, c2913_range, c2913_ell, leafNSq_of_sq c2913_nsq, leafHAr_of_sq c2913_har,
   c2913_r, c2913_e', c2913_f1, leafS2_of_sq c2913_s2, leafS3_of_sq c2913_s3,
   c2913_iso, leafR8_of_sq c2913_nof2 c2913_nof3 c2913_nof4z⟩
theorem not_tile'_2913 (D : CongruentDissection 2913) : False :=
  not_tile_of_conditions' 2913 C'_2913 D

private theorem c2914_sqf   : LeafSqf 2914   := by decide +kernel
private theorem c2914_range : LeafRange 2914  := by decide +kernel
private theorem c2914_ell   : LeafEll 2914    := by decide +kernel
private theorem c2914_nsq   : NSqChkSq 2914   := by decide +kernel
private theorem c2914_har   : HArithChkSq 2914 := by decide +kernel
private theorem c2914_r     : LeafR 2914      := by decide +kernel
private theorem c2914_e'    : LeafE' 2914     := by decide +kernel
private theorem c2914_f1    : LeafF1 2914     := Or.inl (by decide)
private theorem c2914_s2    : S2ChkSq 2914    := by decide +kernel
private theorem c2914_s3    : S3ChkSq 2914    := by decide +kernel
private theorem c2914_iso   : LeafIso 2914    := by decide +kernel
private theorem c2914_nof2  : NoF2ChkSq 2914  := by decide +kernel
private theorem c2914_nof3  : NoF3ChkSq 2914  := by decide +kernel
private theorem c2914_nof4z : NoF4zChkSq 2914 := by decide +kernel
theorem C'_2914 : C' 2914 :=
  ⟨c2914_sqf, c2914_range, c2914_ell, leafNSq_of_sq c2914_nsq, leafHAr_of_sq c2914_har,
   c2914_r, c2914_e', c2914_f1, leafS2_of_sq c2914_s2, leafS3_of_sq c2914_s3,
   c2914_iso, leafR8_of_sq c2914_nof2 c2914_nof3 c2914_nof4z⟩
theorem not_tile'_2914 (D : CongruentDissection 2914) : False :=
  not_tile_of_conditions' 2914 C'_2914 D

private theorem c2915_sqf   : LeafSqf 2915   := by decide +kernel
private theorem c2915_range : LeafRange 2915  := by decide +kernel
private theorem c2915_ell   : LeafEll 2915    := by decide +kernel
private theorem c2915_nsq   : NSqChkSq 2915   := by decide +kernel
private theorem c2915_har   : HArithChkSq 2915 := by decide +kernel
private theorem c2915_r     : LeafR 2915      := by decide +kernel
private theorem c2915_e'    : LeafE' 2915     := by decide +kernel
private theorem c2915_f1    : LeafF1 2915     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2915_s2    : S2ChkSq 2915    := by decide +kernel
private theorem c2915_s3    : S3ChkSq 2915    := by decide +kernel
private theorem c2915_iso   : LeafIso 2915    := by decide +kernel
private theorem c2915_nof2  : NoF2ChkSq 2915  := by decide +kernel
private theorem c2915_nof3  : NoF3ChkSq 2915  := by decide +kernel
private theorem c2915_nof4z : NoF4zChkSq 2915 := by decide +kernel
theorem C'_2915 : C' 2915 :=
  ⟨c2915_sqf, c2915_range, c2915_ell, leafNSq_of_sq c2915_nsq, leafHAr_of_sq c2915_har,
   c2915_r, c2915_e', c2915_f1, leafS2_of_sq c2915_s2, leafS3_of_sq c2915_s3,
   c2915_iso, leafR8_of_sq c2915_nof2 c2915_nof3 c2915_nof4z⟩
theorem not_tile'_2915 (D : CongruentDissection 2915) : False :=
  not_tile_of_conditions' 2915 C'_2915 D

private theorem c2918_sqf   : LeafSqf 2918   := by decide +kernel
private theorem c2918_range : LeafRange 2918  := by decide +kernel
private theorem c2918_ell   : LeafEll 2918    := by decide +kernel
private theorem c2918_nsq   : NSqChkSq 2918   := by decide +kernel
private theorem c2918_har   : HArithChkSq 2918 := by decide +kernel
private theorem c2918_r     : LeafR 2918      := by decide +kernel
private theorem c2918_e'    : LeafE' 2918     := by decide +kernel
private theorem c2918_f1    : LeafF1 2918     := Or.inl (by decide)
private theorem c2918_s2    : S2ChkSq 2918    := by decide +kernel
private theorem c2918_s3    : S3ChkSq 2918    := by decide +kernel
private theorem c2918_iso   : LeafIso 2918    := by decide +kernel
private theorem c2918_nof2  : NoF2ChkSq 2918  := by decide +kernel
private theorem c2918_nof3  : NoF3ChkSq 2918  := by decide +kernel
private theorem c2918_nof4z : NoF4zChkSq 2918 := by decide +kernel
theorem C'_2918 : C' 2918 :=
  ⟨c2918_sqf, c2918_range, c2918_ell, leafNSq_of_sq c2918_nsq, leafHAr_of_sq c2918_har,
   c2918_r, c2918_e', c2918_f1, leafS2_of_sq c2918_s2, leafS3_of_sq c2918_s3,
   c2918_iso, leafR8_of_sq c2918_nof2 c2918_nof3 c2918_nof4z⟩
theorem not_tile'_2918 (D : CongruentDissection 2918) : False :=
  not_tile_of_conditions' 2918 C'_2918 D

private theorem c2921_sqf   : LeafSqf 2921   := by decide +kernel
private theorem c2921_range : LeafRange 2921  := by decide +kernel
private theorem c2921_ell   : LeafEll 2921    := by decide +kernel
private theorem c2921_nsq   : NSqChkSq 2921   := by decide +kernel
private theorem c2921_har   : HArithChkSq 2921 := by decide +kernel
private theorem c2921_r     : LeafR 2921      := by decide +kernel
private theorem c2921_e'    : LeafE' 2921     := by decide +kernel
private theorem c2921_f1    : LeafF1 2921     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2921_s2    : S2ChkSq 2921    := by decide +kernel
private theorem c2921_s3    : S3ChkSq 2921    := by decide +kernel
private theorem c2921_iso   : LeafIso 2921    := by decide +kernel
private theorem c2921_nof2  : NoF2ChkSq 2921  := by decide +kernel
private theorem c2921_nof3  : NoF3ChkSq 2921  := by decide +kernel
private theorem c2921_nof4z : NoF4zChkSq 2921 := by decide +kernel
theorem C'_2921 : C' 2921 :=
  ⟨c2921_sqf, c2921_range, c2921_ell, leafNSq_of_sq c2921_nsq, leafHAr_of_sq c2921_har,
   c2921_r, c2921_e', c2921_f1, leafS2_of_sq c2921_s2, leafS3_of_sq c2921_s3,
   c2921_iso, leafR8_of_sq c2921_nof2 c2921_nof3 c2921_nof4z⟩
theorem not_tile'_2921 (D : CongruentDissection 2921) : False :=
  not_tile_of_conditions' 2921 C'_2921 D

end Erdos634.Draft.AllN2

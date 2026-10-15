/- AllN2Check280: N = 4907, 4910, 4911, 4915, 4918
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4907_sqf   : LeafSqf 4907   := by decide +kernel
private theorem c4907_range : LeafRange 4907  := by decide +kernel
private theorem c4907_ell   : LeafEll 4907    := by decide +kernel
private theorem c4907_nsq   : NSqChkSq 4907   := by decide +kernel
private theorem c4907_har   : HArithChkSq 4907 := by decide +kernel
private theorem c4907_r     : LeafR 4907      := by decide +kernel
private theorem c4907_e'    : LeafE' 4907     := by decide +kernel
private theorem c4907_f1    : LeafF1 4907     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4907_s2    : S2ChkSq 4907    := by decide +kernel
private theorem c4907_s3    : S3ChkSq 4907    := by decide +kernel
private theorem c4907_iso   : LeafIso 4907    := by decide +kernel
private theorem c4907_nof2  : NoF2ChkSq 4907  := by decide +kernel
private theorem c4907_nof3  : NoF3ChkSq 4907  := by decide +kernel
private theorem c4907_nof4z : NoF4zChkSq 4907 := by decide +kernel
theorem C'_4907 : C' 4907 :=
  ⟨c4907_sqf, c4907_range, c4907_ell, leafNSq_of_sq c4907_nsq, leafHAr_of_sq c4907_har,
   c4907_r, c4907_e', c4907_f1, leafS2_of_sq c4907_s2, leafS3_of_sq c4907_s3,
   c4907_iso, leafR8_of_sq c4907_nof2 c4907_nof3 c4907_nof4z⟩
theorem not_tile'_4907 (D : CongruentDissection 4907) : False :=
  not_tile_of_conditions' 4907 C'_4907 D

private theorem c4910_sqf   : LeafSqf 4910   := by decide +kernel
private theorem c4910_range : LeafRange 4910  := by decide +kernel
private theorem c4910_ell   : LeafEll 4910    := by decide +kernel
private theorem c4910_nsq   : NSqChkSq 4910   := by decide +kernel
private theorem c4910_har   : HArithChkSq 4910 := by decide +kernel
private theorem c4910_r     : LeafR 4910      := by decide +kernel
private theorem c4910_e'    : LeafE' 4910     := by decide +kernel
private theorem c4910_f1    : LeafF1 4910     := Or.inl (by decide)
private theorem c4910_s2    : S2ChkSq 4910    := by decide +kernel
private theorem c4910_s3    : S3ChkSq 4910    := by decide +kernel
private theorem c4910_iso   : LeafIso 4910    := by decide +kernel
private theorem c4910_nof2  : NoF2ChkSq 4910  := by decide +kernel
private theorem c4910_nof3  : NoF3ChkSq 4910  := by decide +kernel
private theorem c4910_nof4z : NoF4zChkSq 4910 := by decide +kernel
theorem C'_4910 : C' 4910 :=
  ⟨c4910_sqf, c4910_range, c4910_ell, leafNSq_of_sq c4910_nsq, leafHAr_of_sq c4910_har,
   c4910_r, c4910_e', c4910_f1, leafS2_of_sq c4910_s2, leafS3_of_sq c4910_s3,
   c4910_iso, leafR8_of_sq c4910_nof2 c4910_nof3 c4910_nof4z⟩
theorem not_tile'_4910 (D : CongruentDissection 4910) : False :=
  not_tile_of_conditions' 4910 C'_4910 D

private theorem c4911_sqf   : LeafSqf 4911   := by decide +kernel
private theorem c4911_range : LeafRange 4911  := by decide +kernel
private theorem c4911_ell   : LeafEll 4911    := by decide +kernel
private theorem c4911_nsq   : NSqChkSq 4911   := by decide +kernel
private theorem c4911_har   : HArithChkSq 4911 := by decide +kernel
private theorem c4911_r     : LeafR 4911      := by decide +kernel
private theorem c4911_e'    : LeafE' 4911     := by decide +kernel
private theorem c4911_f1    : LeafF1 4911     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4911_s2    : S2ChkSq 4911    := by decide +kernel
private theorem c4911_s3    : S3ChkSq 4911    := by decide +kernel
private theorem c4911_iso   : LeafIso 4911    := by decide +kernel
private theorem c4911_nof2  : NoF2ChkSq 4911  := by decide +kernel
private theorem c4911_nof3  : NoF3ChkSq 4911  := by decide +kernel
private theorem c4911_nof4z : NoF4zChkSq 4911 := by decide +kernel
theorem C'_4911 : C' 4911 :=
  ⟨c4911_sqf, c4911_range, c4911_ell, leafNSq_of_sq c4911_nsq, leafHAr_of_sq c4911_har,
   c4911_r, c4911_e', c4911_f1, leafS2_of_sq c4911_s2, leafS3_of_sq c4911_s3,
   c4911_iso, leafR8_of_sq c4911_nof2 c4911_nof3 c4911_nof4z⟩
theorem not_tile'_4911 (D : CongruentDissection 4911) : False :=
  not_tile_of_conditions' 4911 C'_4911 D

private theorem c4915_sqf   : LeafSqf 4915   := by decide +kernel
private theorem c4915_range : LeafRange 4915  := by decide +kernel
private theorem c4915_ell   : LeafEll 4915    := by decide +kernel
private theorem c4915_nsq   : NSqChkSq 4915   := by decide +kernel
private theorem c4915_har   : HArithChkSq 4915 := by decide +kernel
private theorem c4915_r     : LeafR 4915      := by decide +kernel
private theorem c4915_e'    : LeafE' 4915     := by decide +kernel
private theorem c4915_f1    : LeafF1 4915     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4915_s2    : S2ChkSq 4915    := by decide +kernel
private theorem c4915_s3    : S3ChkSq 4915    := by decide +kernel
private theorem c4915_iso   : LeafIso 4915    := by decide +kernel
private theorem c4915_nof2  : NoF2ChkSq 4915  := by decide +kernel
private theorem c4915_nof3  : NoF3ChkSq 4915  := by decide +kernel
private theorem c4915_nof4z : NoF4zChkSq 4915 := by decide +kernel
theorem C'_4915 : C' 4915 :=
  ⟨c4915_sqf, c4915_range, c4915_ell, leafNSq_of_sq c4915_nsq, leafHAr_of_sq c4915_har,
   c4915_r, c4915_e', c4915_f1, leafS2_of_sq c4915_s2, leafS3_of_sq c4915_s3,
   c4915_iso, leafR8_of_sq c4915_nof2 c4915_nof3 c4915_nof4z⟩
theorem not_tile'_4915 (D : CongruentDissection 4915) : False :=
  not_tile_of_conditions' 4915 C'_4915 D

private theorem c4918_sqf   : LeafSqf 4918   := by decide +kernel
private theorem c4918_range : LeafRange 4918  := by decide +kernel
private theorem c4918_ell   : LeafEll 4918    := by decide +kernel
private theorem c4918_nsq   : NSqChkSq 4918   := by decide +kernel
private theorem c4918_har   : HArithChkSq 4918 := by decide +kernel
private theorem c4918_r     : LeafR 4918      := by decide +kernel
private theorem c4918_e'    : LeafE' 4918     := by decide +kernel
private theorem c4918_f1    : LeafF1 4918     := Or.inl (by decide)
private theorem c4918_s2    : S2ChkSq 4918    := by decide +kernel
private theorem c4918_s3    : S3ChkSq 4918    := by decide +kernel
private theorem c4918_iso   : LeafIso 4918    := by decide +kernel
private theorem c4918_nof2  : NoF2ChkSq 4918  := by decide +kernel
private theorem c4918_nof3  : NoF3ChkSq 4918  := by decide +kernel
private theorem c4918_nof4z : NoF4zChkSq 4918 := by decide +kernel
theorem C'_4918 : C' 4918 :=
  ⟨c4918_sqf, c4918_range, c4918_ell, leafNSq_of_sq c4918_nsq, leafHAr_of_sq c4918_har,
   c4918_r, c4918_e', c4918_f1, leafS2_of_sq c4918_s2, leafS3_of_sq c4918_s3,
   c4918_iso, leafR8_of_sq c4918_nof2 c4918_nof3 c4918_nof4z⟩
theorem not_tile'_4918 (D : CongruentDissection 4918) : False :=
  not_tile_of_conditions' 4918 C'_4918 D

end Erdos634.Draft.AllN2

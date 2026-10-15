/- AllN2Check135: N = 3059, 3062, 3063, 3066, 3067
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3059_sqf   : LeafSqf 3059   := by decide +kernel
private theorem c3059_range : LeafRange 3059  := by decide +kernel
private theorem c3059_ell   : LeafEll 3059    := by decide +kernel
private theorem c3059_nsq   : NSqChkSq 3059   := by decide +kernel
private theorem c3059_har   : HArithChkSq 3059 := by decide +kernel
private theorem c3059_r     : LeafR 3059      := by decide +kernel
private theorem c3059_e'    : LeafE' 3059     := by decide +kernel
private theorem c3059_f1    : LeafF1 3059     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3059_s2    : S2ChkSq 3059    := by decide +kernel
private theorem c3059_s3    : S3ChkSq 3059    := by decide +kernel
private theorem c3059_iso   : LeafIso 3059    := by decide +kernel
private theorem c3059_nof2  : NoF2ChkSq 3059  := by decide +kernel
private theorem c3059_nof3  : NoF3ChkSq 3059  := by decide +kernel
private theorem c3059_nof4z : NoF4zChkSq 3059 := by decide +kernel
theorem C'_3059 : C' 3059 :=
  ⟨c3059_sqf, c3059_range, c3059_ell, leafNSq_of_sq c3059_nsq, leafHAr_of_sq c3059_har,
   c3059_r, c3059_e', c3059_f1, leafS2_of_sq c3059_s2, leafS3_of_sq c3059_s3,
   c3059_iso, leafR8_of_sq c3059_nof2 c3059_nof3 c3059_nof4z⟩
theorem not_tile'_3059 (D : CongruentDissection 3059) : False :=
  not_tile_of_conditions' 3059 C'_3059 D

private theorem c3062_sqf   : LeafSqf 3062   := by decide +kernel
private theorem c3062_range : LeafRange 3062  := by decide +kernel
private theorem c3062_ell   : LeafEll 3062    := by decide +kernel
private theorem c3062_nsq   : NSqChkSq 3062   := by decide +kernel
private theorem c3062_har   : HArithChkSq 3062 := by decide +kernel
private theorem c3062_r     : LeafR 3062      := by decide +kernel
private theorem c3062_e'    : LeafE' 3062     := by decide +kernel
private theorem c3062_f1    : LeafF1 3062     := Or.inl (by decide)
private theorem c3062_s2    : S2ChkSq 3062    := by decide +kernel
private theorem c3062_s3    : S3ChkSq 3062    := by decide +kernel
private theorem c3062_iso   : LeafIso 3062    := by decide +kernel
private theorem c3062_nof2  : NoF2ChkSq 3062  := by decide +kernel
private theorem c3062_nof3  : NoF3ChkSq 3062  := by decide +kernel
private theorem c3062_nof4z : NoF4zChkSq 3062 := by decide +kernel
theorem C'_3062 : C' 3062 :=
  ⟨c3062_sqf, c3062_range, c3062_ell, leafNSq_of_sq c3062_nsq, leafHAr_of_sq c3062_har,
   c3062_r, c3062_e', c3062_f1, leafS2_of_sq c3062_s2, leafS3_of_sq c3062_s3,
   c3062_iso, leafR8_of_sq c3062_nof2 c3062_nof3 c3062_nof4z⟩
theorem not_tile'_3062 (D : CongruentDissection 3062) : False :=
  not_tile_of_conditions' 3062 C'_3062 D

private theorem c3063_sqf   : LeafSqf 3063   := by decide +kernel
private theorem c3063_range : LeafRange 3063  := by decide +kernel
private theorem c3063_ell   : LeafEll 3063    := by decide +kernel
private theorem c3063_nsq   : NSqChkSq 3063   := by decide +kernel
private theorem c3063_har   : HArithChkSq 3063 := by decide +kernel
private theorem c3063_r     : LeafR 3063      := by decide +kernel
private theorem c3063_e'    : LeafE' 3063     := by decide +kernel
private theorem c3063_f1    : LeafF1 3063     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3063_s2    : S2ChkSq 3063    := by decide +kernel
private theorem c3063_s3    : S3ChkSq 3063    := by decide +kernel
private theorem c3063_iso   : LeafIso 3063    := by decide +kernel
private theorem c3063_nof2  : NoF2ChkSq 3063  := by decide +kernel
private theorem c3063_nof3  : NoF3ChkSq 3063  := by decide +kernel
private theorem c3063_nof4z : NoF4zChkSq 3063 := by decide +kernel
theorem C'_3063 : C' 3063 :=
  ⟨c3063_sqf, c3063_range, c3063_ell, leafNSq_of_sq c3063_nsq, leafHAr_of_sq c3063_har,
   c3063_r, c3063_e', c3063_f1, leafS2_of_sq c3063_s2, leafS3_of_sq c3063_s3,
   c3063_iso, leafR8_of_sq c3063_nof2 c3063_nof3 c3063_nof4z⟩
theorem not_tile'_3063 (D : CongruentDissection 3063) : False :=
  not_tile_of_conditions' 3063 C'_3063 D

private theorem c3066_sqf   : LeafSqf 3066   := by decide +kernel
private theorem c3066_range : LeafRange 3066  := by decide +kernel
private theorem c3066_ell   : LeafEll 3066    := by decide +kernel
private theorem c3066_nsq   : NSqChkSq 3066   := by decide +kernel
private theorem c3066_har   : HArithChkSq 3066 := by decide +kernel
private theorem c3066_r     : LeafR 3066      := by decide +kernel
private theorem c3066_e'    : LeafE' 3066     := by decide +kernel
private theorem c3066_f1    : LeafF1 3066     := Or.inl (by decide)
private theorem c3066_s2    : S2ChkSq 3066    := by decide +kernel
private theorem c3066_s3    : S3ChkSq 3066    := by decide +kernel
private theorem c3066_iso   : LeafIso 3066    := by decide +kernel
private theorem c3066_nof2  : NoF2ChkSq 3066  := by decide +kernel
private theorem c3066_nof3  : NoF3ChkSq 3066  := by decide +kernel
private theorem c3066_nof4z : NoF4zChkSq 3066 := by decide +kernel
theorem C'_3066 : C' 3066 :=
  ⟨c3066_sqf, c3066_range, c3066_ell, leafNSq_of_sq c3066_nsq, leafHAr_of_sq c3066_har,
   c3066_r, c3066_e', c3066_f1, leafS2_of_sq c3066_s2, leafS3_of_sq c3066_s3,
   c3066_iso, leafR8_of_sq c3066_nof2 c3066_nof3 c3066_nof4z⟩
theorem not_tile'_3066 (D : CongruentDissection 3066) : False :=
  not_tile_of_conditions' 3066 C'_3066 D

private theorem c3067_sqf   : LeafSqf 3067   := by decide +kernel
private theorem c3067_range : LeafRange 3067  := by decide +kernel
private theorem c3067_ell   : LeafEll 3067    := by decide +kernel
private theorem c3067_nsq   : NSqChkSq 3067   := by decide +kernel
private theorem c3067_har   : HArithChkSq 3067 := by decide +kernel
private theorem c3067_r     : LeafR 3067      := by decide +kernel
private theorem c3067_e'    : LeafE' 3067     := by decide +kernel
private theorem c3067_f1    : LeafF1 3067     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3067_s2    : S2ChkSq 3067    := by decide +kernel
private theorem c3067_s3    : S3ChkSq 3067    := by decide +kernel
private theorem c3067_iso   : LeafIso 3067    := by decide +kernel
private theorem c3067_nof2  : NoF2ChkSq 3067  := by decide +kernel
private theorem c3067_nof3  : NoF3ChkSq 3067  := by decide +kernel
private theorem c3067_nof4z : NoF4zChkSq 3067 := by decide +kernel
theorem C'_3067 : C' 3067 :=
  ⟨c3067_sqf, c3067_range, c3067_ell, leafNSq_of_sq c3067_nsq, leafHAr_of_sq c3067_har,
   c3067_r, c3067_e', c3067_f1, leafS2_of_sq c3067_s2, leafS3_of_sq c3067_s3,
   c3067_iso, leafR8_of_sq c3067_nof2 c3067_nof3 c3067_nof4z⟩
theorem not_tile'_3067 (D : CongruentDissection 3067) : False :=
  not_tile_of_conditions' 3067 C'_3067 D

end Erdos634.Draft.AllN2

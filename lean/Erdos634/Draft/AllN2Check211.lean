/- AllN2Check211: N = 4055, 4061, 4062, 4063, 4066
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4055_sqf   : LeafSqf 4055   := by decide +kernel
private theorem c4055_range : LeafRange 4055  := by decide +kernel
private theorem c4055_ell   : LeafEll 4055    := by decide +kernel
private theorem c4055_nsq   : NSqChkSq 4055   := by decide +kernel
private theorem c4055_har   : HArithChkSq 4055 := by decide +kernel
private theorem c4055_r     : LeafR 4055      := by decide +kernel
private theorem c4055_e'    : LeafE' 4055     := by decide +kernel
private theorem c4055_f1    : LeafF1 4055     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4055_s2    : S2ChkSq 4055    := by decide +kernel
private theorem c4055_s3    : S3ChkSq 4055    := by decide +kernel
private theorem c4055_iso   : LeafIso 4055    := by decide +kernel
private theorem c4055_nof2  : NoF2ChkSq 4055  := by decide +kernel
private theorem c4055_nof3  : NoF3ChkSq 4055  := by decide +kernel
private theorem c4055_nof4z : NoF4zChkSq 4055 := by decide +kernel
theorem C'_4055 : C' 4055 :=
  ⟨c4055_sqf, c4055_range, c4055_ell, leafNSq_of_sq c4055_nsq, leafHAr_of_sq c4055_har,
   c4055_r, c4055_e', c4055_f1, leafS2_of_sq c4055_s2, leafS3_of_sq c4055_s3,
   c4055_iso, leafR8_of_sq c4055_nof2 c4055_nof3 c4055_nof4z⟩
theorem not_tile'_4055 (D : CongruentDissection 4055) : False :=
  not_tile_of_conditions' 4055 C'_4055 D

private theorem c4061_sqf   : LeafSqf 4061   := by decide +kernel
private theorem c4061_range : LeafRange 4061  := by decide +kernel
private theorem c4061_ell   : LeafEll 4061    := by decide +kernel
private theorem c4061_nsq   : NSqChkSq 4061   := by decide +kernel
private theorem c4061_har   : HArithChkSq 4061 := by decide +kernel
private theorem c4061_r     : LeafR 4061      := by decide +kernel
private theorem c4061_e'    : LeafE' 4061     := by decide +kernel
private theorem c4061_f1    : LeafF1 4061     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4061_s2    : S2ChkSq 4061    := by decide +kernel
private theorem c4061_s3    : S3ChkSq 4061    := by decide +kernel
private theorem c4061_iso   : LeafIso 4061    := by decide +kernel
private theorem c4061_nof2  : NoF2ChkSq 4061  := by decide +kernel
private theorem c4061_nof3  : NoF3ChkSq 4061  := by decide +kernel
private theorem c4061_nof4z : NoF4zChkSq 4061 := by decide +kernel
theorem C'_4061 : C' 4061 :=
  ⟨c4061_sqf, c4061_range, c4061_ell, leafNSq_of_sq c4061_nsq, leafHAr_of_sq c4061_har,
   c4061_r, c4061_e', c4061_f1, leafS2_of_sq c4061_s2, leafS3_of_sq c4061_s3,
   c4061_iso, leafR8_of_sq c4061_nof2 c4061_nof3 c4061_nof4z⟩
theorem not_tile'_4061 (D : CongruentDissection 4061) : False :=
  not_tile_of_conditions' 4061 C'_4061 D

private theorem c4062_sqf   : LeafSqf 4062   := by decide +kernel
private theorem c4062_range : LeafRange 4062  := by decide +kernel
private theorem c4062_ell   : LeafEll 4062    := by decide +kernel
private theorem c4062_nsq   : NSqChkSq 4062   := by decide +kernel
private theorem c4062_har   : HArithChkSq 4062 := by decide +kernel
private theorem c4062_r     : LeafR 4062      := by decide +kernel
private theorem c4062_e'    : LeafE' 4062     := by decide +kernel
private theorem c4062_f1    : LeafF1 4062     := Or.inl (by decide)
private theorem c4062_s2    : S2ChkSq 4062    := by decide +kernel
private theorem c4062_s3    : S3ChkSq 4062    := by decide +kernel
private theorem c4062_iso   : LeafIso 4062    := by decide +kernel
private theorem c4062_nof2  : NoF2ChkSq 4062  := by decide +kernel
private theorem c4062_nof3  : NoF3ChkSq 4062  := by decide +kernel
private theorem c4062_nof4z : NoF4zChkSq 4062 := by decide +kernel
theorem C'_4062 : C' 4062 :=
  ⟨c4062_sqf, c4062_range, c4062_ell, leafNSq_of_sq c4062_nsq, leafHAr_of_sq c4062_har,
   c4062_r, c4062_e', c4062_f1, leafS2_of_sq c4062_s2, leafS3_of_sq c4062_s3,
   c4062_iso, leafR8_of_sq c4062_nof2 c4062_nof3 c4062_nof4z⟩
theorem not_tile'_4062 (D : CongruentDissection 4062) : False :=
  not_tile_of_conditions' 4062 C'_4062 D

private theorem c4063_sqf   : LeafSqf 4063   := by decide +kernel
private theorem c4063_range : LeafRange 4063  := by decide +kernel
private theorem c4063_ell   : LeafEll 4063    := by decide +kernel
private theorem c4063_nsq   : NSqChkSq 4063   := by decide +kernel
private theorem c4063_har   : HArithChkSq 4063 := by decide +kernel
private theorem c4063_r     : LeafR 4063      := by decide +kernel
private theorem c4063_e'    : LeafE' 4063     := by decide +kernel
private theorem c4063_f1    : LeafF1 4063     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4063_s2    : S2ChkSq 4063    := by decide +kernel
private theorem c4063_s3    : S3ChkSq 4063    := by decide +kernel
private theorem c4063_iso   : LeafIso 4063    := by decide +kernel
private theorem c4063_nof2  : NoF2ChkSq 4063  := by decide +kernel
private theorem c4063_nof3  : NoF3ChkSq 4063  := by decide +kernel
private theorem c4063_nof4z : NoF4zChkSq 4063 := by decide +kernel
theorem C'_4063 : C' 4063 :=
  ⟨c4063_sqf, c4063_range, c4063_ell, leafNSq_of_sq c4063_nsq, leafHAr_of_sq c4063_har,
   c4063_r, c4063_e', c4063_f1, leafS2_of_sq c4063_s2, leafS3_of_sq c4063_s3,
   c4063_iso, leafR8_of_sq c4063_nof2 c4063_nof3 c4063_nof4z⟩
theorem not_tile'_4063 (D : CongruentDissection 4063) : False :=
  not_tile_of_conditions' 4063 C'_4063 D

private theorem c4066_sqf   : LeafSqf 4066   := by decide +kernel
private theorem c4066_range : LeafRange 4066  := by decide +kernel
private theorem c4066_ell   : LeafEll 4066    := by decide +kernel
private theorem c4066_nsq   : NSqChkSq 4066   := by decide +kernel
private theorem c4066_har   : HArithChkSq 4066 := by decide +kernel
private theorem c4066_r     : LeafR 4066      := by decide +kernel
private theorem c4066_e'    : LeafE' 4066     := by decide +kernel
private theorem c4066_f1    : LeafF1 4066     := Or.inl (by decide)
private theorem c4066_s2    : S2ChkSq 4066    := by decide +kernel
private theorem c4066_s3    : S3ChkSq 4066    := by decide +kernel
private theorem c4066_iso   : LeafIso 4066    := by decide +kernel
private theorem c4066_nof2  : NoF2ChkSq 4066  := by decide +kernel
private theorem c4066_nof3  : NoF3ChkSq 4066  := by decide +kernel
private theorem c4066_nof4z : NoF4zChkSq 4066 := by decide +kernel
theorem C'_4066 : C' 4066 :=
  ⟨c4066_sqf, c4066_range, c4066_ell, leafNSq_of_sq c4066_nsq, leafHAr_of_sq c4066_har,
   c4066_r, c4066_e', c4066_f1, leafS2_of_sq c4066_s2, leafS3_of_sq c4066_s3,
   c4066_iso, leafR8_of_sq c4066_nof2 c4066_nof3 c4066_nof4z⟩
theorem not_tile'_4066 (D : CongruentDissection 4066) : False :=
  not_tile_of_conditions' 4066 C'_4066 D

end Erdos634.Draft.AllN2

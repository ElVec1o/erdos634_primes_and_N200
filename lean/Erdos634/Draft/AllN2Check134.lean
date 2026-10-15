/- AllN2Check134: N = 3053, 3054, 3055, 3057, 3058
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3053_sqf   : LeafSqf 3053   := by decide +kernel
private theorem c3053_range : LeafRange 3053  := by decide +kernel
private theorem c3053_ell   : LeafEll 3053    := by decide +kernel
private theorem c3053_nsq   : NSqChkSq 3053   := by decide +kernel
private theorem c3053_har   : HArithChkSq 3053 := by decide +kernel
private theorem c3053_r     : LeafR 3053      := by decide +kernel
private theorem c3053_e'    : LeafE' 3053     := by decide +kernel
private theorem c3053_f1    : LeafF1 3053     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3053_s2    : S2ChkSq 3053    := by decide +kernel
private theorem c3053_s3    : S3ChkSq 3053    := by decide +kernel
private theorem c3053_iso   : LeafIso 3053    := by decide +kernel
private theorem c3053_nof2  : NoF2ChkSq 3053  := by decide +kernel
private theorem c3053_nof3  : NoF3ChkSq 3053  := by decide +kernel
private theorem c3053_nof4z : NoF4zChkSq 3053 := by decide +kernel
theorem C'_3053 : C' 3053 :=
  ⟨c3053_sqf, c3053_range, c3053_ell, leafNSq_of_sq c3053_nsq, leafHAr_of_sq c3053_har,
   c3053_r, c3053_e', c3053_f1, leafS2_of_sq c3053_s2, leafS3_of_sq c3053_s3,
   c3053_iso, leafR8_of_sq c3053_nof2 c3053_nof3 c3053_nof4z⟩
theorem not_tile'_3053 (D : CongruentDissection 3053) : False :=
  not_tile_of_conditions' 3053 C'_3053 D

private theorem c3054_sqf   : LeafSqf 3054   := by decide +kernel
private theorem c3054_range : LeafRange 3054  := by decide +kernel
private theorem c3054_ell   : LeafEll 3054    := by decide +kernel
private theorem c3054_nsq   : NSqChkSq 3054   := by decide +kernel
private theorem c3054_har   : HArithChkSq 3054 := by decide +kernel
private theorem c3054_r     : LeafR 3054      := by decide +kernel
private theorem c3054_e'    : LeafE' 3054     := by decide +kernel
private theorem c3054_f1    : LeafF1 3054     := Or.inl (by decide)
private theorem c3054_s2    : S2ChkSq 3054    := by decide +kernel
private theorem c3054_s3    : S3ChkSq 3054    := by decide +kernel
private theorem c3054_iso   : LeafIso 3054    := by decide +kernel
private theorem c3054_nof2  : NoF2ChkSq 3054  := by decide +kernel
private theorem c3054_nof3  : NoF3ChkSq 3054  := by decide +kernel
private theorem c3054_nof4z : NoF4zChkSq 3054 := by decide +kernel
theorem C'_3054 : C' 3054 :=
  ⟨c3054_sqf, c3054_range, c3054_ell, leafNSq_of_sq c3054_nsq, leafHAr_of_sq c3054_har,
   c3054_r, c3054_e', c3054_f1, leafS2_of_sq c3054_s2, leafS3_of_sq c3054_s3,
   c3054_iso, leafR8_of_sq c3054_nof2 c3054_nof3 c3054_nof4z⟩
theorem not_tile'_3054 (D : CongruentDissection 3054) : False :=
  not_tile_of_conditions' 3054 C'_3054 D

private theorem c3055_sqf   : LeafSqf 3055   := by decide +kernel
private theorem c3055_range : LeafRange 3055  := by decide +kernel
private theorem c3055_ell   : LeafEll 3055    := by decide +kernel
private theorem c3055_nsq   : NSqChkSq 3055   := by decide +kernel
private theorem c3055_har   : HArithChkSq 3055 := by decide +kernel
private theorem c3055_r     : LeafR 3055      := by decide +kernel
private theorem c3055_e'    : LeafE' 3055     := by decide +kernel
private theorem c3055_f1    : LeafF1 3055     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3055_s2    : S2ChkSq 3055    := by decide +kernel
private theorem c3055_s3    : S3ChkSq 3055    := by decide +kernel
private theorem c3055_iso   : LeafIso 3055    := by decide +kernel
private theorem c3055_nof2  : NoF2ChkSq 3055  := by decide +kernel
private theorem c3055_nof3  : NoF3ChkSq 3055  := by decide +kernel
private theorem c3055_nof4z : NoF4zChkSq 3055 := by decide +kernel
theorem C'_3055 : C' 3055 :=
  ⟨c3055_sqf, c3055_range, c3055_ell, leafNSq_of_sq c3055_nsq, leafHAr_of_sq c3055_har,
   c3055_r, c3055_e', c3055_f1, leafS2_of_sq c3055_s2, leafS3_of_sq c3055_s3,
   c3055_iso, leafR8_of_sq c3055_nof2 c3055_nof3 c3055_nof4z⟩
theorem not_tile'_3055 (D : CongruentDissection 3055) : False :=
  not_tile_of_conditions' 3055 C'_3055 D

private theorem c3057_sqf   : LeafSqf 3057   := by decide +kernel
private theorem c3057_range : LeafRange 3057  := by decide +kernel
private theorem c3057_ell   : LeafEll 3057    := by decide +kernel
private theorem c3057_nsq   : NSqChkSq 3057   := by decide +kernel
private theorem c3057_har   : HArithChkSq 3057 := by decide +kernel
private theorem c3057_r     : LeafR 3057      := by decide +kernel
private theorem c3057_e'    : LeafE' 3057     := by decide +kernel
private theorem c3057_f1    : LeafF1 3057     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3057_s2    : S2ChkSq 3057    := by decide +kernel
private theorem c3057_s3    : S3ChkSq 3057    := by decide +kernel
private theorem c3057_iso   : LeafIso 3057    := by decide +kernel
private theorem c3057_nof2  : NoF2ChkSq 3057  := by decide +kernel
private theorem c3057_nof3  : NoF3ChkSq 3057  := by decide +kernel
private theorem c3057_nof4z : NoF4zChkSq 3057 := by decide +kernel
theorem C'_3057 : C' 3057 :=
  ⟨c3057_sqf, c3057_range, c3057_ell, leafNSq_of_sq c3057_nsq, leafHAr_of_sq c3057_har,
   c3057_r, c3057_e', c3057_f1, leafS2_of_sq c3057_s2, leafS3_of_sq c3057_s3,
   c3057_iso, leafR8_of_sq c3057_nof2 c3057_nof3 c3057_nof4z⟩
theorem not_tile'_3057 (D : CongruentDissection 3057) : False :=
  not_tile_of_conditions' 3057 C'_3057 D

private theorem c3058_sqf   : LeafSqf 3058   := by decide +kernel
private theorem c3058_range : LeafRange 3058  := by decide +kernel
private theorem c3058_ell   : LeafEll 3058    := by decide +kernel
private theorem c3058_nsq   : NSqChkSq 3058   := by decide +kernel
private theorem c3058_har   : HArithChkSq 3058 := by decide +kernel
private theorem c3058_r     : LeafR 3058      := by decide +kernel
private theorem c3058_e'    : LeafE' 3058     := by decide +kernel
private theorem c3058_f1    : LeafF1 3058     := Or.inl (by decide)
private theorem c3058_s2    : S2ChkSq 3058    := by decide +kernel
private theorem c3058_s3    : S3ChkSq 3058    := by decide +kernel
private theorem c3058_iso   : LeafIso 3058    := by decide +kernel
private theorem c3058_nof2  : NoF2ChkSq 3058  := by decide +kernel
private theorem c3058_nof3  : NoF3ChkSq 3058  := by decide +kernel
private theorem c3058_nof4z : NoF4zChkSq 3058 := by decide +kernel
theorem C'_3058 : C' 3058 :=
  ⟨c3058_sqf, c3058_range, c3058_ell, leafNSq_of_sq c3058_nsq, leafHAr_of_sq c3058_har,
   c3058_r, c3058_e', c3058_f1, leafS2_of_sq c3058_s2, leafS3_of_sq c3058_s3,
   c3058_iso, leafR8_of_sq c3058_nof2 c3058_nof3 c3058_nof4z⟩
theorem not_tile'_3058 (D : CongruentDissection 3058) : False :=
  not_tile_of_conditions' 3058 C'_3058 D

end Erdos634.Draft.AllN2

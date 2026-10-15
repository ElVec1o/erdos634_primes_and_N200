/- AllN2Check142: N = 3142, 3143, 3147, 3149, 3151
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3142_sqf   : LeafSqf 3142   := by decide +kernel
private theorem c3142_range : LeafRange 3142  := by decide +kernel
private theorem c3142_ell   : LeafEll 3142    := by decide +kernel
private theorem c3142_nsq   : NSqChkSq 3142   := by decide +kernel
private theorem c3142_har   : HArithChkSq 3142 := by decide +kernel
private theorem c3142_r     : LeafR 3142      := by decide +kernel
private theorem c3142_e'    : LeafE' 3142     := by decide +kernel
private theorem c3142_f1    : LeafF1 3142     := Or.inl (by decide)
private theorem c3142_s2    : S2ChkSq 3142    := by decide +kernel
private theorem c3142_s3    : S3ChkSq 3142    := by decide +kernel
private theorem c3142_iso   : LeafIso 3142    := by decide +kernel
private theorem c3142_nof2  : NoF2ChkSq 3142  := by decide +kernel
private theorem c3142_nof3  : NoF3ChkSq 3142  := by decide +kernel
private theorem c3142_nof4z : NoF4zChkSq 3142 := by decide +kernel
theorem C'_3142 : C' 3142 :=
  ⟨c3142_sqf, c3142_range, c3142_ell, leafNSq_of_sq c3142_nsq, leafHAr_of_sq c3142_har,
   c3142_r, c3142_e', c3142_f1, leafS2_of_sq c3142_s2, leafS3_of_sq c3142_s3,
   c3142_iso, leafR8_of_sq c3142_nof2 c3142_nof3 c3142_nof4z⟩
theorem not_tile'_3142 (D : CongruentDissection 3142) : False :=
  not_tile_of_conditions' 3142 C'_3142 D

private theorem c3143_sqf   : LeafSqf 3143   := by decide +kernel
private theorem c3143_range : LeafRange 3143  := by decide +kernel
private theorem c3143_ell   : LeafEll 3143    := by decide +kernel
private theorem c3143_nsq   : NSqChkSq 3143   := by decide +kernel
private theorem c3143_har   : HArithChkSq 3143 := by decide +kernel
private theorem c3143_r     : LeafR 3143      := by decide +kernel
private theorem c3143_e'    : LeafE' 3143     := by decide +kernel
private theorem c3143_f1    : LeafF1 3143     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3143_s2    : S2ChkSq 3143    := by decide +kernel
private theorem c3143_s3    : S3ChkSq 3143    := by decide +kernel
private theorem c3143_iso   : LeafIso 3143    := by decide +kernel
private theorem c3143_nof2  : NoF2ChkSq 3143  := by decide +kernel
private theorem c3143_nof3  : NoF3ChkSq 3143  := by decide +kernel
private theorem c3143_nof4z : NoF4zChkSq 3143 := by decide +kernel
theorem C'_3143 : C' 3143 :=
  ⟨c3143_sqf, c3143_range, c3143_ell, leafNSq_of_sq c3143_nsq, leafHAr_of_sq c3143_har,
   c3143_r, c3143_e', c3143_f1, leafS2_of_sq c3143_s2, leafS3_of_sq c3143_s3,
   c3143_iso, leafR8_of_sq c3143_nof2 c3143_nof3 c3143_nof4z⟩
theorem not_tile'_3143 (D : CongruentDissection 3143) : False :=
  not_tile_of_conditions' 3143 C'_3143 D

private theorem c3147_sqf   : LeafSqf 3147   := by decide +kernel
private theorem c3147_range : LeafRange 3147  := by decide +kernel
private theorem c3147_ell   : LeafEll 3147    := by decide +kernel
private theorem c3147_nsq   : NSqChkSq 3147   := by decide +kernel
private theorem c3147_har   : HArithChkSq 3147 := by decide +kernel
private theorem c3147_r     : LeafR 3147      := by decide +kernel
private theorem c3147_e'    : LeafE' 3147     := by decide +kernel
private theorem c3147_f1    : LeafF1 3147     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3147_s2    : S2ChkSq 3147    := by decide +kernel
private theorem c3147_s3    : S3ChkSq 3147    := by decide +kernel
private theorem c3147_iso   : LeafIso 3147    := by decide +kernel
private theorem c3147_nof2  : NoF2ChkSq 3147  := by decide +kernel
private theorem c3147_nof3  : NoF3ChkSq 3147  := by decide +kernel
private theorem c3147_nof4z : NoF4zChkSq 3147 := by decide +kernel
theorem C'_3147 : C' 3147 :=
  ⟨c3147_sqf, c3147_range, c3147_ell, leafNSq_of_sq c3147_nsq, leafHAr_of_sq c3147_har,
   c3147_r, c3147_e', c3147_f1, leafS2_of_sq c3147_s2, leafS3_of_sq c3147_s3,
   c3147_iso, leafR8_of_sq c3147_nof2 c3147_nof3 c3147_nof4z⟩
theorem not_tile'_3147 (D : CongruentDissection 3147) : False :=
  not_tile_of_conditions' 3147 C'_3147 D

private theorem c3149_sqf   : LeafSqf 3149   := by decide +kernel
private theorem c3149_range : LeafRange 3149  := by decide +kernel
private theorem c3149_ell   : LeafEll 3149    := by decide +kernel
private theorem c3149_nsq   : NSqChkSq 3149   := by decide +kernel
private theorem c3149_har   : HArithChkSq 3149 := by decide +kernel
private theorem c3149_r     : LeafR 3149      := by decide +kernel
private theorem c3149_e'    : LeafE' 3149     := by decide +kernel
private theorem c3149_f1    : LeafF1 3149     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3149_s2    : S2ChkSq 3149    := by decide +kernel
private theorem c3149_s3    : S3ChkSq 3149    := by decide +kernel
private theorem c3149_iso   : LeafIso 3149    := by decide +kernel
private theorem c3149_nof2  : NoF2ChkSq 3149  := by decide +kernel
private theorem c3149_nof3  : NoF3ChkSq 3149  := by decide +kernel
private theorem c3149_nof4z : NoF4zChkSq 3149 := by decide +kernel
theorem C'_3149 : C' 3149 :=
  ⟨c3149_sqf, c3149_range, c3149_ell, leafNSq_of_sq c3149_nsq, leafHAr_of_sq c3149_har,
   c3149_r, c3149_e', c3149_f1, leafS2_of_sq c3149_s2, leafS3_of_sq c3149_s3,
   c3149_iso, leafR8_of_sq c3149_nof2 c3149_nof3 c3149_nof4z⟩
theorem not_tile'_3149 (D : CongruentDissection 3149) : False :=
  not_tile_of_conditions' 3149 C'_3149 D

private theorem c3151_sqf   : LeafSqf 3151   := by decide +kernel
private theorem c3151_range : LeafRange 3151  := by decide +kernel
private theorem c3151_ell   : LeafEll 3151    := by decide +kernel
private theorem c3151_nsq   : NSqChkSq 3151   := by decide +kernel
private theorem c3151_har   : HArithChkSq 3151 := by decide +kernel
private theorem c3151_r     : LeafR 3151      := by decide +kernel
private theorem c3151_e'    : LeafE' 3151     := by decide +kernel
private theorem c3151_f1    : LeafF1 3151     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3151_s2    : S2ChkSq 3151    := by decide +kernel
private theorem c3151_s3    : S3ChkSq 3151    := by decide +kernel
private theorem c3151_iso   : LeafIso 3151    := by decide +kernel
private theorem c3151_nof2  : NoF2ChkSq 3151  := by decide +kernel
private theorem c3151_nof3  : NoF3ChkSq 3151  := by decide +kernel
private theorem c3151_nof4z : NoF4zChkSq 3151 := by decide +kernel
theorem C'_3151 : C' 3151 :=
  ⟨c3151_sqf, c3151_range, c3151_ell, leafNSq_of_sq c3151_nsq, leafHAr_of_sq c3151_har,
   c3151_r, c3151_e', c3151_f1, leafS2_of_sq c3151_s2, leafS3_of_sq c3151_s3,
   c3151_iso, leafR8_of_sq c3151_nof2 c3151_nof3 c3151_nof4z⟩
theorem not_tile'_3151 (D : CongruentDissection 3151) : False :=
  not_tile_of_conditions' 3151 C'_3151 D

end Erdos634.Draft.AllN2

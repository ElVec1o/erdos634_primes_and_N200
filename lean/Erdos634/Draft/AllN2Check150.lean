/- AllN2Check150: N = 3251, 3254, 3259, 3261, 3262
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3251_sqf   : LeafSqf 3251   := by decide +kernel
private theorem c3251_range : LeafRange 3251  := by decide +kernel
private theorem c3251_ell   : LeafEll 3251    := by decide +kernel
private theorem c3251_nsq   : NSqChkSq 3251   := by decide +kernel
private theorem c3251_har   : HArithChkSq 3251 := by decide +kernel
private theorem c3251_r     : LeafR 3251      := by decide +kernel
private theorem c3251_e'    : LeafE' 3251     := by decide +kernel
private theorem c3251_f1    : LeafF1 3251     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3251_s2    : S2ChkSq 3251    := by decide +kernel
private theorem c3251_s3    : S3ChkSq 3251    := by decide +kernel
private theorem c3251_iso   : LeafIso 3251    := by decide +kernel
private theorem c3251_nof2  : NoF2ChkSq 3251  := by decide +kernel
private theorem c3251_nof3  : NoF3ChkSq 3251  := by decide +kernel
private theorem c3251_nof4z : NoF4zChkSq 3251 := by decide +kernel
theorem C'_3251 : C' 3251 :=
  ⟨c3251_sqf, c3251_range, c3251_ell, leafNSq_of_sq c3251_nsq, leafHAr_of_sq c3251_har,
   c3251_r, c3251_e', c3251_f1, leafS2_of_sq c3251_s2, leafS3_of_sq c3251_s3,
   c3251_iso, leafR8_of_sq c3251_nof2 c3251_nof3 c3251_nof4z⟩
theorem not_tile'_3251 (D : CongruentDissection 3251) : False :=
  not_tile_of_conditions' 3251 C'_3251 D

private theorem c3254_sqf   : LeafSqf 3254   := by decide +kernel
private theorem c3254_range : LeafRange 3254  := by decide +kernel
private theorem c3254_ell   : LeafEll 3254    := by decide +kernel
private theorem c3254_nsq   : NSqChkSq 3254   := by decide +kernel
private theorem c3254_har   : HArithChkSq 3254 := by decide +kernel
private theorem c3254_r     : LeafR 3254      := by decide +kernel
private theorem c3254_e'    : LeafE' 3254     := by decide +kernel
private theorem c3254_f1    : LeafF1 3254     := Or.inl (by decide)
private theorem c3254_s2    : S2ChkSq 3254    := by decide +kernel
private theorem c3254_s3    : S3ChkSq 3254    := by decide +kernel
private theorem c3254_iso   : LeafIso 3254    := by decide +kernel
private theorem c3254_nof2  : NoF2ChkSq 3254  := by decide +kernel
private theorem c3254_nof3  : NoF3ChkSq 3254  := by decide +kernel
private theorem c3254_nof4z : NoF4zChkSq 3254 := by decide +kernel
theorem C'_3254 : C' 3254 :=
  ⟨c3254_sqf, c3254_range, c3254_ell, leafNSq_of_sq c3254_nsq, leafHAr_of_sq c3254_har,
   c3254_r, c3254_e', c3254_f1, leafS2_of_sq c3254_s2, leafS3_of_sq c3254_s3,
   c3254_iso, leafR8_of_sq c3254_nof2 c3254_nof3 c3254_nof4z⟩
theorem not_tile'_3254 (D : CongruentDissection 3254) : False :=
  not_tile_of_conditions' 3254 C'_3254 D

private theorem c3259_sqf   : LeafSqf 3259   := by decide +kernel
private theorem c3259_range : LeafRange 3259  := by decide +kernel
private theorem c3259_ell   : LeafEll 3259    := by decide +kernel
private theorem c3259_nsq   : NSqChkSq 3259   := by decide +kernel
private theorem c3259_har   : HArithChkSq 3259 := by decide +kernel
private theorem c3259_r     : LeafR 3259      := by decide +kernel
private theorem c3259_e'    : LeafE' 3259     := by decide +kernel
private theorem c3259_f1    : LeafF1 3259     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3259_s2    : S2ChkSq 3259    := by decide +kernel
private theorem c3259_s3    : S3ChkSq 3259    := by decide +kernel
private theorem c3259_iso   : LeafIso 3259    := by decide +kernel
private theorem c3259_nof2  : NoF2ChkSq 3259  := by decide +kernel
private theorem c3259_nof3  : NoF3ChkSq 3259  := by decide +kernel
private theorem c3259_nof4z : NoF4zChkSq 3259 := by decide +kernel
theorem C'_3259 : C' 3259 :=
  ⟨c3259_sqf, c3259_range, c3259_ell, leafNSq_of_sq c3259_nsq, leafHAr_of_sq c3259_har,
   c3259_r, c3259_e', c3259_f1, leafS2_of_sq c3259_s2, leafS3_of_sq c3259_s3,
   c3259_iso, leafR8_of_sq c3259_nof2 c3259_nof3 c3259_nof4z⟩
theorem not_tile'_3259 (D : CongruentDissection 3259) : False :=
  not_tile_of_conditions' 3259 C'_3259 D

private theorem c3261_sqf   : LeafSqf 3261   := by decide +kernel
private theorem c3261_range : LeafRange 3261  := by decide +kernel
private theorem c3261_ell   : LeafEll 3261    := by decide +kernel
private theorem c3261_nsq   : NSqChkSq 3261   := by decide +kernel
private theorem c3261_har   : HArithChkSq 3261 := by decide +kernel
private theorem c3261_r     : LeafR 3261      := by decide +kernel
private theorem c3261_e'    : LeafE' 3261     := by decide +kernel
private theorem c3261_f1    : LeafF1 3261     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3261_s2    : S2ChkSq 3261    := by decide +kernel
private theorem c3261_s3    : S3ChkSq 3261    := by decide +kernel
private theorem c3261_iso   : LeafIso 3261    := by decide +kernel
private theorem c3261_nof2  : NoF2ChkSq 3261  := by decide +kernel
private theorem c3261_nof3  : NoF3ChkSq 3261  := by decide +kernel
private theorem c3261_nof4z : NoF4zChkSq 3261 := by decide +kernel
theorem C'_3261 : C' 3261 :=
  ⟨c3261_sqf, c3261_range, c3261_ell, leafNSq_of_sq c3261_nsq, leafHAr_of_sq c3261_har,
   c3261_r, c3261_e', c3261_f1, leafS2_of_sq c3261_s2, leafS3_of_sq c3261_s3,
   c3261_iso, leafR8_of_sq c3261_nof2 c3261_nof3 c3261_nof4z⟩
theorem not_tile'_3261 (D : CongruentDissection 3261) : False :=
  not_tile_of_conditions' 3261 C'_3261 D

private theorem c3262_sqf   : LeafSqf 3262   := by decide +kernel
private theorem c3262_range : LeafRange 3262  := by decide +kernel
private theorem c3262_ell   : LeafEll 3262    := by decide +kernel
private theorem c3262_nsq   : NSqChkSq 3262   := by decide +kernel
private theorem c3262_har   : HArithChkSq 3262 := by decide +kernel
private theorem c3262_r     : LeafR 3262      := by decide +kernel
private theorem c3262_e'    : LeafE' 3262     := by decide +kernel
private theorem c3262_f1    : LeafF1 3262     := Or.inl (by decide)
private theorem c3262_s2    : S2ChkSq 3262    := by decide +kernel
private theorem c3262_s3    : S3ChkSq 3262    := by decide +kernel
private theorem c3262_iso   : LeafIso 3262    := by decide +kernel
private theorem c3262_nof2  : NoF2ChkSq 3262  := by decide +kernel
private theorem c3262_nof3  : NoF3ChkSq 3262  := by decide +kernel
private theorem c3262_nof4z : NoF4zChkSq 3262 := by decide +kernel
theorem C'_3262 : C' 3262 :=
  ⟨c3262_sqf, c3262_range, c3262_ell, leafNSq_of_sq c3262_nsq, leafHAr_of_sq c3262_har,
   c3262_r, c3262_e', c3262_f1, leafS2_of_sq c3262_s2, leafS3_of_sq c3262_s3,
   c3262_iso, leafR8_of_sq c3262_nof2 c3262_nof3 c3262_nof4z⟩
theorem not_tile'_3262 (D : CongruentDissection 3262) : False :=
  not_tile_of_conditions' 3262 C'_3262 D

end Erdos634.Draft.AllN2

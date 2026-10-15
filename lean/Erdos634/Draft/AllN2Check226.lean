/- AllN2Check226: N = 4249, 4254, 4255, 4259, 4262
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4249_sqf   : LeafSqf 4249   := by decide +kernel
private theorem c4249_range : LeafRange 4249  := by decide +kernel
private theorem c4249_ell   : LeafEll 4249    := by decide +kernel
private theorem c4249_nsq   : NSqChkSq 4249   := by decide +kernel
private theorem c4249_har   : HArithChkSq 4249 := by decide +kernel
private theorem c4249_r     : LeafR 4249      := by decide +kernel
private theorem c4249_e'    : LeafE' 4249     := by decide +kernel
private theorem c4249_f1    : LeafF1 4249     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4249_s2    : S2ChkSq 4249    := by decide +kernel
private theorem c4249_s3    : S3ChkSq 4249    := by decide +kernel
private theorem c4249_iso   : LeafIso 4249    := by decide +kernel
private theorem c4249_nof2  : NoF2ChkSq 4249  := by decide +kernel
private theorem c4249_nof3  : NoF3ChkSq 4249  := by decide +kernel
private theorem c4249_nof4z : NoF4zChkSq 4249 := by decide +kernel
theorem C'_4249 : C' 4249 :=
  ⟨c4249_sqf, c4249_range, c4249_ell, leafNSq_of_sq c4249_nsq, leafHAr_of_sq c4249_har,
   c4249_r, c4249_e', c4249_f1, leafS2_of_sq c4249_s2, leafS3_of_sq c4249_s3,
   c4249_iso, leafR8_of_sq c4249_nof2 c4249_nof3 c4249_nof4z⟩
theorem not_tile'_4249 (D : CongruentDissection 4249) : False :=
  not_tile_of_conditions' 4249 C'_4249 D

private theorem c4254_sqf   : LeafSqf 4254   := by decide +kernel
private theorem c4254_range : LeafRange 4254  := by decide +kernel
private theorem c4254_ell   : LeafEll 4254    := by decide +kernel
private theorem c4254_nsq   : NSqChkSq 4254   := by decide +kernel
private theorem c4254_har   : HArithChkSq 4254 := by decide +kernel
private theorem c4254_r     : LeafR 4254      := by decide +kernel
private theorem c4254_e'    : LeafE' 4254     := by decide +kernel
private theorem c4254_f1    : LeafF1 4254     := Or.inl (by decide)
private theorem c4254_s2    : S2ChkSq 4254    := by decide +kernel
private theorem c4254_s3    : S3ChkSq 4254    := by decide +kernel
private theorem c4254_iso   : LeafIso 4254    := by decide +kernel
private theorem c4254_nof2  : NoF2ChkSq 4254  := by decide +kernel
private theorem c4254_nof3  : NoF3ChkSq 4254  := by decide +kernel
private theorem c4254_nof4z : NoF4zChkSq 4254 := by decide +kernel
theorem C'_4254 : C' 4254 :=
  ⟨c4254_sqf, c4254_range, c4254_ell, leafNSq_of_sq c4254_nsq, leafHAr_of_sq c4254_har,
   c4254_r, c4254_e', c4254_f1, leafS2_of_sq c4254_s2, leafS3_of_sq c4254_s3,
   c4254_iso, leafR8_of_sq c4254_nof2 c4254_nof3 c4254_nof4z⟩
theorem not_tile'_4254 (D : CongruentDissection 4254) : False :=
  not_tile_of_conditions' 4254 C'_4254 D

private theorem c4255_sqf   : LeafSqf 4255   := by decide +kernel
private theorem c4255_range : LeafRange 4255  := by decide +kernel
private theorem c4255_ell   : LeafEll 4255    := by decide +kernel
private theorem c4255_nsq   : NSqChkSq 4255   := by decide +kernel
private theorem c4255_har   : HArithChkSq 4255 := by decide +kernel
private theorem c4255_r     : LeafR 4255      := by decide +kernel
private theorem c4255_e'    : LeafE' 4255     := by decide +kernel
private theorem c4255_f1    : LeafF1 4255     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4255_s2    : S2ChkSq 4255    := by decide +kernel
private theorem c4255_s3    : S3ChkSq 4255    := by decide +kernel
private theorem c4255_iso   : LeafIso 4255    := by decide +kernel
private theorem c4255_nof2  : NoF2ChkSq 4255  := by decide +kernel
private theorem c4255_nof3  : NoF3ChkSq 4255  := by decide +kernel
private theorem c4255_nof4z : NoF4zChkSq 4255 := by decide +kernel
theorem C'_4255 : C' 4255 :=
  ⟨c4255_sqf, c4255_range, c4255_ell, leafNSq_of_sq c4255_nsq, leafHAr_of_sq c4255_har,
   c4255_r, c4255_e', c4255_f1, leafS2_of_sq c4255_s2, leafS3_of_sq c4255_s3,
   c4255_iso, leafR8_of_sq c4255_nof2 c4255_nof3 c4255_nof4z⟩
theorem not_tile'_4255 (D : CongruentDissection 4255) : False :=
  not_tile_of_conditions' 4255 C'_4255 D

private theorem c4259_sqf   : LeafSqf 4259   := by decide +kernel
private theorem c4259_range : LeafRange 4259  := by decide +kernel
private theorem c4259_ell   : LeafEll 4259    := by decide +kernel
private theorem c4259_nsq   : NSqChkSq 4259   := by decide +kernel
private theorem c4259_har   : HArithChkSq 4259 := by decide +kernel
private theorem c4259_r     : LeafR 4259      := by decide +kernel
private theorem c4259_e'    : LeafE' 4259     := by decide +kernel
private theorem c4259_f1    : LeafF1 4259     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4259_s2    : S2ChkSq 4259    := by decide +kernel
private theorem c4259_s3    : S3ChkSq 4259    := by decide +kernel
private theorem c4259_iso   : LeafIso 4259    := by decide +kernel
private theorem c4259_nof2  : NoF2ChkSq 4259  := by decide +kernel
private theorem c4259_nof3  : NoF3ChkSq 4259  := by decide +kernel
private theorem c4259_nof4z : NoF4zChkSq 4259 := by decide +kernel
theorem C'_4259 : C' 4259 :=
  ⟨c4259_sqf, c4259_range, c4259_ell, leafNSq_of_sq c4259_nsq, leafHAr_of_sq c4259_har,
   c4259_r, c4259_e', c4259_f1, leafS2_of_sq c4259_s2, leafS3_of_sq c4259_s3,
   c4259_iso, leafR8_of_sq c4259_nof2 c4259_nof3 c4259_nof4z⟩
theorem not_tile'_4259 (D : CongruentDissection 4259) : False :=
  not_tile_of_conditions' 4259 C'_4259 D

private theorem c4262_sqf   : LeafSqf 4262   := by decide +kernel
private theorem c4262_range : LeafRange 4262  := by decide +kernel
private theorem c4262_ell   : LeafEll 4262    := by decide +kernel
private theorem c4262_nsq   : NSqChkSq 4262   := by decide +kernel
private theorem c4262_har   : HArithChkSq 4262 := by decide +kernel
private theorem c4262_r     : LeafR 4262      := by decide +kernel
private theorem c4262_e'    : LeafE' 4262     := by decide +kernel
private theorem c4262_f1    : LeafF1 4262     := Or.inl (by decide)
private theorem c4262_s2    : S2ChkSq 4262    := by decide +kernel
private theorem c4262_s3    : S3ChkSq 4262    := by decide +kernel
private theorem c4262_iso   : LeafIso 4262    := by decide +kernel
private theorem c4262_nof2  : NoF2ChkSq 4262  := by decide +kernel
private theorem c4262_nof3  : NoF3ChkSq 4262  := by decide +kernel
private theorem c4262_nof4z : NoF4zChkSq 4262 := by decide +kernel
theorem C'_4262 : C' 4262 :=
  ⟨c4262_sqf, c4262_range, c4262_ell, leafNSq_of_sq c4262_nsq, leafHAr_of_sq c4262_har,
   c4262_r, c4262_e', c4262_f1, leafS2_of_sq c4262_s2, leafS3_of_sq c4262_s3,
   c4262_iso, leafR8_of_sq c4262_nof2 c4262_nof3 c4262_nof4z⟩
theorem not_tile'_4262 (D : CongruentDissection 4262) : False :=
  not_tile_of_conditions' 4262 C'_4262 D

end Erdos634.Draft.AllN2

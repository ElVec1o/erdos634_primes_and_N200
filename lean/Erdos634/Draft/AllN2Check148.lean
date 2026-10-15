/- AllN2Check148: N = 3227, 3230, 3235, 3238, 3239
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3227_sqf   : LeafSqf 3227   := by decide +kernel
private theorem c3227_range : LeafRange 3227  := by decide +kernel
private theorem c3227_ell   : LeafEll 3227    := by decide +kernel
private theorem c3227_nsq   : NSqChkSq 3227   := by decide +kernel
private theorem c3227_har   : HArithChkSq 3227 := by decide +kernel
private theorem c3227_r     : LeafR 3227      := by decide +kernel
private theorem c3227_e'    : LeafE' 3227     := by decide +kernel
private theorem c3227_f1    : LeafF1 3227     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3227_s2    : S2ChkSq 3227    := by decide +kernel
private theorem c3227_s3    : S3ChkSq 3227    := by decide +kernel
private theorem c3227_iso   : LeafIso 3227    := by decide +kernel
private theorem c3227_nof2  : NoF2ChkSq 3227  := by decide +kernel
private theorem c3227_nof3  : NoF3ChkSq 3227  := by decide +kernel
private theorem c3227_nof4z : NoF4zChkSq 3227 := by decide +kernel
theorem C'_3227 : C' 3227 :=
  ⟨c3227_sqf, c3227_range, c3227_ell, leafNSq_of_sq c3227_nsq, leafHAr_of_sq c3227_har,
   c3227_r, c3227_e', c3227_f1, leafS2_of_sq c3227_s2, leafS3_of_sq c3227_s3,
   c3227_iso, leafR8_of_sq c3227_nof2 c3227_nof3 c3227_nof4z⟩
theorem not_tile'_3227 (D : CongruentDissection 3227) : False :=
  not_tile_of_conditions' 3227 C'_3227 D

private theorem c3230_sqf   : LeafSqf 3230   := by decide +kernel
private theorem c3230_range : LeafRange 3230  := by decide +kernel
private theorem c3230_ell   : LeafEll 3230    := by decide +kernel
private theorem c3230_nsq   : NSqChkSq 3230   := by decide +kernel
private theorem c3230_har   : HArithChkSq 3230 := by decide +kernel
private theorem c3230_r     : LeafR 3230      := by decide +kernel
private theorem c3230_e'    : LeafE' 3230     := by decide +kernel
private theorem c3230_f1    : LeafF1 3230     := Or.inl (by decide)
private theorem c3230_s2    : S2ChkSq 3230    := by decide +kernel
private theorem c3230_s3    : S3ChkSq 3230    := by decide +kernel
private theorem c3230_iso   : LeafIso 3230    := by decide +kernel
private theorem c3230_nof2  : NoF2ChkSq 3230  := by decide +kernel
private theorem c3230_nof3  : NoF3ChkSq 3230  := by decide +kernel
private theorem c3230_nof4z : NoF4zChkSq 3230 := by decide +kernel
theorem C'_3230 : C' 3230 :=
  ⟨c3230_sqf, c3230_range, c3230_ell, leafNSq_of_sq c3230_nsq, leafHAr_of_sq c3230_har,
   c3230_r, c3230_e', c3230_f1, leafS2_of_sq c3230_s2, leafS3_of_sq c3230_s3,
   c3230_iso, leafR8_of_sq c3230_nof2 c3230_nof3 c3230_nof4z⟩
theorem not_tile'_3230 (D : CongruentDissection 3230) : False :=
  not_tile_of_conditions' 3230 C'_3230 D

private theorem c3235_sqf   : LeafSqf 3235   := by decide +kernel
private theorem c3235_range : LeafRange 3235  := by decide +kernel
private theorem c3235_ell   : LeafEll 3235    := by decide +kernel
private theorem c3235_nsq   : NSqChkSq 3235   := by decide +kernel
private theorem c3235_har   : HArithChkSq 3235 := by decide +kernel
private theorem c3235_r     : LeafR 3235      := by decide +kernel
private theorem c3235_e'    : LeafE' 3235     := by decide +kernel
private theorem c3235_f1    : LeafF1 3235     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3235_s2    : S2ChkSq 3235    := by decide +kernel
private theorem c3235_s3    : S3ChkSq 3235    := by decide +kernel
private theorem c3235_iso   : LeafIso 3235    := by decide +kernel
private theorem c3235_nof2  : NoF2ChkSq 3235  := by decide +kernel
private theorem c3235_nof3  : NoF3ChkSq 3235  := by decide +kernel
private theorem c3235_nof4z : NoF4zChkSq 3235 := by decide +kernel
theorem C'_3235 : C' 3235 :=
  ⟨c3235_sqf, c3235_range, c3235_ell, leafNSq_of_sq c3235_nsq, leafHAr_of_sq c3235_har,
   c3235_r, c3235_e', c3235_f1, leafS2_of_sq c3235_s2, leafS3_of_sq c3235_s3,
   c3235_iso, leafR8_of_sq c3235_nof2 c3235_nof3 c3235_nof4z⟩
theorem not_tile'_3235 (D : CongruentDissection 3235) : False :=
  not_tile_of_conditions' 3235 C'_3235 D

private theorem c3238_sqf   : LeafSqf 3238   := by decide +kernel
private theorem c3238_range : LeafRange 3238  := by decide +kernel
private theorem c3238_ell   : LeafEll 3238    := by decide +kernel
private theorem c3238_nsq   : NSqChkSq 3238   := by decide +kernel
private theorem c3238_har   : HArithChkSq 3238 := by decide +kernel
private theorem c3238_r     : LeafR 3238      := by decide +kernel
private theorem c3238_e'    : LeafE' 3238     := by decide +kernel
private theorem c3238_f1    : LeafF1 3238     := Or.inl (by decide)
private theorem c3238_s2    : S2ChkSq 3238    := by decide +kernel
private theorem c3238_s3    : S3ChkSq 3238    := by decide +kernel
private theorem c3238_iso   : LeafIso 3238    := by decide +kernel
private theorem c3238_nof2  : NoF2ChkSq 3238  := by decide +kernel
private theorem c3238_nof3  : NoF3ChkSq 3238  := by decide +kernel
private theorem c3238_nof4z : NoF4zChkSq 3238 := by decide +kernel
theorem C'_3238 : C' 3238 :=
  ⟨c3238_sqf, c3238_range, c3238_ell, leafNSq_of_sq c3238_nsq, leafHAr_of_sq c3238_har,
   c3238_r, c3238_e', c3238_f1, leafS2_of_sq c3238_s2, leafS3_of_sq c3238_s3,
   c3238_iso, leafR8_of_sq c3238_nof2 c3238_nof3 c3238_nof4z⟩
theorem not_tile'_3238 (D : CongruentDissection 3238) : False :=
  not_tile_of_conditions' 3238 C'_3238 D

private theorem c3239_sqf   : LeafSqf 3239   := by decide +kernel
private theorem c3239_range : LeafRange 3239  := by decide +kernel
private theorem c3239_ell   : LeafEll 3239    := by decide +kernel
private theorem c3239_nsq   : NSqChkSq 3239   := by decide +kernel
private theorem c3239_har   : HArithChkSq 3239 := by decide +kernel
private theorem c3239_r     : LeafR 3239      := by decide +kernel
private theorem c3239_e'    : LeafE' 3239     := by decide +kernel
private theorem c3239_f1    : LeafF1 3239     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3239_s2    : S2ChkSq 3239    := by decide +kernel
private theorem c3239_s3    : S3ChkSq 3239    := by decide +kernel
private theorem c3239_iso   : LeafIso 3239    := by decide +kernel
private theorem c3239_nof2  : NoF2ChkSq 3239  := by decide +kernel
private theorem c3239_nof3  : NoF3ChkSq 3239  := by decide +kernel
private theorem c3239_nof4z : NoF4zChkSq 3239 := by decide +kernel
theorem C'_3239 : C' 3239 :=
  ⟨c3239_sqf, c3239_range, c3239_ell, leafNSq_of_sq c3239_nsq, leafHAr_of_sq c3239_har,
   c3239_r, c3239_e', c3239_f1, leafS2_of_sq c3239_s2, leafS3_of_sq c3239_s3,
   c3239_iso, leafR8_of_sq c3239_nof2 c3239_nof3 c3239_nof4z⟩
theorem not_tile'_3239 (D : CongruentDissection 3239) : False :=
  not_tile_of_conditions' 3239 C'_3239 D

end Erdos634.Draft.AllN2

/- AllN2Check11: N = 235, 237, 249
   Squarefree exclusions via C' with sqrt-bounded checks (Wave-2 OOM fix). -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c235_sqf   : LeafSqf 235   := by decide +kernel
private theorem c235_range : LeafRange 235  := by decide +kernel
private theorem c235_ell   : LeafEll 235    := by decide +kernel
private theorem c235_nsq   : NSqChkSq 235   := by decide +kernel
private theorem c235_har   : HArithChkSq 235 := by decide +kernel
private theorem c235_r     : LeafR 235      := by decide +kernel
private theorem c235_e'    : LeafE' 235     := by decide +kernel
private theorem c235_f1    : LeafF1 235     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c235_s2    : S2ChkSq 235    := by decide +kernel
private theorem c235_s3    : S3ChkSq 235    := by decide +kernel
private theorem c235_iso   : LeafIso 235    := by decide +kernel
private theorem c235_nof2  : NoF2ChkSq 235  := by decide +kernel
private theorem c235_nof3  : NoF3ChkSq 235  := by decide +kernel
private theorem c235_nof4z : NoF4zChkSq 235 := by decide +kernel
theorem C'_235 : C' 235 :=
  ⟨c235_sqf, c235_range, c235_ell, leafNSq_of_sq c235_nsq, leafHAr_of_sq c235_har,
   c235_r, c235_e', c235_f1, leafS2_of_sq c235_s2, leafS3_of_sq c235_s3,
   c235_iso, leafR8_of_sq c235_nof2 c235_nof3 c235_nof4z⟩
theorem not_tile'_235 (D : CongruentDissection 235) : False :=
  not_tile_of_conditions' 235 C'_235 D

private theorem c237_sqf   : LeafSqf 237   := by decide +kernel
private theorem c237_range : LeafRange 237  := by decide +kernel
private theorem c237_ell   : LeafEll 237    := by decide +kernel
private theorem c237_nsq   : NSqChkSq 237   := by decide +kernel
private theorem c237_har   : HArithChkSq 237 := by decide +kernel
private theorem c237_r     : LeafR 237      := by decide +kernel
private theorem c237_e'    : LeafE' 237     := by decide +kernel
private theorem c237_f1    : LeafF1 237     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c237_s2    : S2ChkSq 237    := by decide +kernel
private theorem c237_s3    : S3ChkSq 237    := by decide +kernel
private theorem c237_iso   : LeafIso 237    := by decide +kernel
private theorem c237_nof2  : NoF2ChkSq 237  := by decide +kernel
private theorem c237_nof3  : NoF3ChkSq 237  := by decide +kernel
private theorem c237_nof4z : NoF4zChkSq 237 := by decide +kernel
theorem C'_237 : C' 237 :=
  ⟨c237_sqf, c237_range, c237_ell, leafNSq_of_sq c237_nsq, leafHAr_of_sq c237_har,
   c237_r, c237_e', c237_f1, leafS2_of_sq c237_s2, leafS3_of_sq c237_s3,
   c237_iso, leafR8_of_sq c237_nof2 c237_nof3 c237_nof4z⟩
theorem not_tile'_237 (D : CongruentDissection 237) : False :=
  not_tile_of_conditions' 237 C'_237 D

private theorem c249_sqf   : LeafSqf 249   := by decide +kernel
private theorem c249_range : LeafRange 249  := by decide +kernel
private theorem c249_ell   : LeafEll 249    := by decide +kernel
private theorem c249_nsq   : NSqChkSq 249   := by decide +kernel
private theorem c249_har   : HArithChkSq 249 := by decide +kernel
private theorem c249_r     : LeafR 249      := by decide +kernel
private theorem c249_e'    : LeafE' 249     := by decide +kernel
private theorem c249_f1    : LeafF1 249     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c249_s2    : S2ChkSq 249    := by decide +kernel
private theorem c249_s3    : S3ChkSq 249    := by decide +kernel
private theorem c249_iso   : LeafIso 249    := by decide +kernel
private theorem c249_nof2  : NoF2ChkSq 249  := by decide +kernel
private theorem c249_nof3  : NoF3ChkSq 249  := by decide +kernel
private theorem c249_nof4z : NoF4zChkSq 249 := by decide +kernel
theorem C'_249 : C' 249 :=
  ⟨c249_sqf, c249_range, c249_ell, leafNSq_of_sq c249_nsq, leafHAr_of_sq c249_har,
   c249_r, c249_e', c249_f1, leafS2_of_sq c249_s2, leafS3_of_sq c249_s3,
   c249_iso, leafR8_of_sq c249_nof2 c249_nof3 c249_nof4z⟩
theorem not_tile'_249 (D : CongruentDissection 249) : False :=
  not_tile_of_conditions' 249 C'_249 D

end Erdos634.Draft.AllN2

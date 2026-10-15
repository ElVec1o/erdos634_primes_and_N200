/- AllN2Check70: N = 2230, 2231, 2233, 2238, 2239
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2230_sqf   : LeafSqf 2230   := by decide +kernel
private theorem c2230_range : LeafRange 2230  := by decide +kernel
private theorem c2230_ell   : LeafEll 2230    := by decide +kernel
private theorem c2230_nsq   : NSqChkSq 2230   := by decide +kernel
private theorem c2230_har   : HArithChkSq 2230 := by decide +kernel
private theorem c2230_r     : LeafR 2230      := by decide +kernel
private theorem c2230_e'    : LeafE' 2230     := by decide +kernel
private theorem c2230_f1    : LeafF1 2230     := Or.inl (by decide)
private theorem c2230_s2    : S2ChkSq 2230    := by decide +kernel
private theorem c2230_s3    : S3ChkSq 2230    := by decide +kernel
private theorem c2230_iso   : LeafIso 2230    := by decide +kernel
private theorem c2230_nof2  : NoF2ChkSq 2230  := by decide +kernel
private theorem c2230_nof3  : NoF3ChkSq 2230  := by decide +kernel
private theorem c2230_nof4z : NoF4zChkSq 2230 := by decide +kernel
theorem C'_2230 : C' 2230 :=
  ⟨c2230_sqf, c2230_range, c2230_ell, leafNSq_of_sq c2230_nsq, leafHAr_of_sq c2230_har,
   c2230_r, c2230_e', c2230_f1, leafS2_of_sq c2230_s2, leafS3_of_sq c2230_s3,
   c2230_iso, leafR8_of_sq c2230_nof2 c2230_nof3 c2230_nof4z⟩
theorem not_tile'_2230 (D : CongruentDissection 2230) : False :=
  not_tile_of_conditions' 2230 C'_2230 D

private theorem c2231_sqf   : LeafSqf 2231   := by decide +kernel
private theorem c2231_range : LeafRange 2231  := by decide +kernel
private theorem c2231_ell   : LeafEll 2231    := by decide +kernel
private theorem c2231_nsq   : NSqChkSq 2231   := by decide +kernel
private theorem c2231_har   : HArithChkSq 2231 := by decide +kernel
private theorem c2231_r     : LeafR 2231      := by decide +kernel
private theorem c2231_e'    : LeafE' 2231     := by decide +kernel
private theorem c2231_f1    : LeafF1 2231     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2231_s2    : S2ChkSq 2231    := by decide +kernel
private theorem c2231_s3    : S3ChkSq 2231    := by decide +kernel
private theorem c2231_iso   : LeafIso 2231    := by decide +kernel
private theorem c2231_nof2  : NoF2ChkSq 2231  := by decide +kernel
private theorem c2231_nof3  : NoF3ChkSq 2231  := by decide +kernel
private theorem c2231_nof4z : NoF4zChkSq 2231 := by decide +kernel
theorem C'_2231 : C' 2231 :=
  ⟨c2231_sqf, c2231_range, c2231_ell, leafNSq_of_sq c2231_nsq, leafHAr_of_sq c2231_har,
   c2231_r, c2231_e', c2231_f1, leafS2_of_sq c2231_s2, leafS3_of_sq c2231_s3,
   c2231_iso, leafR8_of_sq c2231_nof2 c2231_nof3 c2231_nof4z⟩
theorem not_tile'_2231 (D : CongruentDissection 2231) : False :=
  not_tile_of_conditions' 2231 C'_2231 D

private theorem c2233_sqf   : LeafSqf 2233   := by decide +kernel
private theorem c2233_range : LeafRange 2233  := by decide +kernel
private theorem c2233_ell   : LeafEll 2233    := by decide +kernel
private theorem c2233_nsq   : NSqChkSq 2233   := by decide +kernel
private theorem c2233_har   : HArithChkSq 2233 := by decide +kernel
private theorem c2233_r     : LeafR 2233      := by decide +kernel
private theorem c2233_e'    : LeafE' 2233     := by decide +kernel
private theorem c2233_f1    : LeafF1 2233     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2233_s2    : S2ChkSq 2233    := by decide +kernel
private theorem c2233_s3    : S3ChkSq 2233    := by decide +kernel
private theorem c2233_iso   : LeafIso 2233    := by decide +kernel
private theorem c2233_nof2  : NoF2ChkSq 2233  := by decide +kernel
private theorem c2233_nof3  : NoF3ChkSq 2233  := by decide +kernel
private theorem c2233_nof4z : NoF4zChkSq 2233 := by decide +kernel
theorem C'_2233 : C' 2233 :=
  ⟨c2233_sqf, c2233_range, c2233_ell, leafNSq_of_sq c2233_nsq, leafHAr_of_sq c2233_har,
   c2233_r, c2233_e', c2233_f1, leafS2_of_sq c2233_s2, leafS3_of_sq c2233_s3,
   c2233_iso, leafR8_of_sq c2233_nof2 c2233_nof3 c2233_nof4z⟩
theorem not_tile'_2233 (D : CongruentDissection 2233) : False :=
  not_tile_of_conditions' 2233 C'_2233 D

private theorem c2238_sqf   : LeafSqf 2238   := by decide +kernel
private theorem c2238_range : LeafRange 2238  := by decide +kernel
private theorem c2238_ell   : LeafEll 2238    := by decide +kernel
private theorem c2238_nsq   : NSqChkSq 2238   := by decide +kernel
private theorem c2238_har   : HArithChkSq 2238 := by decide +kernel
private theorem c2238_r     : LeafR 2238      := by decide +kernel
private theorem c2238_e'    : LeafE' 2238     := by decide +kernel
private theorem c2238_f1    : LeafF1 2238     := Or.inl (by decide)
private theorem c2238_s2    : S2ChkSq 2238    := by decide +kernel
private theorem c2238_s3    : S3ChkSq 2238    := by decide +kernel
private theorem c2238_iso   : LeafIso 2238    := by decide +kernel
private theorem c2238_nof2  : NoF2ChkSq 2238  := by decide +kernel
private theorem c2238_nof3  : NoF3ChkSq 2238  := by decide +kernel
private theorem c2238_nof4z : NoF4zChkSq 2238 := by decide +kernel
theorem C'_2238 : C' 2238 :=
  ⟨c2238_sqf, c2238_range, c2238_ell, leafNSq_of_sq c2238_nsq, leafHAr_of_sq c2238_har,
   c2238_r, c2238_e', c2238_f1, leafS2_of_sq c2238_s2, leafS3_of_sq c2238_s3,
   c2238_iso, leafR8_of_sq c2238_nof2 c2238_nof3 c2238_nof4z⟩
theorem not_tile'_2238 (D : CongruentDissection 2238) : False :=
  not_tile_of_conditions' 2238 C'_2238 D

private theorem c2239_sqf   : LeafSqf 2239   := by decide +kernel
private theorem c2239_range : LeafRange 2239  := by decide +kernel
private theorem c2239_ell   : LeafEll 2239    := by decide +kernel
private theorem c2239_nsq   : NSqChkSq 2239   := by decide +kernel
private theorem c2239_har   : HArithChkSq 2239 := by decide +kernel
private theorem c2239_r     : LeafR 2239      := by decide +kernel
private theorem c2239_e'    : LeafE' 2239     := by decide +kernel
private theorem c2239_f1    : LeafF1 2239     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2239_s2    : S2ChkSq 2239    := by decide +kernel
private theorem c2239_s3    : S3ChkSq 2239    := by decide +kernel
private theorem c2239_iso   : LeafIso 2239    := by decide +kernel
private theorem c2239_nof2  : NoF2ChkSq 2239  := by decide +kernel
private theorem c2239_nof3  : NoF3ChkSq 2239  := by decide +kernel
private theorem c2239_nof4z : NoF4zChkSq 2239 := by decide +kernel
theorem C'_2239 : C' 2239 :=
  ⟨c2239_sqf, c2239_range, c2239_ell, leafNSq_of_sq c2239_nsq, leafHAr_of_sq c2239_har,
   c2239_r, c2239_e', c2239_f1, leafS2_of_sq c2239_s2, leafS3_of_sq c2239_s3,
   c2239_iso, leafR8_of_sq c2239_nof2 c2239_nof3 c2239_nof4z⟩
theorem not_tile'_2239 (D : CongruentDissection 2239) : False :=
  not_tile_of_conditions' 2239 C'_2239 D

end Erdos634.Draft.AllN2

/- AllN2Check137: N = 3083, 3086, 3090, 3091, 3093
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3083_sqf   : LeafSqf 3083   := by decide +kernel
private theorem c3083_range : LeafRange 3083  := by decide +kernel
private theorem c3083_ell   : LeafEll 3083    := by decide +kernel
private theorem c3083_nsq   : NSqChkSq 3083   := by decide +kernel
private theorem c3083_har   : HArithChkSq 3083 := by decide +kernel
private theorem c3083_r     : LeafR 3083      := by decide +kernel
private theorem c3083_e'    : LeafE' 3083     := by decide +kernel
private theorem c3083_f1    : LeafF1 3083     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3083_s2    : S2ChkSq 3083    := by decide +kernel
private theorem c3083_s3    : S3ChkSq 3083    := by decide +kernel
private theorem c3083_iso   : LeafIso 3083    := by decide +kernel
private theorem c3083_nof2  : NoF2ChkSq 3083  := by decide +kernel
private theorem c3083_nof3  : NoF3ChkSq 3083  := by decide +kernel
private theorem c3083_nof4z : NoF4zChkSq 3083 := by decide +kernel
theorem C'_3083 : C' 3083 :=
  ⟨c3083_sqf, c3083_range, c3083_ell, leafNSq_of_sq c3083_nsq, leafHAr_of_sq c3083_har,
   c3083_r, c3083_e', c3083_f1, leafS2_of_sq c3083_s2, leafS3_of_sq c3083_s3,
   c3083_iso, leafR8_of_sq c3083_nof2 c3083_nof3 c3083_nof4z⟩
theorem not_tile'_3083 (D : CongruentDissection 3083) : False :=
  not_tile_of_conditions' 3083 C'_3083 D

private theorem c3086_sqf   : LeafSqf 3086   := by decide +kernel
private theorem c3086_range : LeafRange 3086  := by decide +kernel
private theorem c3086_ell   : LeafEll 3086    := by decide +kernel
private theorem c3086_nsq   : NSqChkSq 3086   := by decide +kernel
private theorem c3086_har   : HArithChkSq 3086 := by decide +kernel
private theorem c3086_r     : LeafR 3086      := by decide +kernel
private theorem c3086_e'    : LeafE' 3086     := by decide +kernel
private theorem c3086_f1    : LeafF1 3086     := Or.inl (by decide)
private theorem c3086_s2    : S2ChkSq 3086    := by decide +kernel
private theorem c3086_s3    : S3ChkSq 3086    := by decide +kernel
private theorem c3086_iso   : LeafIso 3086    := by decide +kernel
private theorem c3086_nof2  : NoF2ChkSq 3086  := by decide +kernel
private theorem c3086_nof3  : NoF3ChkSq 3086  := by decide +kernel
private theorem c3086_nof4z : NoF4zChkSq 3086 := by decide +kernel
theorem C'_3086 : C' 3086 :=
  ⟨c3086_sqf, c3086_range, c3086_ell, leafNSq_of_sq c3086_nsq, leafHAr_of_sq c3086_har,
   c3086_r, c3086_e', c3086_f1, leafS2_of_sq c3086_s2, leafS3_of_sq c3086_s3,
   c3086_iso, leafR8_of_sq c3086_nof2 c3086_nof3 c3086_nof4z⟩
theorem not_tile'_3086 (D : CongruentDissection 3086) : False :=
  not_tile_of_conditions' 3086 C'_3086 D

private theorem c3090_sqf   : LeafSqf 3090   := by decide +kernel
private theorem c3090_range : LeafRange 3090  := by decide +kernel
private theorem c3090_ell   : LeafEll 3090    := by decide +kernel
private theorem c3090_nsq   : NSqChkSq 3090   := by decide +kernel
private theorem c3090_har   : HArithChkSq 3090 := by decide +kernel
private theorem c3090_r     : LeafR 3090      := by decide +kernel
private theorem c3090_e'    : LeafE' 3090     := by decide +kernel
private theorem c3090_f1    : LeafF1 3090     := Or.inl (by decide)
private theorem c3090_s2    : S2ChkSq 3090    := by decide +kernel
private theorem c3090_s3    : S3ChkSq 3090    := by decide +kernel
private theorem c3090_iso   : LeafIso 3090    := by decide +kernel
private theorem c3090_nof2  : NoF2ChkSq 3090  := by decide +kernel
private theorem c3090_nof3  : NoF3ChkSq 3090  := by decide +kernel
private theorem c3090_nof4z : NoF4zChkSq 3090 := by decide +kernel
theorem C'_3090 : C' 3090 :=
  ⟨c3090_sqf, c3090_range, c3090_ell, leafNSq_of_sq c3090_nsq, leafHAr_of_sq c3090_har,
   c3090_r, c3090_e', c3090_f1, leafS2_of_sq c3090_s2, leafS3_of_sq c3090_s3,
   c3090_iso, leafR8_of_sq c3090_nof2 c3090_nof3 c3090_nof4z⟩
theorem not_tile'_3090 (D : CongruentDissection 3090) : False :=
  not_tile_of_conditions' 3090 C'_3090 D

private theorem c3091_sqf   : LeafSqf 3091   := by decide +kernel
private theorem c3091_range : LeafRange 3091  := by decide +kernel
private theorem c3091_ell   : LeafEll 3091    := by decide +kernel
private theorem c3091_nsq   : NSqChkSq 3091   := by decide +kernel
private theorem c3091_har   : HArithChkSq 3091 := by decide +kernel
private theorem c3091_r     : LeafR 3091      := by decide +kernel
private theorem c3091_e'    : LeafE' 3091     := by decide +kernel
private theorem c3091_f1    : LeafF1 3091     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3091_s2    : S2ChkSq 3091    := by decide +kernel
private theorem c3091_s3    : S3ChkSq 3091    := by decide +kernel
private theorem c3091_iso   : LeafIso 3091    := by decide +kernel
private theorem c3091_nof2  : NoF2ChkSq 3091  := by decide +kernel
private theorem c3091_nof3  : NoF3ChkSq 3091  := by decide +kernel
private theorem c3091_nof4z : NoF4zChkSq 3091 := by decide +kernel
theorem C'_3091 : C' 3091 :=
  ⟨c3091_sqf, c3091_range, c3091_ell, leafNSq_of_sq c3091_nsq, leafHAr_of_sq c3091_har,
   c3091_r, c3091_e', c3091_f1, leafS2_of_sq c3091_s2, leafS3_of_sq c3091_s3,
   c3091_iso, leafR8_of_sq c3091_nof2 c3091_nof3 c3091_nof4z⟩
theorem not_tile'_3091 (D : CongruentDissection 3091) : False :=
  not_tile_of_conditions' 3091 C'_3091 D

private theorem c3093_sqf   : LeafSqf 3093   := by decide +kernel
private theorem c3093_range : LeafRange 3093  := by decide +kernel
private theorem c3093_ell   : LeafEll 3093    := by decide +kernel
private theorem c3093_nsq   : NSqChkSq 3093   := by decide +kernel
private theorem c3093_har   : HArithChkSq 3093 := by decide +kernel
private theorem c3093_r     : LeafR 3093      := by decide +kernel
private theorem c3093_e'    : LeafE' 3093     := by decide +kernel
private theorem c3093_f1    : LeafF1 3093     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3093_s2    : S2ChkSq 3093    := by decide +kernel
private theorem c3093_s3    : S3ChkSq 3093    := by decide +kernel
private theorem c3093_iso   : LeafIso 3093    := by decide +kernel
private theorem c3093_nof2  : NoF2ChkSq 3093  := by decide +kernel
private theorem c3093_nof3  : NoF3ChkSq 3093  := by decide +kernel
private theorem c3093_nof4z : NoF4zChkSq 3093 := by decide +kernel
theorem C'_3093 : C' 3093 :=
  ⟨c3093_sqf, c3093_range, c3093_ell, leafNSq_of_sq c3093_nsq, leafHAr_of_sq c3093_har,
   c3093_r, c3093_e', c3093_f1, leafS2_of_sq c3093_s2, leafS3_of_sq c3093_s3,
   c3093_iso, leafR8_of_sq c3093_nof2 c3093_nof3 c3093_nof4z⟩
theorem not_tile'_3093 (D : CongruentDissection 3093) : False :=
  not_tile_of_conditions' 3093 C'_3093 D

end Erdos634.Draft.AllN2

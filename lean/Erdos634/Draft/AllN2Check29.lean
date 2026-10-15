/- AllN2Check29: N = 1209, 1211, 1227, 1235, 1243
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1209_sqf   : LeafSqf 1209   := by decide +kernel
private theorem c1209_range : LeafRange 1209  := by decide +kernel
private theorem c1209_ell   : LeafEll 1209    := by decide +kernel
private theorem c1209_nsq   : NSqChkSq 1209   := by decide +kernel
private theorem c1209_har   : HArithChkSq 1209 := by decide +kernel
private theorem c1209_r     : LeafR 1209      := by decide +kernel
private theorem c1209_e'    : LeafE' 1209     := by decide +kernel
private theorem c1209_f1    : LeafF1 1209     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1209_s2    : S2ChkSq 1209    := by decide +kernel
private theorem c1209_s3    : S3ChkSq 1209    := by decide +kernel
private theorem c1209_iso   : LeafIso 1209    := by decide +kernel
private theorem c1209_nof2  : NoF2ChkSq 1209  := by decide +kernel
private theorem c1209_nof3  : NoF3ChkSq 1209  := by decide +kernel
private theorem c1209_nof4z : NoF4zChkSq 1209 := by decide +kernel
theorem C'_1209 : C' 1209 :=
  ⟨c1209_sqf, c1209_range, c1209_ell, leafNSq_of_sq c1209_nsq, leafHAr_of_sq c1209_har,
   c1209_r, c1209_e', c1209_f1, leafS2_of_sq c1209_s2, leafS3_of_sq c1209_s3,
   c1209_iso, leafR8_of_sq c1209_nof2 c1209_nof3 c1209_nof4z⟩
theorem not_tile'_1209 (D : CongruentDissection 1209) : False :=
  not_tile_of_conditions' 1209 C'_1209 D

private theorem c1211_sqf   : LeafSqf 1211   := by decide +kernel
private theorem c1211_range : LeafRange 1211  := by decide +kernel
private theorem c1211_ell   : LeafEll 1211    := by decide +kernel
private theorem c1211_nsq   : NSqChkSq 1211   := by decide +kernel
private theorem c1211_har   : HArithChkSq 1211 := by decide +kernel
private theorem c1211_r     : LeafR 1211      := by decide +kernel
private theorem c1211_e'    : LeafE' 1211     := by decide +kernel
private theorem c1211_f1    : LeafF1 1211     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1211_s2    : S2ChkSq 1211    := by decide +kernel
private theorem c1211_s3    : S3ChkSq 1211    := by decide +kernel
private theorem c1211_iso   : LeafIso 1211    := by decide +kernel
private theorem c1211_nof2  : NoF2ChkSq 1211  := by decide +kernel
private theorem c1211_nof3  : NoF3ChkSq 1211  := by decide +kernel
private theorem c1211_nof4z : NoF4zChkSq 1211 := by decide +kernel
theorem C'_1211 : C' 1211 :=
  ⟨c1211_sqf, c1211_range, c1211_ell, leafNSq_of_sq c1211_nsq, leafHAr_of_sq c1211_har,
   c1211_r, c1211_e', c1211_f1, leafS2_of_sq c1211_s2, leafS3_of_sq c1211_s3,
   c1211_iso, leafR8_of_sq c1211_nof2 c1211_nof3 c1211_nof4z⟩
theorem not_tile'_1211 (D : CongruentDissection 1211) : False :=
  not_tile_of_conditions' 1211 C'_1211 D

private theorem c1227_sqf   : LeafSqf 1227   := by decide +kernel
private theorem c1227_range : LeafRange 1227  := by decide +kernel
private theorem c1227_ell   : LeafEll 1227    := by decide +kernel
private theorem c1227_nsq   : NSqChkSq 1227   := by decide +kernel
private theorem c1227_har   : HArithChkSq 1227 := by decide +kernel
private theorem c1227_r     : LeafR 1227      := by decide +kernel
private theorem c1227_e'    : LeafE' 1227     := by decide +kernel
private theorem c1227_f1    : LeafF1 1227     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1227_s2    : S2ChkSq 1227    := by decide +kernel
private theorem c1227_s3    : S3ChkSq 1227    := by decide +kernel
private theorem c1227_iso   : LeafIso 1227    := by decide +kernel
private theorem c1227_nof2  : NoF2ChkSq 1227  := by decide +kernel
private theorem c1227_nof3  : NoF3ChkSq 1227  := by decide +kernel
private theorem c1227_nof4z : NoF4zChkSq 1227 := by decide +kernel
theorem C'_1227 : C' 1227 :=
  ⟨c1227_sqf, c1227_range, c1227_ell, leafNSq_of_sq c1227_nsq, leafHAr_of_sq c1227_har,
   c1227_r, c1227_e', c1227_f1, leafS2_of_sq c1227_s2, leafS3_of_sq c1227_s3,
   c1227_iso, leafR8_of_sq c1227_nof2 c1227_nof3 c1227_nof4z⟩
theorem not_tile'_1227 (D : CongruentDissection 1227) : False :=
  not_tile_of_conditions' 1227 C'_1227 D

private theorem c1235_sqf   : LeafSqf 1235   := by decide +kernel
private theorem c1235_range : LeafRange 1235  := by decide +kernel
private theorem c1235_ell   : LeafEll 1235    := by decide +kernel
private theorem c1235_nsq   : NSqChkSq 1235   := by decide +kernel
private theorem c1235_har   : HArithChkSq 1235 := by decide +kernel
private theorem c1235_r     : LeafR 1235      := by decide +kernel
private theorem c1235_e'    : LeafE' 1235     := by decide +kernel
private theorem c1235_f1    : LeafF1 1235     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1235_s2    : S2ChkSq 1235    := by decide +kernel
private theorem c1235_s3    : S3ChkSq 1235    := by decide +kernel
private theorem c1235_iso   : LeafIso 1235    := by decide +kernel
private theorem c1235_nof2  : NoF2ChkSq 1235  := by decide +kernel
private theorem c1235_nof3  : NoF3ChkSq 1235  := by decide +kernel
private theorem c1235_nof4z : NoF4zChkSq 1235 := by decide +kernel
theorem C'_1235 : C' 1235 :=
  ⟨c1235_sqf, c1235_range, c1235_ell, leafNSq_of_sq c1235_nsq, leafHAr_of_sq c1235_har,
   c1235_r, c1235_e', c1235_f1, leafS2_of_sq c1235_s2, leafS3_of_sq c1235_s3,
   c1235_iso, leafR8_of_sq c1235_nof2 c1235_nof3 c1235_nof4z⟩
theorem not_tile'_1235 (D : CongruentDissection 1235) : False :=
  not_tile_of_conditions' 1235 C'_1235 D

private theorem c1243_sqf   : LeafSqf 1243   := by decide +kernel
private theorem c1243_range : LeafRange 1243  := by decide +kernel
private theorem c1243_ell   : LeafEll 1243    := by decide +kernel
private theorem c1243_nsq   : NSqChkSq 1243   := by decide +kernel
private theorem c1243_har   : HArithChkSq 1243 := by decide +kernel
private theorem c1243_r     : LeafR 1243      := by decide +kernel
private theorem c1243_e'    : LeafE' 1243     := by decide +kernel
private theorem c1243_f1    : LeafF1 1243     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1243_s2    : S2ChkSq 1243    := by decide +kernel
private theorem c1243_s3    : S3ChkSq 1243    := by decide +kernel
private theorem c1243_iso   : LeafIso 1243    := by decide +kernel
private theorem c1243_nof2  : NoF2ChkSq 1243  := by decide +kernel
private theorem c1243_nof3  : NoF3ChkSq 1243  := by decide +kernel
private theorem c1243_nof4z : NoF4zChkSq 1243 := by decide +kernel
theorem C'_1243 : C' 1243 :=
  ⟨c1243_sqf, c1243_range, c1243_ell, leafNSq_of_sq c1243_nsq, leafHAr_of_sq c1243_har,
   c1243_r, c1243_e', c1243_f1, leafS2_of_sq c1243_s2, leafS3_of_sq c1243_s3,
   c1243_iso, leafR8_of_sq c1243_nof2 c1243_nof3 c1243_nof4z⟩
theorem not_tile'_1243 (D : CongruentDissection 1243) : False :=
  not_tile_of_conditions' 1243 C'_1243 D

end Erdos634.Draft.AllN2

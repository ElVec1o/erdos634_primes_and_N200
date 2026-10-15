/- AllN2Check27: N = 1135, 1137, 1141, 1149, 1167
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1135_sqf   : LeafSqf 1135   := by decide +kernel
private theorem c1135_range : LeafRange 1135  := by decide +kernel
private theorem c1135_ell   : LeafEll 1135    := by decide +kernel
private theorem c1135_nsq   : NSqChkSq 1135   := by decide +kernel
private theorem c1135_har   : HArithChkSq 1135 := by decide +kernel
private theorem c1135_r     : LeafR 1135      := by decide +kernel
private theorem c1135_e'    : LeafE' 1135     := by decide +kernel
private theorem c1135_f1    : LeafF1 1135     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1135_s2    : S2ChkSq 1135    := by decide +kernel
private theorem c1135_s3    : S3ChkSq 1135    := by decide +kernel
private theorem c1135_iso   : LeafIso 1135    := by decide +kernel
private theorem c1135_nof2  : NoF2ChkSq 1135  := by decide +kernel
private theorem c1135_nof3  : NoF3ChkSq 1135  := by decide +kernel
private theorem c1135_nof4z : NoF4zChkSq 1135 := by decide +kernel
theorem C'_1135 : C' 1135 :=
  ⟨c1135_sqf, c1135_range, c1135_ell, leafNSq_of_sq c1135_nsq, leafHAr_of_sq c1135_har,
   c1135_r, c1135_e', c1135_f1, leafS2_of_sq c1135_s2, leafS3_of_sq c1135_s3,
   c1135_iso, leafR8_of_sq c1135_nof2 c1135_nof3 c1135_nof4z⟩
theorem not_tile'_1135 (D : CongruentDissection 1135) : False :=
  not_tile_of_conditions' 1135 C'_1135 D

private theorem c1137_sqf   : LeafSqf 1137   := by decide +kernel
private theorem c1137_range : LeafRange 1137  := by decide +kernel
private theorem c1137_ell   : LeafEll 1137    := by decide +kernel
private theorem c1137_nsq   : NSqChkSq 1137   := by decide +kernel
private theorem c1137_har   : HArithChkSq 1137 := by decide +kernel
private theorem c1137_r     : LeafR 1137      := by decide +kernel
private theorem c1137_e'    : LeafE' 1137     := by decide +kernel
private theorem c1137_f1    : LeafF1 1137     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1137_s2    : S2ChkSq 1137    := by decide +kernel
private theorem c1137_s3    : S3ChkSq 1137    := by decide +kernel
private theorem c1137_iso   : LeafIso 1137    := by decide +kernel
private theorem c1137_nof2  : NoF2ChkSq 1137  := by decide +kernel
private theorem c1137_nof3  : NoF3ChkSq 1137  := by decide +kernel
private theorem c1137_nof4z : NoF4zChkSq 1137 := by decide +kernel
theorem C'_1137 : C' 1137 :=
  ⟨c1137_sqf, c1137_range, c1137_ell, leafNSq_of_sq c1137_nsq, leafHAr_of_sq c1137_har,
   c1137_r, c1137_e', c1137_f1, leafS2_of_sq c1137_s2, leafS3_of_sq c1137_s3,
   c1137_iso, leafR8_of_sq c1137_nof2 c1137_nof3 c1137_nof4z⟩
theorem not_tile'_1137 (D : CongruentDissection 1137) : False :=
  not_tile_of_conditions' 1137 C'_1137 D

private theorem c1141_sqf   : LeafSqf 1141   := by decide +kernel
private theorem c1141_range : LeafRange 1141  := by decide +kernel
private theorem c1141_ell   : LeafEll 1141    := by decide +kernel
private theorem c1141_nsq   : NSqChkSq 1141   := by decide +kernel
private theorem c1141_har   : HArithChkSq 1141 := by decide +kernel
private theorem c1141_r     : LeafR 1141      := by decide +kernel
private theorem c1141_e'    : LeafE' 1141     := by decide +kernel
private theorem c1141_f1    : LeafF1 1141     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1141_s2    : S2ChkSq 1141    := by decide +kernel
private theorem c1141_s3    : S3ChkSq 1141    := by decide +kernel
private theorem c1141_iso   : LeafIso 1141    := by decide +kernel
private theorem c1141_nof2  : NoF2ChkSq 1141  := by decide +kernel
private theorem c1141_nof3  : NoF3ChkSq 1141  := by decide +kernel
private theorem c1141_nof4z : NoF4zChkSq 1141 := by decide +kernel
theorem C'_1141 : C' 1141 :=
  ⟨c1141_sqf, c1141_range, c1141_ell, leafNSq_of_sq c1141_nsq, leafHAr_of_sq c1141_har,
   c1141_r, c1141_e', c1141_f1, leafS2_of_sq c1141_s2, leafS3_of_sq c1141_s3,
   c1141_iso, leafR8_of_sq c1141_nof2 c1141_nof3 c1141_nof4z⟩
theorem not_tile'_1141 (D : CongruentDissection 1141) : False :=
  not_tile_of_conditions' 1141 C'_1141 D

private theorem c1149_sqf   : LeafSqf 1149   := by decide +kernel
private theorem c1149_range : LeafRange 1149  := by decide +kernel
private theorem c1149_ell   : LeafEll 1149    := by decide +kernel
private theorem c1149_nsq   : NSqChkSq 1149   := by decide +kernel
private theorem c1149_har   : HArithChkSq 1149 := by decide +kernel
private theorem c1149_r     : LeafR 1149      := by decide +kernel
private theorem c1149_e'    : LeafE' 1149     := by decide +kernel
private theorem c1149_f1    : LeafF1 1149     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1149_s2    : S2ChkSq 1149    := by decide +kernel
private theorem c1149_s3    : S3ChkSq 1149    := by decide +kernel
private theorem c1149_iso   : LeafIso 1149    := by decide +kernel
private theorem c1149_nof2  : NoF2ChkSq 1149  := by decide +kernel
private theorem c1149_nof3  : NoF3ChkSq 1149  := by decide +kernel
private theorem c1149_nof4z : NoF4zChkSq 1149 := by decide +kernel
theorem C'_1149 : C' 1149 :=
  ⟨c1149_sqf, c1149_range, c1149_ell, leafNSq_of_sq c1149_nsq, leafHAr_of_sq c1149_har,
   c1149_r, c1149_e', c1149_f1, leafS2_of_sq c1149_s2, leafS3_of_sq c1149_s3,
   c1149_iso, leafR8_of_sq c1149_nof2 c1149_nof3 c1149_nof4z⟩
theorem not_tile'_1149 (D : CongruentDissection 1149) : False :=
  not_tile_of_conditions' 1149 C'_1149 D

private theorem c1167_sqf   : LeafSqf 1167   := by decide +kernel
private theorem c1167_range : LeafRange 1167  := by decide +kernel
private theorem c1167_ell   : LeafEll 1167    := by decide +kernel
private theorem c1167_nsq   : NSqChkSq 1167   := by decide +kernel
private theorem c1167_har   : HArithChkSq 1167 := by decide +kernel
private theorem c1167_r     : LeafR 1167      := by decide +kernel
private theorem c1167_e'    : LeafE' 1167     := by decide +kernel
private theorem c1167_f1    : LeafF1 1167     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1167_s2    : S2ChkSq 1167    := by decide +kernel
private theorem c1167_s3    : S3ChkSq 1167    := by decide +kernel
private theorem c1167_iso   : LeafIso 1167    := by decide +kernel
private theorem c1167_nof2  : NoF2ChkSq 1167  := by decide +kernel
private theorem c1167_nof3  : NoF3ChkSq 1167  := by decide +kernel
private theorem c1167_nof4z : NoF4zChkSq 1167 := by decide +kernel
theorem C'_1167 : C' 1167 :=
  ⟨c1167_sqf, c1167_range, c1167_ell, leafNSq_of_sq c1167_nsq, leafHAr_of_sq c1167_har,
   c1167_r, c1167_e', c1167_f1, leafS2_of_sq c1167_s2, leafS3_of_sq c1167_s3,
   c1167_iso, leafR8_of_sq c1167_nof2 c1167_nof3 c1167_nof4z⟩
theorem not_tile'_1167 (D : CongruentDissection 1167) : False :=
  not_tile_of_conditions' 1167 C'_1167 D

end Erdos634.Draft.AllN2

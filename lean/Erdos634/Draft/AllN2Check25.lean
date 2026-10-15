/- AllN2Check25: N = 1059, 1077, 1085, 1099, 1101
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1059_sqf   : LeafSqf 1059   := by decide +kernel
private theorem c1059_range : LeafRange 1059  := by decide +kernel
private theorem c1059_ell   : LeafEll 1059    := by decide +kernel
private theorem c1059_nsq   : NSqChkSq 1059   := by decide +kernel
private theorem c1059_har   : HArithChkSq 1059 := by decide +kernel
private theorem c1059_r     : LeafR 1059      := by decide +kernel
private theorem c1059_e'    : LeafE' 1059     := by decide +kernel
private theorem c1059_f1    : LeafF1 1059     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1059_s2    : S2ChkSq 1059    := by decide +kernel
private theorem c1059_s3    : S3ChkSq 1059    := by decide +kernel
private theorem c1059_iso   : LeafIso 1059    := by decide +kernel
private theorem c1059_nof2  : NoF2ChkSq 1059  := by decide +kernel
private theorem c1059_nof3  : NoF3ChkSq 1059  := by decide +kernel
private theorem c1059_nof4z : NoF4zChkSq 1059 := by decide +kernel
theorem C'_1059 : C' 1059 :=
  ⟨c1059_sqf, c1059_range, c1059_ell, leafNSq_of_sq c1059_nsq, leafHAr_of_sq c1059_har,
   c1059_r, c1059_e', c1059_f1, leafS2_of_sq c1059_s2, leafS3_of_sq c1059_s3,
   c1059_iso, leafR8_of_sq c1059_nof2 c1059_nof3 c1059_nof4z⟩
theorem not_tile'_1059 (D : CongruentDissection 1059) : False :=
  not_tile_of_conditions' 1059 C'_1059 D

private theorem c1077_sqf   : LeafSqf 1077   := by decide +kernel
private theorem c1077_range : LeafRange 1077  := by decide +kernel
private theorem c1077_ell   : LeafEll 1077    := by decide +kernel
private theorem c1077_nsq   : NSqChkSq 1077   := by decide +kernel
private theorem c1077_har   : HArithChkSq 1077 := by decide +kernel
private theorem c1077_r     : LeafR 1077      := by decide +kernel
private theorem c1077_e'    : LeafE' 1077     := by decide +kernel
private theorem c1077_f1    : LeafF1 1077     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1077_s2    : S2ChkSq 1077    := by decide +kernel
private theorem c1077_s3    : S3ChkSq 1077    := by decide +kernel
private theorem c1077_iso   : LeafIso 1077    := by decide +kernel
private theorem c1077_nof2  : NoF2ChkSq 1077  := by decide +kernel
private theorem c1077_nof3  : NoF3ChkSq 1077  := by decide +kernel
private theorem c1077_nof4z : NoF4zChkSq 1077 := by decide +kernel
theorem C'_1077 : C' 1077 :=
  ⟨c1077_sqf, c1077_range, c1077_ell, leafNSq_of_sq c1077_nsq, leafHAr_of_sq c1077_har,
   c1077_r, c1077_e', c1077_f1, leafS2_of_sq c1077_s2, leafS3_of_sq c1077_s3,
   c1077_iso, leafR8_of_sq c1077_nof2 c1077_nof3 c1077_nof4z⟩
theorem not_tile'_1077 (D : CongruentDissection 1077) : False :=
  not_tile_of_conditions' 1077 C'_1077 D

private theorem c1085_sqf   : LeafSqf 1085   := by decide +kernel
private theorem c1085_range : LeafRange 1085  := by decide +kernel
private theorem c1085_ell   : LeafEll 1085    := by decide +kernel
private theorem c1085_nsq   : NSqChkSq 1085   := by decide +kernel
private theorem c1085_har   : HArithChkSq 1085 := by decide +kernel
private theorem c1085_r     : LeafR 1085      := by decide +kernel
private theorem c1085_e'    : LeafE' 1085     := by decide +kernel
private theorem c1085_f1    : LeafF1 1085     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1085_s2    : S2ChkSq 1085    := by decide +kernel
private theorem c1085_s3    : S3ChkSq 1085    := by decide +kernel
private theorem c1085_iso   : LeafIso 1085    := by decide +kernel
private theorem c1085_nof2  : NoF2ChkSq 1085  := by decide +kernel
private theorem c1085_nof3  : NoF3ChkSq 1085  := by decide +kernel
private theorem c1085_nof4z : NoF4zChkSq 1085 := by decide +kernel
theorem C'_1085 : C' 1085 :=
  ⟨c1085_sqf, c1085_range, c1085_ell, leafNSq_of_sq c1085_nsq, leafHAr_of_sq c1085_har,
   c1085_r, c1085_e', c1085_f1, leafS2_of_sq c1085_s2, leafS3_of_sq c1085_s3,
   c1085_iso, leafR8_of_sq c1085_nof2 c1085_nof3 c1085_nof4z⟩
theorem not_tile'_1085 (D : CongruentDissection 1085) : False :=
  not_tile_of_conditions' 1085 C'_1085 D

private theorem c1099_sqf   : LeafSqf 1099   := by decide +kernel
private theorem c1099_range : LeafRange 1099  := by decide +kernel
private theorem c1099_ell   : LeafEll 1099    := by decide +kernel
private theorem c1099_nsq   : NSqChkSq 1099   := by decide +kernel
private theorem c1099_har   : HArithChkSq 1099 := by decide +kernel
private theorem c1099_r     : LeafR 1099      := by decide +kernel
private theorem c1099_e'    : LeafE' 1099     := by decide +kernel
private theorem c1099_f1    : LeafF1 1099     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1099_s2    : S2ChkSq 1099    := by decide +kernel
private theorem c1099_s3    : S3ChkSq 1099    := by decide +kernel
private theorem c1099_iso   : LeafIso 1099    := by decide +kernel
private theorem c1099_nof2  : NoF2ChkSq 1099  := by decide +kernel
private theorem c1099_nof3  : NoF3ChkSq 1099  := by decide +kernel
private theorem c1099_nof4z : NoF4zChkSq 1099 := by decide +kernel
theorem C'_1099 : C' 1099 :=
  ⟨c1099_sqf, c1099_range, c1099_ell, leafNSq_of_sq c1099_nsq, leafHAr_of_sq c1099_har,
   c1099_r, c1099_e', c1099_f1, leafS2_of_sq c1099_s2, leafS3_of_sq c1099_s3,
   c1099_iso, leafR8_of_sq c1099_nof2 c1099_nof3 c1099_nof4z⟩
theorem not_tile'_1099 (D : CongruentDissection 1099) : False :=
  not_tile_of_conditions' 1099 C'_1099 D

private theorem c1101_sqf   : LeafSqf 1101   := by decide +kernel
private theorem c1101_range : LeafRange 1101  := by decide +kernel
private theorem c1101_ell   : LeafEll 1101    := by decide +kernel
private theorem c1101_nsq   : NSqChkSq 1101   := by decide +kernel
private theorem c1101_har   : HArithChkSq 1101 := by decide +kernel
private theorem c1101_r     : LeafR 1101      := by decide +kernel
private theorem c1101_e'    : LeafE' 1101     := by decide +kernel
private theorem c1101_f1    : LeafF1 1101     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1101_s2    : S2ChkSq 1101    := by decide +kernel
private theorem c1101_s3    : S3ChkSq 1101    := by decide +kernel
private theorem c1101_iso   : LeafIso 1101    := by decide +kernel
private theorem c1101_nof2  : NoF2ChkSq 1101  := by decide +kernel
private theorem c1101_nof3  : NoF3ChkSq 1101  := by decide +kernel
private theorem c1101_nof4z : NoF4zChkSq 1101 := by decide +kernel
theorem C'_1101 : C' 1101 :=
  ⟨c1101_sqf, c1101_range, c1101_ell, leafNSq_of_sq c1101_nsq, leafHAr_of_sq c1101_har,
   c1101_r, c1101_e', c1101_f1, leafS2_of_sq c1101_s2, leafS3_of_sq c1101_s3,
   c1101_iso, leafR8_of_sq c1101_nof2 c1101_nof3 c1101_nof4z⟩
theorem not_tile'_1101 (D : CongruentDissection 1101) : False :=
  not_tile_of_conditions' 1101 C'_1101 D

end Erdos634.Draft.AllN2

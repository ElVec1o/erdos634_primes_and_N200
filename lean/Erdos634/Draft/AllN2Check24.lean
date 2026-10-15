/- AllN2Check24: N = 1043, 1045, 1047, 1055, 1057
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1043_sqf   : LeafSqf 1043   := by decide +kernel
private theorem c1043_range : LeafRange 1043  := by decide +kernel
private theorem c1043_ell   : LeafEll 1043    := by decide +kernel
private theorem c1043_nsq   : NSqChkSq 1043   := by decide +kernel
private theorem c1043_har   : HArithChkSq 1043 := by decide +kernel
private theorem c1043_r     : LeafR 1043      := by decide +kernel
private theorem c1043_e'    : LeafE' 1043     := by decide +kernel
private theorem c1043_f1    : LeafF1 1043     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1043_s2    : S2ChkSq 1043    := by decide +kernel
private theorem c1043_s3    : S3ChkSq 1043    := by decide +kernel
private theorem c1043_iso   : LeafIso 1043    := by decide +kernel
private theorem c1043_nof2  : NoF2ChkSq 1043  := by decide +kernel
private theorem c1043_nof3  : NoF3ChkSq 1043  := by decide +kernel
private theorem c1043_nof4z : NoF4zChkSq 1043 := by decide +kernel
theorem C'_1043 : C' 1043 :=
  ⟨c1043_sqf, c1043_range, c1043_ell, leafNSq_of_sq c1043_nsq, leafHAr_of_sq c1043_har,
   c1043_r, c1043_e', c1043_f1, leafS2_of_sq c1043_s2, leafS3_of_sq c1043_s3,
   c1043_iso, leafR8_of_sq c1043_nof2 c1043_nof3 c1043_nof4z⟩
theorem not_tile'_1043 (D : CongruentDissection 1043) : False :=
  not_tile_of_conditions' 1043 C'_1043 D

private theorem c1045_sqf   : LeafSqf 1045   := by decide +kernel
private theorem c1045_range : LeafRange 1045  := by decide +kernel
private theorem c1045_ell   : LeafEll 1045    := by decide +kernel
private theorem c1045_nsq   : NSqChkSq 1045   := by decide +kernel
private theorem c1045_har   : HArithChkSq 1045 := by decide +kernel
private theorem c1045_r     : LeafR 1045      := by decide +kernel
private theorem c1045_e'    : LeafE' 1045     := by decide +kernel
private theorem c1045_f1    : LeafF1 1045     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1045_s2    : S2ChkSq 1045    := by decide +kernel
private theorem c1045_s3    : S3ChkSq 1045    := by decide +kernel
private theorem c1045_iso   : LeafIso 1045    := by decide +kernel
private theorem c1045_nof2  : NoF2ChkSq 1045  := by decide +kernel
private theorem c1045_nof3  : NoF3ChkSq 1045  := by decide +kernel
private theorem c1045_nof4z : NoF4zChkSq 1045 := by decide +kernel
theorem C'_1045 : C' 1045 :=
  ⟨c1045_sqf, c1045_range, c1045_ell, leafNSq_of_sq c1045_nsq, leafHAr_of_sq c1045_har,
   c1045_r, c1045_e', c1045_f1, leafS2_of_sq c1045_s2, leafS3_of_sq c1045_s3,
   c1045_iso, leafR8_of_sq c1045_nof2 c1045_nof3 c1045_nof4z⟩
theorem not_tile'_1045 (D : CongruentDissection 1045) : False :=
  not_tile_of_conditions' 1045 C'_1045 D

private theorem c1047_sqf   : LeafSqf 1047   := by decide +kernel
private theorem c1047_range : LeafRange 1047  := by decide +kernel
private theorem c1047_ell   : LeafEll 1047    := by decide +kernel
private theorem c1047_nsq   : NSqChkSq 1047   := by decide +kernel
private theorem c1047_har   : HArithChkSq 1047 := by decide +kernel
private theorem c1047_r     : LeafR 1047      := by decide +kernel
private theorem c1047_e'    : LeafE' 1047     := by decide +kernel
private theorem c1047_f1    : LeafF1 1047     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1047_s2    : S2ChkSq 1047    := by decide +kernel
private theorem c1047_s3    : S3ChkSq 1047    := by decide +kernel
private theorem c1047_iso   : LeafIso 1047    := by decide +kernel
private theorem c1047_nof2  : NoF2ChkSq 1047  := by decide +kernel
private theorem c1047_nof3  : NoF3ChkSq 1047  := by decide +kernel
private theorem c1047_nof4z : NoF4zChkSq 1047 := by decide +kernel
theorem C'_1047 : C' 1047 :=
  ⟨c1047_sqf, c1047_range, c1047_ell, leafNSq_of_sq c1047_nsq, leafHAr_of_sq c1047_har,
   c1047_r, c1047_e', c1047_f1, leafS2_of_sq c1047_s2, leafS3_of_sq c1047_s3,
   c1047_iso, leafR8_of_sq c1047_nof2 c1047_nof3 c1047_nof4z⟩
theorem not_tile'_1047 (D : CongruentDissection 1047) : False :=
  not_tile_of_conditions' 1047 C'_1047 D

private theorem c1055_sqf   : LeafSqf 1055   := by decide +kernel
private theorem c1055_range : LeafRange 1055  := by decide +kernel
private theorem c1055_ell   : LeafEll 1055    := by decide +kernel
private theorem c1055_nsq   : NSqChkSq 1055   := by decide +kernel
private theorem c1055_har   : HArithChkSq 1055 := by decide +kernel
private theorem c1055_r     : LeafR 1055      := by decide +kernel
private theorem c1055_e'    : LeafE' 1055     := by decide +kernel
private theorem c1055_f1    : LeafF1 1055     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1055_s2    : S2ChkSq 1055    := by decide +kernel
private theorem c1055_s3    : S3ChkSq 1055    := by decide +kernel
private theorem c1055_iso   : LeafIso 1055    := by decide +kernel
private theorem c1055_nof2  : NoF2ChkSq 1055  := by decide +kernel
private theorem c1055_nof3  : NoF3ChkSq 1055  := by decide +kernel
private theorem c1055_nof4z : NoF4zChkSq 1055 := by decide +kernel
theorem C'_1055 : C' 1055 :=
  ⟨c1055_sqf, c1055_range, c1055_ell, leafNSq_of_sq c1055_nsq, leafHAr_of_sq c1055_har,
   c1055_r, c1055_e', c1055_f1, leafS2_of_sq c1055_s2, leafS3_of_sq c1055_s3,
   c1055_iso, leafR8_of_sq c1055_nof2 c1055_nof3 c1055_nof4z⟩
theorem not_tile'_1055 (D : CongruentDissection 1055) : False :=
  not_tile_of_conditions' 1055 C'_1055 D

private theorem c1057_sqf   : LeafSqf 1057   := by decide +kernel
private theorem c1057_range : LeafRange 1057  := by decide +kernel
private theorem c1057_ell   : LeafEll 1057    := by decide +kernel
private theorem c1057_nsq   : NSqChkSq 1057   := by decide +kernel
private theorem c1057_har   : HArithChkSq 1057 := by decide +kernel
private theorem c1057_r     : LeafR 1057      := by decide +kernel
private theorem c1057_e'    : LeafE' 1057     := by decide +kernel
private theorem c1057_f1    : LeafF1 1057     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1057_s2    : S2ChkSq 1057    := by decide +kernel
private theorem c1057_s3    : S3ChkSq 1057    := by decide +kernel
private theorem c1057_iso   : LeafIso 1057    := by decide +kernel
private theorem c1057_nof2  : NoF2ChkSq 1057  := by decide +kernel
private theorem c1057_nof3  : NoF3ChkSq 1057  := by decide +kernel
private theorem c1057_nof4z : NoF4zChkSq 1057 := by decide +kernel
theorem C'_1057 : C' 1057 :=
  ⟨c1057_sqf, c1057_range, c1057_ell, leafNSq_of_sq c1057_nsq, leafHAr_of_sq c1057_har,
   c1057_r, c1057_e', c1057_f1, leafS2_of_sq c1057_s2, leafS3_of_sq c1057_s3,
   c1057_iso, leafR8_of_sq c1057_nof2 c1057_nof3 c1057_nof4z⟩
theorem not_tile'_1057 (D : CongruentDissection 1057) : False :=
  not_tile_of_conditions' 1057 C'_1057 D

end Erdos634.Draft.AllN2

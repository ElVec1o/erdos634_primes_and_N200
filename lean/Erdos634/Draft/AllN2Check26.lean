/- AllN2Check26: N = 1111, 1115, 1119, 1131, 1133
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1111_sqf   : LeafSqf 1111   := by decide +kernel
private theorem c1111_range : LeafRange 1111  := by decide +kernel
private theorem c1111_ell   : LeafEll 1111    := by decide +kernel
private theorem c1111_nsq   : NSqChkSq 1111   := by decide +kernel
private theorem c1111_har   : HArithChkSq 1111 := by decide +kernel
private theorem c1111_r     : LeafR 1111      := by decide +kernel
private theorem c1111_e'    : LeafE' 1111     := by decide +kernel
private theorem c1111_f1    : LeafF1 1111     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1111_s2    : S2ChkSq 1111    := by decide +kernel
private theorem c1111_s3    : S3ChkSq 1111    := by decide +kernel
private theorem c1111_iso   : LeafIso 1111    := by decide +kernel
private theorem c1111_nof2  : NoF2ChkSq 1111  := by decide +kernel
private theorem c1111_nof3  : NoF3ChkSq 1111  := by decide +kernel
private theorem c1111_nof4z : NoF4zChkSq 1111 := by decide +kernel
theorem C'_1111 : C' 1111 :=
  ⟨c1111_sqf, c1111_range, c1111_ell, leafNSq_of_sq c1111_nsq, leafHAr_of_sq c1111_har,
   c1111_r, c1111_e', c1111_f1, leafS2_of_sq c1111_s2, leafS3_of_sq c1111_s3,
   c1111_iso, leafR8_of_sq c1111_nof2 c1111_nof3 c1111_nof4z⟩
theorem not_tile'_1111 (D : CongruentDissection 1111) : False :=
  not_tile_of_conditions' 1111 C'_1111 D

private theorem c1115_sqf   : LeafSqf 1115   := by decide +kernel
private theorem c1115_range : LeafRange 1115  := by decide +kernel
private theorem c1115_ell   : LeafEll 1115    := by decide +kernel
private theorem c1115_nsq   : NSqChkSq 1115   := by decide +kernel
private theorem c1115_har   : HArithChkSq 1115 := by decide +kernel
private theorem c1115_r     : LeafR 1115      := by decide +kernel
private theorem c1115_e'    : LeafE' 1115     := by decide +kernel
private theorem c1115_f1    : LeafF1 1115     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1115_s2    : S2ChkSq 1115    := by decide +kernel
private theorem c1115_s3    : S3ChkSq 1115    := by decide +kernel
private theorem c1115_iso   : LeafIso 1115    := by decide +kernel
private theorem c1115_nof2  : NoF2ChkSq 1115  := by decide +kernel
private theorem c1115_nof3  : NoF3ChkSq 1115  := by decide +kernel
private theorem c1115_nof4z : NoF4zChkSq 1115 := by decide +kernel
theorem C'_1115 : C' 1115 :=
  ⟨c1115_sqf, c1115_range, c1115_ell, leafNSq_of_sq c1115_nsq, leafHAr_of_sq c1115_har,
   c1115_r, c1115_e', c1115_f1, leafS2_of_sq c1115_s2, leafS3_of_sq c1115_s3,
   c1115_iso, leafR8_of_sq c1115_nof2 c1115_nof3 c1115_nof4z⟩
theorem not_tile'_1115 (D : CongruentDissection 1115) : False :=
  not_tile_of_conditions' 1115 C'_1115 D

private theorem c1119_sqf   : LeafSqf 1119   := by decide +kernel
private theorem c1119_range : LeafRange 1119  := by decide +kernel
private theorem c1119_ell   : LeafEll 1119    := by decide +kernel
private theorem c1119_nsq   : NSqChkSq 1119   := by decide +kernel
private theorem c1119_har   : HArithChkSq 1119 := by decide +kernel
private theorem c1119_r     : LeafR 1119      := by decide +kernel
private theorem c1119_e'    : LeafE' 1119     := by decide +kernel
private theorem c1119_f1    : LeafF1 1119     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1119_s2    : S2ChkSq 1119    := by decide +kernel
private theorem c1119_s3    : S3ChkSq 1119    := by decide +kernel
private theorem c1119_iso   : LeafIso 1119    := by decide +kernel
private theorem c1119_nof2  : NoF2ChkSq 1119  := by decide +kernel
private theorem c1119_nof3  : NoF3ChkSq 1119  := by decide +kernel
private theorem c1119_nof4z : NoF4zChkSq 1119 := by decide +kernel
theorem C'_1119 : C' 1119 :=
  ⟨c1119_sqf, c1119_range, c1119_ell, leafNSq_of_sq c1119_nsq, leafHAr_of_sq c1119_har,
   c1119_r, c1119_e', c1119_f1, leafS2_of_sq c1119_s2, leafS3_of_sq c1119_s3,
   c1119_iso, leafR8_of_sq c1119_nof2 c1119_nof3 c1119_nof4z⟩
theorem not_tile'_1119 (D : CongruentDissection 1119) : False :=
  not_tile_of_conditions' 1119 C'_1119 D

private theorem c1131_sqf   : LeafSqf 1131   := by decide +kernel
private theorem c1131_range : LeafRange 1131  := by decide +kernel
private theorem c1131_ell   : LeafEll 1131    := by decide +kernel
private theorem c1131_nsq   : NSqChkSq 1131   := by decide +kernel
private theorem c1131_har   : HArithChkSq 1131 := by decide +kernel
private theorem c1131_r     : LeafR 1131      := by decide +kernel
private theorem c1131_e'    : LeafE' 1131     := by decide +kernel
private theorem c1131_f1    : LeafF1 1131     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1131_s2    : S2ChkSq 1131    := by decide +kernel
private theorem c1131_s3    : S3ChkSq 1131    := by decide +kernel
private theorem c1131_iso   : LeafIso 1131    := by decide +kernel
private theorem c1131_nof2  : NoF2ChkSq 1131  := by decide +kernel
private theorem c1131_nof3  : NoF3ChkSq 1131  := by decide +kernel
private theorem c1131_nof4z : NoF4zChkSq 1131 := by decide +kernel
theorem C'_1131 : C' 1131 :=
  ⟨c1131_sqf, c1131_range, c1131_ell, leafNSq_of_sq c1131_nsq, leafHAr_of_sq c1131_har,
   c1131_r, c1131_e', c1131_f1, leafS2_of_sq c1131_s2, leafS3_of_sq c1131_s3,
   c1131_iso, leafR8_of_sq c1131_nof2 c1131_nof3 c1131_nof4z⟩
theorem not_tile'_1131 (D : CongruentDissection 1131) : False :=
  not_tile_of_conditions' 1131 C'_1131 D

private theorem c1133_sqf   : LeafSqf 1133   := by decide +kernel
private theorem c1133_range : LeafRange 1133  := by decide +kernel
private theorem c1133_ell   : LeafEll 1133    := by decide +kernel
private theorem c1133_nsq   : NSqChkSq 1133   := by decide +kernel
private theorem c1133_har   : HArithChkSq 1133 := by decide +kernel
private theorem c1133_r     : LeafR 1133      := by decide +kernel
private theorem c1133_e'    : LeafE' 1133     := by decide +kernel
private theorem c1133_f1    : LeafF1 1133     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1133_s2    : S2ChkSq 1133    := by decide +kernel
private theorem c1133_s3    : S3ChkSq 1133    := by decide +kernel
private theorem c1133_iso   : LeafIso 1133    := by decide +kernel
private theorem c1133_nof2  : NoF2ChkSq 1133  := by decide +kernel
private theorem c1133_nof3  : NoF3ChkSq 1133  := by decide +kernel
private theorem c1133_nof4z : NoF4zChkSq 1133 := by decide +kernel
theorem C'_1133 : C' 1133 :=
  ⟨c1133_sqf, c1133_range, c1133_ell, leafNSq_of_sq c1133_nsq, leafHAr_of_sq c1133_har,
   c1133_r, c1133_e', c1133_f1, leafS2_of_sq c1133_s2, leafS3_of_sq c1133_s3,
   c1133_iso, leafR8_of_sq c1133_nof2 c1133_nof3 c1133_nof4z⟩
theorem not_tile'_1133 (D : CongruentDissection 1133) : False :=
  not_tile_of_conditions' 1133 C'_1133 D

end Erdos634.Draft.AllN2

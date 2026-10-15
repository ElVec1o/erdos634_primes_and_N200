/- AllN2Check47: N = 1857, 1883, 1887, 1893, 1895
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1857_sqf   : LeafSqf 1857   := by decide +kernel
private theorem c1857_range : LeafRange 1857  := by decide +kernel
private theorem c1857_ell   : LeafEll 1857    := by decide +kernel
private theorem c1857_nsq   : NSqChkSq 1857   := by decide +kernel
private theorem c1857_har   : HArithChkSq 1857 := by decide +kernel
private theorem c1857_r     : LeafR 1857      := by decide +kernel
private theorem c1857_e'    : LeafE' 1857     := by decide +kernel
private theorem c1857_f1    : LeafF1 1857     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1857_s2    : S2ChkSq 1857    := by decide +kernel
private theorem c1857_s3    : S3ChkSq 1857    := by decide +kernel
private theorem c1857_iso   : LeafIso 1857    := by decide +kernel
private theorem c1857_nof2  : NoF2ChkSq 1857  := by decide +kernel
private theorem c1857_nof3  : NoF3ChkSq 1857  := by decide +kernel
private theorem c1857_nof4z : NoF4zChkSq 1857 := by decide +kernel
theorem C'_1857 : C' 1857 :=
  ⟨c1857_sqf, c1857_range, c1857_ell, leafNSq_of_sq c1857_nsq, leafHAr_of_sq c1857_har,
   c1857_r, c1857_e', c1857_f1, leafS2_of_sq c1857_s2, leafS3_of_sq c1857_s3,
   c1857_iso, leafR8_of_sq c1857_nof2 c1857_nof3 c1857_nof4z⟩
theorem not_tile'_1857 (D : CongruentDissection 1857) : False :=
  not_tile_of_conditions' 1857 C'_1857 D

private theorem c1883_sqf   : LeafSqf 1883   := by decide +kernel
private theorem c1883_range : LeafRange 1883  := by decide +kernel
private theorem c1883_ell   : LeafEll 1883    := by decide +kernel
private theorem c1883_nsq   : NSqChkSq 1883   := by decide +kernel
private theorem c1883_har   : HArithChkSq 1883 := by decide +kernel
private theorem c1883_r     : LeafR 1883      := by decide +kernel
private theorem c1883_e'    : LeafE' 1883     := by decide +kernel
private theorem c1883_f1    : LeafF1 1883     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1883_s2    : S2ChkSq 1883    := by decide +kernel
private theorem c1883_s3    : S3ChkSq 1883    := by decide +kernel
private theorem c1883_iso   : LeafIso 1883    := by decide +kernel
private theorem c1883_nof2  : NoF2ChkSq 1883  := by decide +kernel
private theorem c1883_nof3  : NoF3ChkSq 1883  := by decide +kernel
private theorem c1883_nof4z : NoF4zChkSq 1883 := by decide +kernel
theorem C'_1883 : C' 1883 :=
  ⟨c1883_sqf, c1883_range, c1883_ell, leafNSq_of_sq c1883_nsq, leafHAr_of_sq c1883_har,
   c1883_r, c1883_e', c1883_f1, leafS2_of_sq c1883_s2, leafS3_of_sq c1883_s3,
   c1883_iso, leafR8_of_sq c1883_nof2 c1883_nof3 c1883_nof4z⟩
theorem not_tile'_1883 (D : CongruentDissection 1883) : False :=
  not_tile_of_conditions' 1883 C'_1883 D

private theorem c1887_sqf   : LeafSqf 1887   := by decide +kernel
private theorem c1887_range : LeafRange 1887  := by decide +kernel
private theorem c1887_ell   : LeafEll 1887    := by decide +kernel
private theorem c1887_nsq   : NSqChkSq 1887   := by decide +kernel
private theorem c1887_har   : HArithChkSq 1887 := by decide +kernel
private theorem c1887_r     : LeafR 1887      := by decide +kernel
private theorem c1887_e'    : LeafE' 1887     := by decide +kernel
private theorem c1887_f1    : LeafF1 1887     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1887_s2    : S2ChkSq 1887    := by decide +kernel
private theorem c1887_s3    : S3ChkSq 1887    := by decide +kernel
private theorem c1887_iso   : LeafIso 1887    := by decide +kernel
private theorem c1887_nof2  : NoF2ChkSq 1887  := by decide +kernel
private theorem c1887_nof3  : NoF3ChkSq 1887  := by decide +kernel
private theorem c1887_nof4z : NoF4zChkSq 1887 := by decide +kernel
theorem C'_1887 : C' 1887 :=
  ⟨c1887_sqf, c1887_range, c1887_ell, leafNSq_of_sq c1887_nsq, leafHAr_of_sq c1887_har,
   c1887_r, c1887_e', c1887_f1, leafS2_of_sq c1887_s2, leafS3_of_sq c1887_s3,
   c1887_iso, leafR8_of_sq c1887_nof2 c1887_nof3 c1887_nof4z⟩
theorem not_tile'_1887 (D : CongruentDissection 1887) : False :=
  not_tile_of_conditions' 1887 C'_1887 D

private theorem c1893_sqf   : LeafSqf 1893   := by decide +kernel
private theorem c1893_range : LeafRange 1893  := by decide +kernel
private theorem c1893_ell   : LeafEll 1893    := by decide +kernel
private theorem c1893_nsq   : NSqChkSq 1893   := by decide +kernel
private theorem c1893_har   : HArithChkSq 1893 := by decide +kernel
private theorem c1893_r     : LeafR 1893      := by decide +kernel
private theorem c1893_e'    : LeafE' 1893     := by decide +kernel
private theorem c1893_f1    : LeafF1 1893     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1893_s2    : S2ChkSq 1893    := by decide +kernel
private theorem c1893_s3    : S3ChkSq 1893    := by decide +kernel
private theorem c1893_iso   : LeafIso 1893    := by decide +kernel
private theorem c1893_nof2  : NoF2ChkSq 1893  := by decide +kernel
private theorem c1893_nof3  : NoF3ChkSq 1893  := by decide +kernel
private theorem c1893_nof4z : NoF4zChkSq 1893 := by decide +kernel
theorem C'_1893 : C' 1893 :=
  ⟨c1893_sqf, c1893_range, c1893_ell, leafNSq_of_sq c1893_nsq, leafHAr_of_sq c1893_har,
   c1893_r, c1893_e', c1893_f1, leafS2_of_sq c1893_s2, leafS3_of_sq c1893_s3,
   c1893_iso, leafR8_of_sq c1893_nof2 c1893_nof3 c1893_nof4z⟩
theorem not_tile'_1893 (D : CongruentDissection 1893) : False :=
  not_tile_of_conditions' 1893 C'_1893 D

private theorem c1895_sqf   : LeafSqf 1895   := by decide +kernel
private theorem c1895_range : LeafRange 1895  := by decide +kernel
private theorem c1895_ell   : LeafEll 1895    := by decide +kernel
private theorem c1895_nsq   : NSqChkSq 1895   := by decide +kernel
private theorem c1895_har   : HArithChkSq 1895 := by decide +kernel
private theorem c1895_r     : LeafR 1895      := by decide +kernel
private theorem c1895_e'    : LeafE' 1895     := by decide +kernel
private theorem c1895_f1    : LeafF1 1895     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1895_s2    : S2ChkSq 1895    := by decide +kernel
private theorem c1895_s3    : S3ChkSq 1895    := by decide +kernel
private theorem c1895_iso   : LeafIso 1895    := by decide +kernel
private theorem c1895_nof2  : NoF2ChkSq 1895  := by decide +kernel
private theorem c1895_nof3  : NoF3ChkSq 1895  := by decide +kernel
private theorem c1895_nof4z : NoF4zChkSq 1895 := by decide +kernel
theorem C'_1895 : C' 1895 :=
  ⟨c1895_sqf, c1895_range, c1895_ell, leafNSq_of_sq c1895_nsq, leafHAr_of_sq c1895_har,
   c1895_r, c1895_e', c1895_f1, leafS2_of_sq c1895_s2, leafS3_of_sq c1895_s3,
   c1895_iso, leafR8_of_sq c1895_nof2 c1895_nof3 c1895_nof4z⟩
theorem not_tile'_1895 (D : CongruentDissection 1895) : False :=
  not_tile_of_conditions' 1895 C'_1895 D

end Erdos634.Draft.AllN2

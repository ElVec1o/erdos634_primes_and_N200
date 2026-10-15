/- AllN2Check121: N = 2882, 2887, 2893, 2894, 2899
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2882_sqf   : LeafSqf 2882   := by decide +kernel
private theorem c2882_range : LeafRange 2882  := by decide +kernel
private theorem c2882_ell   : LeafEll 2882    := by decide +kernel
private theorem c2882_nsq   : NSqChkSq 2882   := by decide +kernel
private theorem c2882_har   : HArithChkSq 2882 := by decide +kernel
private theorem c2882_r     : LeafR 2882      := by decide +kernel
private theorem c2882_e'    : LeafE' 2882     := by decide +kernel
private theorem c2882_f1    : LeafF1 2882     := Or.inl (by decide)
private theorem c2882_s2    : S2ChkSq 2882    := by decide +kernel
private theorem c2882_s3    : S3ChkSq 2882    := by decide +kernel
private theorem c2882_iso   : LeafIso 2882    := by decide +kernel
private theorem c2882_nof2  : NoF2ChkSq 2882  := by decide +kernel
private theorem c2882_nof3  : NoF3ChkSq 2882  := by decide +kernel
private theorem c2882_nof4z : NoF4zChkSq 2882 := by decide +kernel
theorem C'_2882 : C' 2882 :=
  ⟨c2882_sqf, c2882_range, c2882_ell, leafNSq_of_sq c2882_nsq, leafHAr_of_sq c2882_har,
   c2882_r, c2882_e', c2882_f1, leafS2_of_sq c2882_s2, leafS3_of_sq c2882_s3,
   c2882_iso, leafR8_of_sq c2882_nof2 c2882_nof3 c2882_nof4z⟩
theorem not_tile'_2882 (D : CongruentDissection 2882) : False :=
  not_tile_of_conditions' 2882 C'_2882 D

private theorem c2887_sqf   : LeafSqf 2887   := by decide +kernel
private theorem c2887_range : LeafRange 2887  := by decide +kernel
private theorem c2887_ell   : LeafEll 2887    := by decide +kernel
private theorem c2887_nsq   : NSqChkSq 2887   := by decide +kernel
private theorem c2887_har   : HArithChkSq 2887 := by decide +kernel
private theorem c2887_r     : LeafR 2887      := by decide +kernel
private theorem c2887_e'    : LeafE' 2887     := by decide +kernel
private theorem c2887_f1    : LeafF1 2887     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2887_s2    : S2ChkSq 2887    := by decide +kernel
private theorem c2887_s3    : S3ChkSq 2887    := by decide +kernel
private theorem c2887_iso   : LeafIso 2887    := by decide +kernel
private theorem c2887_nof2  : NoF2ChkSq 2887  := by decide +kernel
private theorem c2887_nof3  : NoF3ChkSq 2887  := by decide +kernel
private theorem c2887_nof4z : NoF4zChkSq 2887 := by decide +kernel
theorem C'_2887 : C' 2887 :=
  ⟨c2887_sqf, c2887_range, c2887_ell, leafNSq_of_sq c2887_nsq, leafHAr_of_sq c2887_har,
   c2887_r, c2887_e', c2887_f1, leafS2_of_sq c2887_s2, leafS3_of_sq c2887_s3,
   c2887_iso, leafR8_of_sq c2887_nof2 c2887_nof3 c2887_nof4z⟩
theorem not_tile'_2887 (D : CongruentDissection 2887) : False :=
  not_tile_of_conditions' 2887 C'_2887 D

private theorem c2893_sqf   : LeafSqf 2893   := by decide +kernel
private theorem c2893_range : LeafRange 2893  := by decide +kernel
private theorem c2893_ell   : LeafEll 2893    := by decide +kernel
private theorem c2893_nsq   : NSqChkSq 2893   := by decide +kernel
private theorem c2893_har   : HArithChkSq 2893 := by decide +kernel
private theorem c2893_r     : LeafR 2893      := by decide +kernel
private theorem c2893_e'    : LeafE' 2893     := by decide +kernel
private theorem c2893_f1    : LeafF1 2893     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2893_s2    : S2ChkSq 2893    := by decide +kernel
private theorem c2893_s3    : S3ChkSq 2893    := by decide +kernel
private theorem c2893_iso   : LeafIso 2893    := by decide +kernel
private theorem c2893_nof2  : NoF2ChkSq 2893  := by decide +kernel
private theorem c2893_nof3  : NoF3ChkSq 2893  := by decide +kernel
private theorem c2893_nof4z : NoF4zChkSq 2893 := by decide +kernel
theorem C'_2893 : C' 2893 :=
  ⟨c2893_sqf, c2893_range, c2893_ell, leafNSq_of_sq c2893_nsq, leafHAr_of_sq c2893_har,
   c2893_r, c2893_e', c2893_f1, leafS2_of_sq c2893_s2, leafS3_of_sq c2893_s3,
   c2893_iso, leafR8_of_sq c2893_nof2 c2893_nof3 c2893_nof4z⟩
theorem not_tile'_2893 (D : CongruentDissection 2893) : False :=
  not_tile_of_conditions' 2893 C'_2893 D

private theorem c2894_sqf   : LeafSqf 2894   := by decide +kernel
private theorem c2894_range : LeafRange 2894  := by decide +kernel
private theorem c2894_ell   : LeafEll 2894    := by decide +kernel
private theorem c2894_nsq   : NSqChkSq 2894   := by decide +kernel
private theorem c2894_har   : HArithChkSq 2894 := by decide +kernel
private theorem c2894_r     : LeafR 2894      := by decide +kernel
private theorem c2894_e'    : LeafE' 2894     := by decide +kernel
private theorem c2894_f1    : LeafF1 2894     := Or.inl (by decide)
private theorem c2894_s2    : S2ChkSq 2894    := by decide +kernel
private theorem c2894_s3    : S3ChkSq 2894    := by decide +kernel
private theorem c2894_iso   : LeafIso 2894    := by decide +kernel
private theorem c2894_nof2  : NoF2ChkSq 2894  := by decide +kernel
private theorem c2894_nof3  : NoF3ChkSq 2894  := by decide +kernel
private theorem c2894_nof4z : NoF4zChkSq 2894 := by decide +kernel
theorem C'_2894 : C' 2894 :=
  ⟨c2894_sqf, c2894_range, c2894_ell, leafNSq_of_sq c2894_nsq, leafHAr_of_sq c2894_har,
   c2894_r, c2894_e', c2894_f1, leafS2_of_sq c2894_s2, leafS3_of_sq c2894_s3,
   c2894_iso, leafR8_of_sq c2894_nof2 c2894_nof3 c2894_nof4z⟩
theorem not_tile'_2894 (D : CongruentDissection 2894) : False :=
  not_tile_of_conditions' 2894 C'_2894 D

private theorem c2899_sqf   : LeafSqf 2899   := by decide +kernel
private theorem c2899_range : LeafRange 2899  := by decide +kernel
private theorem c2899_ell   : LeafEll 2899    := by decide +kernel
private theorem c2899_nsq   : NSqChkSq 2899   := by decide +kernel
private theorem c2899_har   : HArithChkSq 2899 := by decide +kernel
private theorem c2899_r     : LeafR 2899      := by decide +kernel
private theorem c2899_e'    : LeafE' 2899     := by decide +kernel
private theorem c2899_f1    : LeafF1 2899     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2899_s2    : S2ChkSq 2899    := by decide +kernel
private theorem c2899_s3    : S3ChkSq 2899    := by decide +kernel
private theorem c2899_iso   : LeafIso 2899    := by decide +kernel
private theorem c2899_nof2  : NoF2ChkSq 2899  := by decide +kernel
private theorem c2899_nof3  : NoF3ChkSq 2899  := by decide +kernel
private theorem c2899_nof4z : NoF4zChkSq 2899 := by decide +kernel
theorem C'_2899 : C' 2899 :=
  ⟨c2899_sqf, c2899_range, c2899_ell, leafNSq_of_sq c2899_nsq, leafHAr_of_sq c2899_har,
   c2899_r, c2899_e', c2899_f1, leafS2_of_sq c2899_s2, leafS3_of_sq c2899_s3,
   c2899_iso, leafR8_of_sq c2899_nof2 c2899_nof3 c2899_nof4z⟩
theorem not_tile'_2899 (D : CongruentDissection 2899) : False :=
  not_tile_of_conditions' 2899 C'_2899 D

end Erdos634.Draft.AllN2

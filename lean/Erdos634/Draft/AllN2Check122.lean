/- AllN2Check122: N = 2901, 2902, 2903, 2910, 2911
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2901_sqf   : LeafSqf 2901   := by decide +kernel
private theorem c2901_range : LeafRange 2901  := by decide +kernel
private theorem c2901_ell   : LeafEll 2901    := by decide +kernel
private theorem c2901_nsq   : NSqChkSq 2901   := by decide +kernel
private theorem c2901_har   : HArithChkSq 2901 := by decide +kernel
private theorem c2901_r     : LeafR 2901      := by decide +kernel
private theorem c2901_e'    : LeafE' 2901     := by decide +kernel
private theorem c2901_f1    : LeafF1 2901     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2901_s2    : S2ChkSq 2901    := by decide +kernel
private theorem c2901_s3    : S3ChkSq 2901    := by decide +kernel
private theorem c2901_iso   : LeafIso 2901    := by decide +kernel
private theorem c2901_nof2  : NoF2ChkSq 2901  := by decide +kernel
private theorem c2901_nof3  : NoF3ChkSq 2901  := by decide +kernel
private theorem c2901_nof4z : NoF4zChkSq 2901 := by decide +kernel
theorem C'_2901 : C' 2901 :=
  ⟨c2901_sqf, c2901_range, c2901_ell, leafNSq_of_sq c2901_nsq, leafHAr_of_sq c2901_har,
   c2901_r, c2901_e', c2901_f1, leafS2_of_sq c2901_s2, leafS3_of_sq c2901_s3,
   c2901_iso, leafR8_of_sq c2901_nof2 c2901_nof3 c2901_nof4z⟩
theorem not_tile'_2901 (D : CongruentDissection 2901) : False :=
  not_tile_of_conditions' 2901 C'_2901 D

private theorem c2902_sqf   : LeafSqf 2902   := by decide +kernel
private theorem c2902_range : LeafRange 2902  := by decide +kernel
private theorem c2902_ell   : LeafEll 2902    := by decide +kernel
private theorem c2902_nsq   : NSqChkSq 2902   := by decide +kernel
private theorem c2902_har   : HArithChkSq 2902 := by decide +kernel
private theorem c2902_r     : LeafR 2902      := by decide +kernel
private theorem c2902_e'    : LeafE' 2902     := by decide +kernel
private theorem c2902_f1    : LeafF1 2902     := Or.inl (by decide)
private theorem c2902_s2    : S2ChkSq 2902    := by decide +kernel
private theorem c2902_s3    : S3ChkSq 2902    := by decide +kernel
private theorem c2902_iso   : LeafIso 2902    := by decide +kernel
private theorem c2902_nof2  : NoF2ChkSq 2902  := by decide +kernel
private theorem c2902_nof3  : NoF3ChkSq 2902  := by decide +kernel
private theorem c2902_nof4z : NoF4zChkSq 2902 := by decide +kernel
theorem C'_2902 : C' 2902 :=
  ⟨c2902_sqf, c2902_range, c2902_ell, leafNSq_of_sq c2902_nsq, leafHAr_of_sq c2902_har,
   c2902_r, c2902_e', c2902_f1, leafS2_of_sq c2902_s2, leafS3_of_sq c2902_s3,
   c2902_iso, leafR8_of_sq c2902_nof2 c2902_nof3 c2902_nof4z⟩
theorem not_tile'_2902 (D : CongruentDissection 2902) : False :=
  not_tile_of_conditions' 2902 C'_2902 D

private theorem c2903_sqf   : LeafSqf 2903   := by decide +kernel
private theorem c2903_range : LeafRange 2903  := by decide +kernel
private theorem c2903_ell   : LeafEll 2903    := by decide +kernel
private theorem c2903_nsq   : NSqChkSq 2903   := by decide +kernel
private theorem c2903_har   : HArithChkSq 2903 := by decide +kernel
private theorem c2903_r     : LeafR 2903      := by decide +kernel
private theorem c2903_e'    : LeafE' 2903     := by decide +kernel
private theorem c2903_f1    : LeafF1 2903     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2903_s2    : S2ChkSq 2903    := by decide +kernel
private theorem c2903_s3    : S3ChkSq 2903    := by decide +kernel
private theorem c2903_iso   : LeafIso 2903    := by decide +kernel
private theorem c2903_nof2  : NoF2ChkSq 2903  := by decide +kernel
private theorem c2903_nof3  : NoF3ChkSq 2903  := by decide +kernel
private theorem c2903_nof4z : NoF4zChkSq 2903 := by decide +kernel
theorem C'_2903 : C' 2903 :=
  ⟨c2903_sqf, c2903_range, c2903_ell, leafNSq_of_sq c2903_nsq, leafHAr_of_sq c2903_har,
   c2903_r, c2903_e', c2903_f1, leafS2_of_sq c2903_s2, leafS3_of_sq c2903_s3,
   c2903_iso, leafR8_of_sq c2903_nof2 c2903_nof3 c2903_nof4z⟩
theorem not_tile'_2903 (D : CongruentDissection 2903) : False :=
  not_tile_of_conditions' 2903 C'_2903 D

private theorem c2910_sqf   : LeafSqf 2910   := by decide +kernel
private theorem c2910_range : LeafRange 2910  := by decide +kernel
private theorem c2910_ell   : LeafEll 2910    := by decide +kernel
private theorem c2910_nsq   : NSqChkSq 2910   := by decide +kernel
private theorem c2910_har   : HArithChkSq 2910 := by decide +kernel
private theorem c2910_r     : LeafR 2910      := by decide +kernel
private theorem c2910_e'    : LeafE' 2910     := by decide +kernel
private theorem c2910_f1    : LeafF1 2910     := Or.inl (by decide)
private theorem c2910_s2    : S2ChkSq 2910    := by decide +kernel
private theorem c2910_s3    : S3ChkSq 2910    := by decide +kernel
private theorem c2910_iso   : LeafIso 2910    := by decide +kernel
private theorem c2910_nof2  : NoF2ChkSq 2910  := by decide +kernel
private theorem c2910_nof3  : NoF3ChkSq 2910  := by decide +kernel
private theorem c2910_nof4z : NoF4zChkSq 2910 := by decide +kernel
theorem C'_2910 : C' 2910 :=
  ⟨c2910_sqf, c2910_range, c2910_ell, leafNSq_of_sq c2910_nsq, leafHAr_of_sq c2910_har,
   c2910_r, c2910_e', c2910_f1, leafS2_of_sq c2910_s2, leafS3_of_sq c2910_s3,
   c2910_iso, leafR8_of_sq c2910_nof2 c2910_nof3 c2910_nof4z⟩
theorem not_tile'_2910 (D : CongruentDissection 2910) : False :=
  not_tile_of_conditions' 2910 C'_2910 D

private theorem c2911_sqf   : LeafSqf 2911   := by decide +kernel
private theorem c2911_range : LeafRange 2911  := by decide +kernel
private theorem c2911_ell   : LeafEll 2911    := by decide +kernel
private theorem c2911_nsq   : NSqChkSq 2911   := by decide +kernel
private theorem c2911_har   : HArithChkSq 2911 := by decide +kernel
private theorem c2911_r     : LeafR 2911      := by decide +kernel
private theorem c2911_e'    : LeafE' 2911     := by decide +kernel
private theorem c2911_f1    : LeafF1 2911     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2911_s2    : S2ChkSq 2911    := by decide +kernel
private theorem c2911_s3    : S3ChkSq 2911    := by decide +kernel
private theorem c2911_iso   : LeafIso 2911    := by decide +kernel
private theorem c2911_nof2  : NoF2ChkSq 2911  := by decide +kernel
private theorem c2911_nof3  : NoF3ChkSq 2911  := by decide +kernel
private theorem c2911_nof4z : NoF4zChkSq 2911 := by decide +kernel
theorem C'_2911 : C' 2911 :=
  ⟨c2911_sqf, c2911_range, c2911_ell, leafNSq_of_sq c2911_nsq, leafHAr_of_sq c2911_har,
   c2911_r, c2911_e', c2911_f1, leafS2_of_sq c2911_s2, leafS3_of_sq c2911_s3,
   c2911_iso, leafR8_of_sq c2911_nof2 c2911_nof3 c2911_nof4z⟩
theorem not_tile'_2911 (D : CongruentDissection 2911) : False :=
  not_tile_of_conditions' 2911 C'_2911 D

end Erdos634.Draft.AllN2

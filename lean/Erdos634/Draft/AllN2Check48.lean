/- AllN2Check48: N = 1897, 1903, 1915, 1923, 1929
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1897_sqf   : LeafSqf 1897   := by decide +kernel
private theorem c1897_range : LeafRange 1897  := by decide +kernel
private theorem c1897_ell   : LeafEll 1897    := by decide +kernel
private theorem c1897_nsq   : NSqChkSq 1897   := by decide +kernel
private theorem c1897_har   : HArithChkSq 1897 := by decide +kernel
private theorem c1897_r     : LeafR 1897      := by decide +kernel
private theorem c1897_e'    : LeafE' 1897     := by decide +kernel
private theorem c1897_f1    : LeafF1 1897     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1897_s2    : S2ChkSq 1897    := by decide +kernel
private theorem c1897_s3    : S3ChkSq 1897    := by decide +kernel
private theorem c1897_iso   : LeafIso 1897    := by decide +kernel
private theorem c1897_nof2  : NoF2ChkSq 1897  := by decide +kernel
private theorem c1897_nof3  : NoF3ChkSq 1897  := by decide +kernel
private theorem c1897_nof4z : NoF4zChkSq 1897 := by decide +kernel
theorem C'_1897 : C' 1897 :=
  ⟨c1897_sqf, c1897_range, c1897_ell, leafNSq_of_sq c1897_nsq, leafHAr_of_sq c1897_har,
   c1897_r, c1897_e', c1897_f1, leafS2_of_sq c1897_s2, leafS3_of_sq c1897_s3,
   c1897_iso, leafR8_of_sq c1897_nof2 c1897_nof3 c1897_nof4z⟩
theorem not_tile'_1897 (D : CongruentDissection 1897) : False :=
  not_tile_of_conditions' 1897 C'_1897 D

private theorem c1903_sqf   : LeafSqf 1903   := by decide +kernel
private theorem c1903_range : LeafRange 1903  := by decide +kernel
private theorem c1903_ell   : LeafEll 1903    := by decide +kernel
private theorem c1903_nsq   : NSqChkSq 1903   := by decide +kernel
private theorem c1903_har   : HArithChkSq 1903 := by decide +kernel
private theorem c1903_r     : LeafR 1903      := by decide +kernel
private theorem c1903_e'    : LeafE' 1903     := by decide +kernel
private theorem c1903_f1    : LeafF1 1903     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1903_s2    : S2ChkSq 1903    := by decide +kernel
private theorem c1903_s3    : S3ChkSq 1903    := by decide +kernel
private theorem c1903_iso   : LeafIso 1903    := by decide +kernel
private theorem c1903_nof2  : NoF2ChkSq 1903  := by decide +kernel
private theorem c1903_nof3  : NoF3ChkSq 1903  := by decide +kernel
private theorem c1903_nof4z : NoF4zChkSq 1903 := by decide +kernel
theorem C'_1903 : C' 1903 :=
  ⟨c1903_sqf, c1903_range, c1903_ell, leafNSq_of_sq c1903_nsq, leafHAr_of_sq c1903_har,
   c1903_r, c1903_e', c1903_f1, leafS2_of_sq c1903_s2, leafS3_of_sq c1903_s3,
   c1903_iso, leafR8_of_sq c1903_nof2 c1903_nof3 c1903_nof4z⟩
theorem not_tile'_1903 (D : CongruentDissection 1903) : False :=
  not_tile_of_conditions' 1903 C'_1903 D

private theorem c1915_sqf   : LeafSqf 1915   := by decide +kernel
private theorem c1915_range : LeafRange 1915  := by decide +kernel
private theorem c1915_ell   : LeafEll 1915    := by decide +kernel
private theorem c1915_nsq   : NSqChkSq 1915   := by decide +kernel
private theorem c1915_har   : HArithChkSq 1915 := by decide +kernel
private theorem c1915_r     : LeafR 1915      := by decide +kernel
private theorem c1915_e'    : LeafE' 1915     := by decide +kernel
private theorem c1915_f1    : LeafF1 1915     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1915_s2    : S2ChkSq 1915    := by decide +kernel
private theorem c1915_s3    : S3ChkSq 1915    := by decide +kernel
private theorem c1915_iso   : LeafIso 1915    := by decide +kernel
private theorem c1915_nof2  : NoF2ChkSq 1915  := by decide +kernel
private theorem c1915_nof3  : NoF3ChkSq 1915  := by decide +kernel
private theorem c1915_nof4z : NoF4zChkSq 1915 := by decide +kernel
theorem C'_1915 : C' 1915 :=
  ⟨c1915_sqf, c1915_range, c1915_ell, leafNSq_of_sq c1915_nsq, leafHAr_of_sq c1915_har,
   c1915_r, c1915_e', c1915_f1, leafS2_of_sq c1915_s2, leafS3_of_sq c1915_s3,
   c1915_iso, leafR8_of_sq c1915_nof2 c1915_nof3 c1915_nof4z⟩
theorem not_tile'_1915 (D : CongruentDissection 1915) : False :=
  not_tile_of_conditions' 1915 C'_1915 D

private theorem c1923_sqf   : LeafSqf 1923   := by decide +kernel
private theorem c1923_range : LeafRange 1923  := by decide +kernel
private theorem c1923_ell   : LeafEll 1923    := by decide +kernel
private theorem c1923_nsq   : NSqChkSq 1923   := by decide +kernel
private theorem c1923_har   : HArithChkSq 1923 := by decide +kernel
private theorem c1923_r     : LeafR 1923      := by decide +kernel
private theorem c1923_e'    : LeafE' 1923     := by decide +kernel
private theorem c1923_f1    : LeafF1 1923     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1923_s2    : S2ChkSq 1923    := by decide +kernel
private theorem c1923_s3    : S3ChkSq 1923    := by decide +kernel
private theorem c1923_iso   : LeafIso 1923    := by decide +kernel
private theorem c1923_nof2  : NoF2ChkSq 1923  := by decide +kernel
private theorem c1923_nof3  : NoF3ChkSq 1923  := by decide +kernel
private theorem c1923_nof4z : NoF4zChkSq 1923 := by decide +kernel
theorem C'_1923 : C' 1923 :=
  ⟨c1923_sqf, c1923_range, c1923_ell, leafNSq_of_sq c1923_nsq, leafHAr_of_sq c1923_har,
   c1923_r, c1923_e', c1923_f1, leafS2_of_sq c1923_s2, leafS3_of_sq c1923_s3,
   c1923_iso, leafR8_of_sq c1923_nof2 c1923_nof3 c1923_nof4z⟩
theorem not_tile'_1923 (D : CongruentDissection 1923) : False :=
  not_tile_of_conditions' 1923 C'_1923 D

private theorem c1929_sqf   : LeafSqf 1929   := by decide +kernel
private theorem c1929_range : LeafRange 1929  := by decide +kernel
private theorem c1929_ell   : LeafEll 1929    := by decide +kernel
private theorem c1929_nsq   : NSqChkSq 1929   := by decide +kernel
private theorem c1929_har   : HArithChkSq 1929 := by decide +kernel
private theorem c1929_r     : LeafR 1929      := by decide +kernel
private theorem c1929_e'    : LeafE' 1929     := by decide +kernel
private theorem c1929_f1    : LeafF1 1929     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1929_s2    : S2ChkSq 1929    := by decide +kernel
private theorem c1929_s3    : S3ChkSq 1929    := by decide +kernel
private theorem c1929_iso   : LeafIso 1929    := by decide +kernel
private theorem c1929_nof2  : NoF2ChkSq 1929  := by decide +kernel
private theorem c1929_nof3  : NoF3ChkSq 1929  := by decide +kernel
private theorem c1929_nof4z : NoF4zChkSq 1929 := by decide +kernel
theorem C'_1929 : C' 1929 :=
  ⟨c1929_sqf, c1929_range, c1929_ell, leafNSq_of_sq c1929_nsq, leafHAr_of_sq c1929_har,
   c1929_r, c1929_e', c1929_f1, leafS2_of_sq c1929_s2, leafS3_of_sq c1929_s3,
   c1929_iso, leafR8_of_sq c1929_nof2 c1929_nof3 c1929_nof4z⟩
theorem not_tile'_1929 (D : CongruentDissection 1929) : False :=
  not_tile_of_conditions' 1929 C'_1929 D

end Erdos634.Draft.AllN2

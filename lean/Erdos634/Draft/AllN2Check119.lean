/- AllN2Check119: N = 2855, 2859, 2863, 2867, 2869
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2855_sqf   : LeafSqf 2855   := by decide +kernel
private theorem c2855_range : LeafRange 2855  := by decide +kernel
private theorem c2855_ell   : LeafEll 2855    := by decide +kernel
private theorem c2855_nsq   : NSqChkSq 2855   := by decide +kernel
private theorem c2855_har   : HArithChkSq 2855 := by decide +kernel
private theorem c2855_r     : LeafR 2855      := by decide +kernel
private theorem c2855_e'    : LeafE' 2855     := by decide +kernel
private theorem c2855_f1    : LeafF1 2855     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2855_s2    : S2ChkSq 2855    := by decide +kernel
private theorem c2855_s3    : S3ChkSq 2855    := by decide +kernel
private theorem c2855_iso   : LeafIso 2855    := by decide +kernel
private theorem c2855_nof2  : NoF2ChkSq 2855  := by decide +kernel
private theorem c2855_nof3  : NoF3ChkSq 2855  := by decide +kernel
private theorem c2855_nof4z : NoF4zChkSq 2855 := by decide +kernel
theorem C'_2855 : C' 2855 :=
  ⟨c2855_sqf, c2855_range, c2855_ell, leafNSq_of_sq c2855_nsq, leafHAr_of_sq c2855_har,
   c2855_r, c2855_e', c2855_f1, leafS2_of_sq c2855_s2, leafS3_of_sq c2855_s3,
   c2855_iso, leafR8_of_sq c2855_nof2 c2855_nof3 c2855_nof4z⟩
theorem not_tile'_2855 (D : CongruentDissection 2855) : False :=
  not_tile_of_conditions' 2855 C'_2855 D

private theorem c2859_sqf   : LeafSqf 2859   := by decide +kernel
private theorem c2859_range : LeafRange 2859  := by decide +kernel
private theorem c2859_ell   : LeafEll 2859    := by decide +kernel
private theorem c2859_nsq   : NSqChkSq 2859   := by decide +kernel
private theorem c2859_har   : HArithChkSq 2859 := by decide +kernel
private theorem c2859_r     : LeafR 2859      := by decide +kernel
private theorem c2859_e'    : LeafE' 2859     := by decide +kernel
private theorem c2859_f1    : LeafF1 2859     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2859_s2    : S2ChkSq 2859    := by decide +kernel
private theorem c2859_s3    : S3ChkSq 2859    := by decide +kernel
private theorem c2859_iso   : LeafIso 2859    := by decide +kernel
private theorem c2859_nof2  : NoF2ChkSq 2859  := by decide +kernel
private theorem c2859_nof3  : NoF3ChkSq 2859  := by decide +kernel
private theorem c2859_nof4z : NoF4zChkSq 2859 := by decide +kernel
theorem C'_2859 : C' 2859 :=
  ⟨c2859_sqf, c2859_range, c2859_ell, leafNSq_of_sq c2859_nsq, leafHAr_of_sq c2859_har,
   c2859_r, c2859_e', c2859_f1, leafS2_of_sq c2859_s2, leafS3_of_sq c2859_s3,
   c2859_iso, leafR8_of_sq c2859_nof2 c2859_nof3 c2859_nof4z⟩
theorem not_tile'_2859 (D : CongruentDissection 2859) : False :=
  not_tile_of_conditions' 2859 C'_2859 D

private theorem c2863_sqf   : LeafSqf 2863   := by decide +kernel
private theorem c2863_range : LeafRange 2863  := by decide +kernel
private theorem c2863_ell   : LeafEll 2863    := by decide +kernel
private theorem c2863_nsq   : NSqChkSq 2863   := by decide +kernel
private theorem c2863_har   : HArithChkSq 2863 := by decide +kernel
private theorem c2863_r     : LeafR 2863      := by decide +kernel
private theorem c2863_e'    : LeafE' 2863     := by decide +kernel
private theorem c2863_f1    : LeafF1 2863     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2863_s2    : S2ChkSq 2863    := by decide +kernel
private theorem c2863_s3    : S3ChkSq 2863    := by decide +kernel
private theorem c2863_iso   : LeafIso 2863    := by decide +kernel
private theorem c2863_nof2  : NoF2ChkSq 2863  := by decide +kernel
private theorem c2863_nof3  : NoF3ChkSq 2863  := by decide +kernel
private theorem c2863_nof4z : NoF4zChkSq 2863 := by decide +kernel
theorem C'_2863 : C' 2863 :=
  ⟨c2863_sqf, c2863_range, c2863_ell, leafNSq_of_sq c2863_nsq, leafHAr_of_sq c2863_har,
   c2863_r, c2863_e', c2863_f1, leafS2_of_sq c2863_s2, leafS3_of_sq c2863_s3,
   c2863_iso, leafR8_of_sq c2863_nof2 c2863_nof3 c2863_nof4z⟩
theorem not_tile'_2863 (D : CongruentDissection 2863) : False :=
  not_tile_of_conditions' 2863 C'_2863 D

private theorem c2867_sqf   : LeafSqf 2867   := by decide +kernel
private theorem c2867_range : LeafRange 2867  := by decide +kernel
private theorem c2867_ell   : LeafEll 2867    := by decide +kernel
private theorem c2867_nsq   : NSqChkSq 2867   := by decide +kernel
private theorem c2867_har   : HArithChkSq 2867 := by decide +kernel
private theorem c2867_r     : LeafR 2867      := by decide +kernel
private theorem c2867_e'    : LeafE' 2867     := by decide +kernel
private theorem c2867_f1    : LeafF1 2867     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2867_s2    : S2ChkSq 2867    := by decide +kernel
private theorem c2867_s3    : S3ChkSq 2867    := by decide +kernel
private theorem c2867_iso   : LeafIso 2867    := by decide +kernel
private theorem c2867_nof2  : NoF2ChkSq 2867  := by decide +kernel
private theorem c2867_nof3  : NoF3ChkSq 2867  := by decide +kernel
private theorem c2867_nof4z : NoF4zChkSq 2867 := by decide +kernel
theorem C'_2867 : C' 2867 :=
  ⟨c2867_sqf, c2867_range, c2867_ell, leafNSq_of_sq c2867_nsq, leafHAr_of_sq c2867_har,
   c2867_r, c2867_e', c2867_f1, leafS2_of_sq c2867_s2, leafS3_of_sq c2867_s3,
   c2867_iso, leafR8_of_sq c2867_nof2 c2867_nof3 c2867_nof4z⟩
theorem not_tile'_2867 (D : CongruentDissection 2867) : False :=
  not_tile_of_conditions' 2867 C'_2867 D

private theorem c2869_sqf   : LeafSqf 2869   := by decide +kernel
private theorem c2869_range : LeafRange 2869  := by decide +kernel
private theorem c2869_ell   : LeafEll 2869    := by decide +kernel
private theorem c2869_nsq   : NSqChkSq 2869   := by decide +kernel
private theorem c2869_har   : HArithChkSq 2869 := by decide +kernel
private theorem c2869_r     : LeafR 2869      := by decide +kernel
private theorem c2869_e'    : LeafE' 2869     := by decide +kernel
private theorem c2869_f1    : LeafF1 2869     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2869_s2    : S2ChkSq 2869    := by decide +kernel
private theorem c2869_s3    : S3ChkSq 2869    := by decide +kernel
private theorem c2869_iso   : LeafIso 2869    := by decide +kernel
private theorem c2869_nof2  : NoF2ChkSq 2869  := by decide +kernel
private theorem c2869_nof3  : NoF3ChkSq 2869  := by decide +kernel
private theorem c2869_nof4z : NoF4zChkSq 2869 := by decide +kernel
theorem C'_2869 : C' 2869 :=
  ⟨c2869_sqf, c2869_range, c2869_ell, leafNSq_of_sq c2869_nsq, leafHAr_of_sq c2869_har,
   c2869_r, c2869_e', c2869_f1, leafS2_of_sq c2869_s2, leafS3_of_sq c2869_s3,
   c2869_iso, leafR8_of_sq c2869_nof2 c2869_nof3 c2869_nof4z⟩
theorem not_tile'_2869 (D : CongruentDissection 2869) : False :=
  not_tile_of_conditions' 2869 C'_2869 D

end Erdos634.Draft.AllN2

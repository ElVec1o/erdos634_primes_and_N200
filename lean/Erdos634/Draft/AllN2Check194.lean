/- AllN2Check194: N = 3830, 3831, 3835, 3837, 3838
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3830_sqf   : LeafSqf 3830   := by decide +kernel
private theorem c3830_range : LeafRange 3830  := by decide +kernel
private theorem c3830_ell   : LeafEll 3830    := by decide +kernel
private theorem c3830_nsq   : NSqChkSq 3830   := by decide +kernel
private theorem c3830_har   : HArithChkSq 3830 := by decide +kernel
private theorem c3830_r     : LeafR 3830      := by decide +kernel
private theorem c3830_e'    : LeafE' 3830     := by decide +kernel
private theorem c3830_f1    : LeafF1 3830     := Or.inl (by decide)
private theorem c3830_s2    : S2ChkSq 3830    := by decide +kernel
private theorem c3830_s3    : S3ChkSq 3830    := by decide +kernel
private theorem c3830_iso   : LeafIso 3830    := by decide +kernel
private theorem c3830_nof2  : NoF2ChkSq 3830  := by decide +kernel
private theorem c3830_nof3  : NoF3ChkSq 3830  := by decide +kernel
private theorem c3830_nof4z : NoF4zChkSq 3830 := by decide +kernel
theorem C'_3830 : C' 3830 :=
  ⟨c3830_sqf, c3830_range, c3830_ell, leafNSq_of_sq c3830_nsq, leafHAr_of_sq c3830_har,
   c3830_r, c3830_e', c3830_f1, leafS2_of_sq c3830_s2, leafS3_of_sq c3830_s3,
   c3830_iso, leafR8_of_sq c3830_nof2 c3830_nof3 c3830_nof4z⟩
theorem not_tile'_3830 (D : CongruentDissection 3830) : False :=
  not_tile_of_conditions' 3830 C'_3830 D

private theorem c3831_sqf   : LeafSqf 3831   := by decide +kernel
private theorem c3831_range : LeafRange 3831  := by decide +kernel
private theorem c3831_ell   : LeafEll 3831    := by decide +kernel
private theorem c3831_nsq   : NSqChkSq 3831   := by decide +kernel
private theorem c3831_har   : HArithChkSq 3831 := by decide +kernel
private theorem c3831_r     : LeafR 3831      := by decide +kernel
private theorem c3831_e'    : LeafE' 3831     := by decide +kernel
private theorem c3831_f1    : LeafF1 3831     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3831_s2    : S2ChkSq 3831    := by decide +kernel
private theorem c3831_s3    : S3ChkSq 3831    := by decide +kernel
private theorem c3831_iso   : LeafIso 3831    := by decide +kernel
private theorem c3831_nof2  : NoF2ChkSq 3831  := by decide +kernel
private theorem c3831_nof3  : NoF3ChkSq 3831  := by decide +kernel
private theorem c3831_nof4z : NoF4zChkSq 3831 := by decide +kernel
theorem C'_3831 : C' 3831 :=
  ⟨c3831_sqf, c3831_range, c3831_ell, leafNSq_of_sq c3831_nsq, leafHAr_of_sq c3831_har,
   c3831_r, c3831_e', c3831_f1, leafS2_of_sq c3831_s2, leafS3_of_sq c3831_s3,
   c3831_iso, leafR8_of_sq c3831_nof2 c3831_nof3 c3831_nof4z⟩
theorem not_tile'_3831 (D : CongruentDissection 3831) : False :=
  not_tile_of_conditions' 3831 C'_3831 D

private theorem c3835_sqf   : LeafSqf 3835   := by decide +kernel
private theorem c3835_range : LeafRange 3835  := by decide +kernel
private theorem c3835_ell   : LeafEll 3835    := by decide +kernel
private theorem c3835_nsq   : NSqChkSq 3835   := by decide +kernel
private theorem c3835_har   : HArithChkSq 3835 := by decide +kernel
private theorem c3835_r     : LeafR 3835      := by decide +kernel
private theorem c3835_e'    : LeafE' 3835     := by decide +kernel
private theorem c3835_f1    : LeafF1 3835     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3835_s2    : S2ChkSq 3835    := by decide +kernel
private theorem c3835_s3    : S3ChkSq 3835    := by decide +kernel
private theorem c3835_iso   : LeafIso 3835    := by decide +kernel
private theorem c3835_nof2  : NoF2ChkSq 3835  := by decide +kernel
private theorem c3835_nof3  : NoF3ChkSq 3835  := by decide +kernel
private theorem c3835_nof4z : NoF4zChkSq 3835 := by decide +kernel
theorem C'_3835 : C' 3835 :=
  ⟨c3835_sqf, c3835_range, c3835_ell, leafNSq_of_sq c3835_nsq, leafHAr_of_sq c3835_har,
   c3835_r, c3835_e', c3835_f1, leafS2_of_sq c3835_s2, leafS3_of_sq c3835_s3,
   c3835_iso, leafR8_of_sq c3835_nof2 c3835_nof3 c3835_nof4z⟩
theorem not_tile'_3835 (D : CongruentDissection 3835) : False :=
  not_tile_of_conditions' 3835 C'_3835 D

private theorem c3837_sqf   : LeafSqf 3837   := by decide +kernel
private theorem c3837_range : LeafRange 3837  := by decide +kernel
private theorem c3837_ell   : LeafEll 3837    := by decide +kernel
private theorem c3837_nsq   : NSqChkSq 3837   := by decide +kernel
private theorem c3837_har   : HArithChkSq 3837 := by decide +kernel
private theorem c3837_r     : LeafR 3837      := by decide +kernel
private theorem c3837_e'    : LeafE' 3837     := by decide +kernel
private theorem c3837_f1    : LeafF1 3837     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3837_s2    : S2ChkSq 3837    := by decide +kernel
private theorem c3837_s3    : S3ChkSq 3837    := by decide +kernel
private theorem c3837_iso   : LeafIso 3837    := by decide +kernel
private theorem c3837_nof2  : NoF2ChkSq 3837  := by decide +kernel
private theorem c3837_nof3  : NoF3ChkSq 3837  := by decide +kernel
private theorem c3837_nof4z : NoF4zChkSq 3837 := by decide +kernel
theorem C'_3837 : C' 3837 :=
  ⟨c3837_sqf, c3837_range, c3837_ell, leafNSq_of_sq c3837_nsq, leafHAr_of_sq c3837_har,
   c3837_r, c3837_e', c3837_f1, leafS2_of_sq c3837_s2, leafS3_of_sq c3837_s3,
   c3837_iso, leafR8_of_sq c3837_nof2 c3837_nof3 c3837_nof4z⟩
theorem not_tile'_3837 (D : CongruentDissection 3837) : False :=
  not_tile_of_conditions' 3837 C'_3837 D

private theorem c3838_sqf   : LeafSqf 3838   := by decide +kernel
private theorem c3838_range : LeafRange 3838  := by decide +kernel
private theorem c3838_ell   : LeafEll 3838    := by decide +kernel
private theorem c3838_nsq   : NSqChkSq 3838   := by decide +kernel
private theorem c3838_har   : HArithChkSq 3838 := by decide +kernel
private theorem c3838_r     : LeafR 3838      := by decide +kernel
private theorem c3838_e'    : LeafE' 3838     := by decide +kernel
private theorem c3838_f1    : LeafF1 3838     := Or.inl (by decide)
private theorem c3838_s2    : S2ChkSq 3838    := by decide +kernel
private theorem c3838_s3    : S3ChkSq 3838    := by decide +kernel
private theorem c3838_iso   : LeafIso 3838    := by decide +kernel
private theorem c3838_nof2  : NoF2ChkSq 3838  := by decide +kernel
private theorem c3838_nof3  : NoF3ChkSq 3838  := by decide +kernel
private theorem c3838_nof4z : NoF4zChkSq 3838 := by decide +kernel
theorem C'_3838 : C' 3838 :=
  ⟨c3838_sqf, c3838_range, c3838_ell, leafNSq_of_sq c3838_nsq, leafHAr_of_sq c3838_har,
   c3838_r, c3838_e', c3838_f1, leafS2_of_sq c3838_s2, leafS3_of_sq c3838_s3,
   c3838_iso, leafR8_of_sq c3838_nof2 c3838_nof3 c3838_nof4z⟩
theorem not_tile'_3838 (D : CongruentDissection 3838) : False :=
  not_tile_of_conditions' 3838 C'_3838 D

end Erdos634.Draft.AllN2

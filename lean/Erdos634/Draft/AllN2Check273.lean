/- AllN2Check273: N = 4831, 4835, 4837, 4838, 4839
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4831_sqf   : LeafSqf 4831   := by decide +kernel
private theorem c4831_range : LeafRange 4831  := by decide +kernel
private theorem c4831_ell   : LeafEll 4831    := by decide +kernel
private theorem c4831_nsq   : NSqChkSq 4831   := by decide +kernel
private theorem c4831_har   : HArithChkSq 4831 := by decide +kernel
private theorem c4831_r     : LeafR 4831      := by decide +kernel
private theorem c4831_e'    : LeafE' 4831     := by decide +kernel
private theorem c4831_f1    : LeafF1 4831     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4831_s2    : S2ChkSq 4831    := by decide +kernel
private theorem c4831_s3    : S3ChkSq 4831    := by decide +kernel
private theorem c4831_iso   : LeafIso 4831    := by decide +kernel
private theorem c4831_nof2  : NoF2ChkSq 4831  := by decide +kernel
private theorem c4831_nof3  : NoF3ChkSq 4831  := by decide +kernel
private theorem c4831_nof4z : NoF4zChkSq 4831 := by decide +kernel
theorem C'_4831 : C' 4831 :=
  ⟨c4831_sqf, c4831_range, c4831_ell, leafNSq_of_sq c4831_nsq, leafHAr_of_sq c4831_har,
   c4831_r, c4831_e', c4831_f1, leafS2_of_sq c4831_s2, leafS3_of_sq c4831_s3,
   c4831_iso, leafR8_of_sq c4831_nof2 c4831_nof3 c4831_nof4z⟩
theorem not_tile'_4831 (D : CongruentDissection 4831) : False :=
  not_tile_of_conditions' 4831 C'_4831 D

private theorem c4835_sqf   : LeafSqf 4835   := by decide +kernel
private theorem c4835_range : LeafRange 4835  := by decide +kernel
private theorem c4835_ell   : LeafEll 4835    := by decide +kernel
private theorem c4835_nsq   : NSqChkSq 4835   := by decide +kernel
private theorem c4835_har   : HArithChkSq 4835 := by decide +kernel
private theorem c4835_r     : LeafR 4835      := by decide +kernel
private theorem c4835_e'    : LeafE' 4835     := by decide +kernel
private theorem c4835_f1    : LeafF1 4835     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4835_s2    : S2ChkSq 4835    := by decide +kernel
private theorem c4835_s3    : S3ChkSq 4835    := by decide +kernel
private theorem c4835_iso   : LeafIso 4835    := by decide +kernel
private theorem c4835_nof2  : NoF2ChkSq 4835  := by decide +kernel
private theorem c4835_nof3  : NoF3ChkSq 4835  := by decide +kernel
private theorem c4835_nof4z : NoF4zChkSq 4835 := by decide +kernel
theorem C'_4835 : C' 4835 :=
  ⟨c4835_sqf, c4835_range, c4835_ell, leafNSq_of_sq c4835_nsq, leafHAr_of_sq c4835_har,
   c4835_r, c4835_e', c4835_f1, leafS2_of_sq c4835_s2, leafS3_of_sq c4835_s3,
   c4835_iso, leafR8_of_sq c4835_nof2 c4835_nof3 c4835_nof4z⟩
theorem not_tile'_4835 (D : CongruentDissection 4835) : False :=
  not_tile_of_conditions' 4835 C'_4835 D

private theorem c4837_sqf   : LeafSqf 4837   := by decide +kernel
private theorem c4837_range : LeafRange 4837  := by decide +kernel
private theorem c4837_ell   : LeafEll 4837    := by decide +kernel
private theorem c4837_nsq   : NSqChkSq 4837   := by decide +kernel
private theorem c4837_har   : HArithChkSq 4837 := by decide +kernel
private theorem c4837_r     : LeafR 4837      := by decide +kernel
private theorem c4837_e'    : LeafE' 4837     := by decide +kernel
private theorem c4837_f1    : LeafF1 4837     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4837_s2    : S2ChkSq 4837    := by decide +kernel
private theorem c4837_s3    : S3ChkSq 4837    := by decide +kernel
private theorem c4837_iso   : LeafIso 4837    := by decide +kernel
private theorem c4837_nof2  : NoF2ChkSq 4837  := by decide +kernel
private theorem c4837_nof3  : NoF3ChkSq 4837  := by decide +kernel
private theorem c4837_nof4z : NoF4zChkSq 4837 := by decide +kernel
theorem C'_4837 : C' 4837 :=
  ⟨c4837_sqf, c4837_range, c4837_ell, leafNSq_of_sq c4837_nsq, leafHAr_of_sq c4837_har,
   c4837_r, c4837_e', c4837_f1, leafS2_of_sq c4837_s2, leafS3_of_sq c4837_s3,
   c4837_iso, leafR8_of_sq c4837_nof2 c4837_nof3 c4837_nof4z⟩
theorem not_tile'_4837 (D : CongruentDissection 4837) : False :=
  not_tile_of_conditions' 4837 C'_4837 D

private theorem c4838_sqf   : LeafSqf 4838   := by decide +kernel
private theorem c4838_range : LeafRange 4838  := by decide +kernel
private theorem c4838_ell   : LeafEll 4838    := by decide +kernel
private theorem c4838_nsq   : NSqChkSq 4838   := by decide +kernel
private theorem c4838_har   : HArithChkSq 4838 := by decide +kernel
private theorem c4838_r     : LeafR 4838      := by decide +kernel
private theorem c4838_e'    : LeafE' 4838     := by decide +kernel
private theorem c4838_f1    : LeafF1 4838     := Or.inl (by decide)
private theorem c4838_s2    : S2ChkSq 4838    := by decide +kernel
private theorem c4838_s3    : S3ChkSq 4838    := by decide +kernel
private theorem c4838_iso   : LeafIso 4838    := by decide +kernel
private theorem c4838_nof2  : NoF2ChkSq 4838  := by decide +kernel
private theorem c4838_nof3  : NoF3ChkSq 4838  := by decide +kernel
private theorem c4838_nof4z : NoF4zChkSq 4838 := by decide +kernel
theorem C'_4838 : C' 4838 :=
  ⟨c4838_sqf, c4838_range, c4838_ell, leafNSq_of_sq c4838_nsq, leafHAr_of_sq c4838_har,
   c4838_r, c4838_e', c4838_f1, leafS2_of_sq c4838_s2, leafS3_of_sq c4838_s3,
   c4838_iso, leafR8_of_sq c4838_nof2 c4838_nof3 c4838_nof4z⟩
theorem not_tile'_4838 (D : CongruentDissection 4838) : False :=
  not_tile_of_conditions' 4838 C'_4838 D

private theorem c4839_sqf   : LeafSqf 4839   := by decide +kernel
private theorem c4839_range : LeafRange 4839  := by decide +kernel
private theorem c4839_ell   : LeafEll 4839    := by decide +kernel
private theorem c4839_nsq   : NSqChkSq 4839   := by decide +kernel
private theorem c4839_har   : HArithChkSq 4839 := by decide +kernel
private theorem c4839_r     : LeafR 4839      := by decide +kernel
private theorem c4839_e'    : LeafE' 4839     := by decide +kernel
private theorem c4839_f1    : LeafF1 4839     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4839_s2    : S2ChkSq 4839    := by decide +kernel
private theorem c4839_s3    : S3ChkSq 4839    := by decide +kernel
private theorem c4839_iso   : LeafIso 4839    := by decide +kernel
private theorem c4839_nof2  : NoF2ChkSq 4839  := by decide +kernel
private theorem c4839_nof3  : NoF3ChkSq 4839  := by decide +kernel
private theorem c4839_nof4z : NoF4zChkSq 4839 := by decide +kernel
theorem C'_4839 : C' 4839 :=
  ⟨c4839_sqf, c4839_range, c4839_ell, leafNSq_of_sq c4839_nsq, leafHAr_of_sq c4839_har,
   c4839_r, c4839_e', c4839_f1, leafS2_of_sq c4839_s2, leafS3_of_sq c4839_s3,
   c4839_iso, leafR8_of_sq c4839_nof2 c4839_nof3 c4839_nof4z⟩
theorem not_tile'_4839 (D : CongruentDissection 4839) : False :=
  not_tile_of_conditions' 4839 C'_4839 D

end Erdos634.Draft.AllN2

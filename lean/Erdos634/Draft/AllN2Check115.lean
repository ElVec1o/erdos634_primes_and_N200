/- AllN2Check115: N = 2803, 2806, 2807, 2811, 2814
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2803_sqf   : LeafSqf 2803   := by decide +kernel
private theorem c2803_range : LeafRange 2803  := by decide +kernel
private theorem c2803_ell   : LeafEll 2803    := by decide +kernel
private theorem c2803_nsq   : NSqChkSq 2803   := by decide +kernel
private theorem c2803_har   : HArithChkSq 2803 := by decide +kernel
private theorem c2803_r     : LeafR 2803      := by decide +kernel
private theorem c2803_e'    : LeafE' 2803     := by decide +kernel
private theorem c2803_f1    : LeafF1 2803     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2803_s2    : S2ChkSq 2803    := by decide +kernel
private theorem c2803_s3    : S3ChkSq 2803    := by decide +kernel
private theorem c2803_iso   : LeafIso 2803    := by decide +kernel
private theorem c2803_nof2  : NoF2ChkSq 2803  := by decide +kernel
private theorem c2803_nof3  : NoF3ChkSq 2803  := by decide +kernel
private theorem c2803_nof4z : NoF4zChkSq 2803 := by decide +kernel
theorem C'_2803 : C' 2803 :=
  ⟨c2803_sqf, c2803_range, c2803_ell, leafNSq_of_sq c2803_nsq, leafHAr_of_sq c2803_har,
   c2803_r, c2803_e', c2803_f1, leafS2_of_sq c2803_s2, leafS3_of_sq c2803_s3,
   c2803_iso, leafR8_of_sq c2803_nof2 c2803_nof3 c2803_nof4z⟩
theorem not_tile'_2803 (D : CongruentDissection 2803) : False :=
  not_tile_of_conditions' 2803 C'_2803 D

private theorem c2806_sqf   : LeafSqf 2806   := by decide +kernel
private theorem c2806_range : LeafRange 2806  := by decide +kernel
private theorem c2806_ell   : LeafEll 2806    := by decide +kernel
private theorem c2806_nsq   : NSqChkSq 2806   := by decide +kernel
private theorem c2806_har   : HArithChkSq 2806 := by decide +kernel
private theorem c2806_r     : LeafR 2806      := by decide +kernel
private theorem c2806_e'    : LeafE' 2806     := by decide +kernel
private theorem c2806_f1    : LeafF1 2806     := Or.inl (by decide)
private theorem c2806_s2    : S2ChkSq 2806    := by decide +kernel
private theorem c2806_s3    : S3ChkSq 2806    := by decide +kernel
private theorem c2806_iso   : LeafIso 2806    := by decide +kernel
private theorem c2806_nof2  : NoF2ChkSq 2806  := by decide +kernel
private theorem c2806_nof3  : NoF3ChkSq 2806  := by decide +kernel
private theorem c2806_nof4z : NoF4zChkSq 2806 := by decide +kernel
theorem C'_2806 : C' 2806 :=
  ⟨c2806_sqf, c2806_range, c2806_ell, leafNSq_of_sq c2806_nsq, leafHAr_of_sq c2806_har,
   c2806_r, c2806_e', c2806_f1, leafS2_of_sq c2806_s2, leafS3_of_sq c2806_s3,
   c2806_iso, leafR8_of_sq c2806_nof2 c2806_nof3 c2806_nof4z⟩
theorem not_tile'_2806 (D : CongruentDissection 2806) : False :=
  not_tile_of_conditions' 2806 C'_2806 D

private theorem c2807_sqf   : LeafSqf 2807   := by decide +kernel
private theorem c2807_range : LeafRange 2807  := by decide +kernel
private theorem c2807_ell   : LeafEll 2807    := by decide +kernel
private theorem c2807_nsq   : NSqChkSq 2807   := by decide +kernel
private theorem c2807_har   : HArithChkSq 2807 := by decide +kernel
private theorem c2807_r     : LeafR 2807      := by decide +kernel
private theorem c2807_e'    : LeafE' 2807     := by decide +kernel
private theorem c2807_f1    : LeafF1 2807     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2807_s2    : S2ChkSq 2807    := by decide +kernel
private theorem c2807_s3    : S3ChkSq 2807    := by decide +kernel
private theorem c2807_iso   : LeafIso 2807    := by decide +kernel
private theorem c2807_nof2  : NoF2ChkSq 2807  := by decide +kernel
private theorem c2807_nof3  : NoF3ChkSq 2807  := by decide +kernel
private theorem c2807_nof4z : NoF4zChkSq 2807 := by decide +kernel
theorem C'_2807 : C' 2807 :=
  ⟨c2807_sqf, c2807_range, c2807_ell, leafNSq_of_sq c2807_nsq, leafHAr_of_sq c2807_har,
   c2807_r, c2807_e', c2807_f1, leafS2_of_sq c2807_s2, leafS3_of_sq c2807_s3,
   c2807_iso, leafR8_of_sq c2807_nof2 c2807_nof3 c2807_nof4z⟩
theorem not_tile'_2807 (D : CongruentDissection 2807) : False :=
  not_tile_of_conditions' 2807 C'_2807 D

private theorem c2811_sqf   : LeafSqf 2811   := by decide +kernel
private theorem c2811_range : LeafRange 2811  := by decide +kernel
private theorem c2811_ell   : LeafEll 2811    := by decide +kernel
private theorem c2811_nsq   : NSqChkSq 2811   := by decide +kernel
private theorem c2811_har   : HArithChkSq 2811 := by decide +kernel
private theorem c2811_r     : LeafR 2811      := by decide +kernel
private theorem c2811_e'    : LeafE' 2811     := by decide +kernel
private theorem c2811_f1    : LeafF1 2811     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2811_s2    : S2ChkSq 2811    := by decide +kernel
private theorem c2811_s3    : S3ChkSq 2811    := by decide +kernel
private theorem c2811_iso   : LeafIso 2811    := by decide +kernel
private theorem c2811_nof2  : NoF2ChkSq 2811  := by decide +kernel
private theorem c2811_nof3  : NoF3ChkSq 2811  := by decide +kernel
private theorem c2811_nof4z : NoF4zChkSq 2811 := by decide +kernel
theorem C'_2811 : C' 2811 :=
  ⟨c2811_sqf, c2811_range, c2811_ell, leafNSq_of_sq c2811_nsq, leafHAr_of_sq c2811_har,
   c2811_r, c2811_e', c2811_f1, leafS2_of_sq c2811_s2, leafS3_of_sq c2811_s3,
   c2811_iso, leafR8_of_sq c2811_nof2 c2811_nof3 c2811_nof4z⟩
theorem not_tile'_2811 (D : CongruentDissection 2811) : False :=
  not_tile_of_conditions' 2811 C'_2811 D

private theorem c2814_sqf   : LeafSqf 2814   := by decide +kernel
private theorem c2814_range : LeafRange 2814  := by decide +kernel
private theorem c2814_ell   : LeafEll 2814    := by decide +kernel
private theorem c2814_nsq   : NSqChkSq 2814   := by decide +kernel
private theorem c2814_har   : HArithChkSq 2814 := by decide +kernel
private theorem c2814_r     : LeafR 2814      := by decide +kernel
private theorem c2814_e'    : LeafE' 2814     := by decide +kernel
private theorem c2814_f1    : LeafF1 2814     := Or.inl (by decide)
private theorem c2814_s2    : S2ChkSq 2814    := by decide +kernel
private theorem c2814_s3    : S3ChkSq 2814    := by decide +kernel
private theorem c2814_iso   : LeafIso 2814    := by decide +kernel
private theorem c2814_nof2  : NoF2ChkSq 2814  := by decide +kernel
private theorem c2814_nof3  : NoF3ChkSq 2814  := by decide +kernel
private theorem c2814_nof4z : NoF4zChkSq 2814 := by decide +kernel
theorem C'_2814 : C' 2814 :=
  ⟨c2814_sqf, c2814_range, c2814_ell, leafNSq_of_sq c2814_nsq, leafHAr_of_sq c2814_har,
   c2814_r, c2814_e', c2814_f1, leafS2_of_sq c2814_s2, leafS3_of_sq c2814_s3,
   c2814_iso, leafR8_of_sq c2814_nof2 c2814_nof3 c2814_nof4z⟩
theorem not_tile'_2814 (D : CongruentDissection 2814) : False :=
  not_tile_of_conditions' 2814 C'_2814 D

end Erdos634.Draft.AllN2

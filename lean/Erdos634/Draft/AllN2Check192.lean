/- AllN2Check192: N = 3803, 3806, 3810, 3811, 3814
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3803_sqf   : LeafSqf 3803   := by decide +kernel
private theorem c3803_range : LeafRange 3803  := by decide +kernel
private theorem c3803_ell   : LeafEll 3803    := by decide +kernel
private theorem c3803_nsq   : NSqChkSq 3803   := by decide +kernel
private theorem c3803_har   : HArithChkSq 3803 := by decide +kernel
private theorem c3803_r     : LeafR 3803      := by decide +kernel
private theorem c3803_e'    : LeafE' 3803     := by decide +kernel
private theorem c3803_f1    : LeafF1 3803     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3803_s2    : S2ChkSq 3803    := by decide +kernel
private theorem c3803_s3    : S3ChkSq 3803    := by decide +kernel
private theorem c3803_iso   : LeafIso 3803    := by decide +kernel
private theorem c3803_nof2  : NoF2ChkSq 3803  := by decide +kernel
private theorem c3803_nof3  : NoF3ChkSq 3803  := by decide +kernel
private theorem c3803_nof4z : NoF4zChkSq 3803 := by decide +kernel
theorem C'_3803 : C' 3803 :=
  ⟨c3803_sqf, c3803_range, c3803_ell, leafNSq_of_sq c3803_nsq, leafHAr_of_sq c3803_har,
   c3803_r, c3803_e', c3803_f1, leafS2_of_sq c3803_s2, leafS3_of_sq c3803_s3,
   c3803_iso, leafR8_of_sq c3803_nof2 c3803_nof3 c3803_nof4z⟩
theorem not_tile'_3803 (D : CongruentDissection 3803) : False :=
  not_tile_of_conditions' 3803 C'_3803 D

private theorem c3806_sqf   : LeafSqf 3806   := by decide +kernel
private theorem c3806_range : LeafRange 3806  := by decide +kernel
private theorem c3806_ell   : LeafEll 3806    := by decide +kernel
private theorem c3806_nsq   : NSqChkSq 3806   := by decide +kernel
private theorem c3806_har   : HArithChkSq 3806 := by decide +kernel
private theorem c3806_r     : LeafR 3806      := by decide +kernel
private theorem c3806_e'    : LeafE' 3806     := by decide +kernel
private theorem c3806_f1    : LeafF1 3806     := Or.inl (by decide)
private theorem c3806_s2    : S2ChkSq 3806    := by decide +kernel
private theorem c3806_s3    : S3ChkSq 3806    := by decide +kernel
private theorem c3806_iso   : LeafIso 3806    := by decide +kernel
private theorem c3806_nof2  : NoF2ChkSq 3806  := by decide +kernel
private theorem c3806_nof3  : NoF3ChkSq 3806  := by decide +kernel
private theorem c3806_nof4z : NoF4zChkSq 3806 := by decide +kernel
theorem C'_3806 : C' 3806 :=
  ⟨c3806_sqf, c3806_range, c3806_ell, leafNSq_of_sq c3806_nsq, leafHAr_of_sq c3806_har,
   c3806_r, c3806_e', c3806_f1, leafS2_of_sq c3806_s2, leafS3_of_sq c3806_s3,
   c3806_iso, leafR8_of_sq c3806_nof2 c3806_nof3 c3806_nof4z⟩
theorem not_tile'_3806 (D : CongruentDissection 3806) : False :=
  not_tile_of_conditions' 3806 C'_3806 D

private theorem c3810_sqf   : LeafSqf 3810   := by decide +kernel
private theorem c3810_range : LeafRange 3810  := by decide +kernel
private theorem c3810_ell   : LeafEll 3810    := by decide +kernel
private theorem c3810_nsq   : NSqChkSq 3810   := by decide +kernel
private theorem c3810_har   : HArithChkSq 3810 := by decide +kernel
private theorem c3810_r     : LeafR 3810      := by decide +kernel
private theorem c3810_e'    : LeafE' 3810     := by decide +kernel
private theorem c3810_f1    : LeafF1 3810     := Or.inl (by decide)
private theorem c3810_s2    : S2ChkSq 3810    := by decide +kernel
private theorem c3810_s3    : S3ChkSq 3810    := by decide +kernel
private theorem c3810_iso   : LeafIso 3810    := by decide +kernel
private theorem c3810_nof2  : NoF2ChkSq 3810  := by decide +kernel
private theorem c3810_nof3  : NoF3ChkSq 3810  := by decide +kernel
private theorem c3810_nof4z : NoF4zChkSq 3810 := by decide +kernel
theorem C'_3810 : C' 3810 :=
  ⟨c3810_sqf, c3810_range, c3810_ell, leafNSq_of_sq c3810_nsq, leafHAr_of_sq c3810_har,
   c3810_r, c3810_e', c3810_f1, leafS2_of_sq c3810_s2, leafS3_of_sq c3810_s3,
   c3810_iso, leafR8_of_sq c3810_nof2 c3810_nof3 c3810_nof4z⟩
theorem not_tile'_3810 (D : CongruentDissection 3810) : False :=
  not_tile_of_conditions' 3810 C'_3810 D

private theorem c3811_sqf   : LeafSqf 3811   := by decide +kernel
private theorem c3811_range : LeafRange 3811  := by decide +kernel
private theorem c3811_ell   : LeafEll 3811    := by decide +kernel
private theorem c3811_nsq   : NSqChkSq 3811   := by decide +kernel
private theorem c3811_har   : HArithChkSq 3811 := by decide +kernel
private theorem c3811_r     : LeafR 3811      := by decide +kernel
private theorem c3811_e'    : LeafE' 3811     := by decide +kernel
private theorem c3811_f1    : LeafF1 3811     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3811_s2    : S2ChkSq 3811    := by decide +kernel
private theorem c3811_s3    : S3ChkSq 3811    := by decide +kernel
private theorem c3811_iso   : LeafIso 3811    := by decide +kernel
private theorem c3811_nof2  : NoF2ChkSq 3811  := by decide +kernel
private theorem c3811_nof3  : NoF3ChkSq 3811  := by decide +kernel
private theorem c3811_nof4z : NoF4zChkSq 3811 := by decide +kernel
theorem C'_3811 : C' 3811 :=
  ⟨c3811_sqf, c3811_range, c3811_ell, leafNSq_of_sq c3811_nsq, leafHAr_of_sq c3811_har,
   c3811_r, c3811_e', c3811_f1, leafS2_of_sq c3811_s2, leafS3_of_sq c3811_s3,
   c3811_iso, leafR8_of_sq c3811_nof2 c3811_nof3 c3811_nof4z⟩
theorem not_tile'_3811 (D : CongruentDissection 3811) : False :=
  not_tile_of_conditions' 3811 C'_3811 D

private theorem c3814_sqf   : LeafSqf 3814   := by decide +kernel
private theorem c3814_range : LeafRange 3814  := by decide +kernel
private theorem c3814_ell   : LeafEll 3814    := by decide +kernel
private theorem c3814_nsq   : NSqChkSq 3814   := by decide +kernel
private theorem c3814_har   : HArithChkSq 3814 := by decide +kernel
private theorem c3814_r     : LeafR 3814      := by decide +kernel
private theorem c3814_e'    : LeafE' 3814     := by decide +kernel
private theorem c3814_f1    : LeafF1 3814     := Or.inl (by decide)
private theorem c3814_s2    : S2ChkSq 3814    := by decide +kernel
private theorem c3814_s3    : S3ChkSq 3814    := by decide +kernel
private theorem c3814_iso   : LeafIso 3814    := by decide +kernel
private theorem c3814_nof2  : NoF2ChkSq 3814  := by decide +kernel
private theorem c3814_nof3  : NoF3ChkSq 3814  := by decide +kernel
private theorem c3814_nof4z : NoF4zChkSq 3814 := by decide +kernel
theorem C'_3814 : C' 3814 :=
  ⟨c3814_sqf, c3814_range, c3814_ell, leafNSq_of_sq c3814_nsq, leafHAr_of_sq c3814_har,
   c3814_r, c3814_e', c3814_f1, leafS2_of_sq c3814_s2, leafS3_of_sq c3814_s3,
   c3814_iso, leafR8_of_sq c3814_nof2 c3814_nof3 c3814_nof4z⟩
theorem not_tile'_3814 (D : CongruentDissection 3814) : False :=
  not_tile_of_conditions' 3814 C'_3814 D

end Erdos634.Draft.AllN2

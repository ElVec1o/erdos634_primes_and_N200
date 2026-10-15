/- AllN2Check117: N = 2827, 2830, 2831, 2839, 2841
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2827_sqf   : LeafSqf 2827   := by decide +kernel
private theorem c2827_range : LeafRange 2827  := by decide +kernel
private theorem c2827_ell   : LeafEll 2827    := by decide +kernel
private theorem c2827_nsq   : NSqChkSq 2827   := by decide +kernel
private theorem c2827_har   : HArithChkSq 2827 := by decide +kernel
private theorem c2827_r     : LeafR 2827      := by decide +kernel
private theorem c2827_e'    : LeafE' 2827     := by decide +kernel
private theorem c2827_f1    : LeafF1 2827     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2827_s2    : S2ChkSq 2827    := by decide +kernel
private theorem c2827_s3    : S3ChkSq 2827    := by decide +kernel
private theorem c2827_iso   : LeafIso 2827    := by decide +kernel
private theorem c2827_nof2  : NoF2ChkSq 2827  := by decide +kernel
private theorem c2827_nof3  : NoF3ChkSq 2827  := by decide +kernel
private theorem c2827_nof4z : NoF4zChkSq 2827 := by decide +kernel
theorem C'_2827 : C' 2827 :=
  ⟨c2827_sqf, c2827_range, c2827_ell, leafNSq_of_sq c2827_nsq, leafHAr_of_sq c2827_har,
   c2827_r, c2827_e', c2827_f1, leafS2_of_sq c2827_s2, leafS3_of_sq c2827_s3,
   c2827_iso, leafR8_of_sq c2827_nof2 c2827_nof3 c2827_nof4z⟩
theorem not_tile'_2827 (D : CongruentDissection 2827) : False :=
  not_tile_of_conditions' 2827 C'_2827 D

private theorem c2830_sqf   : LeafSqf 2830   := by decide +kernel
private theorem c2830_range : LeafRange 2830  := by decide +kernel
private theorem c2830_ell   : LeafEll 2830    := by decide +kernel
private theorem c2830_nsq   : NSqChkSq 2830   := by decide +kernel
private theorem c2830_har   : HArithChkSq 2830 := by decide +kernel
private theorem c2830_r     : LeafR 2830      := by decide +kernel
private theorem c2830_e'    : LeafE' 2830     := by decide +kernel
private theorem c2830_f1    : LeafF1 2830     := Or.inl (by decide)
private theorem c2830_s2    : S2ChkSq 2830    := by decide +kernel
private theorem c2830_s3    : S3ChkSq 2830    := by decide +kernel
private theorem c2830_iso   : LeafIso 2830    := by decide +kernel
private theorem c2830_nof2  : NoF2ChkSq 2830  := by decide +kernel
private theorem c2830_nof3  : NoF3ChkSq 2830  := by decide +kernel
private theorem c2830_nof4z : NoF4zChkSq 2830 := by decide +kernel
theorem C'_2830 : C' 2830 :=
  ⟨c2830_sqf, c2830_range, c2830_ell, leafNSq_of_sq c2830_nsq, leafHAr_of_sq c2830_har,
   c2830_r, c2830_e', c2830_f1, leafS2_of_sq c2830_s2, leafS3_of_sq c2830_s3,
   c2830_iso, leafR8_of_sq c2830_nof2 c2830_nof3 c2830_nof4z⟩
theorem not_tile'_2830 (D : CongruentDissection 2830) : False :=
  not_tile_of_conditions' 2830 C'_2830 D

private theorem c2831_sqf   : LeafSqf 2831   := by decide +kernel
private theorem c2831_range : LeafRange 2831  := by decide +kernel
private theorem c2831_ell   : LeafEll 2831    := by decide +kernel
private theorem c2831_nsq   : NSqChkSq 2831   := by decide +kernel
private theorem c2831_har   : HArithChkSq 2831 := by decide +kernel
private theorem c2831_r     : LeafR 2831      := by decide +kernel
private theorem c2831_e'    : LeafE' 2831     := by decide +kernel
private theorem c2831_f1    : LeafF1 2831     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2831_s2    : S2ChkSq 2831    := by decide +kernel
private theorem c2831_s3    : S3ChkSq 2831    := by decide +kernel
private theorem c2831_iso   : LeafIso 2831    := by decide +kernel
private theorem c2831_nof2  : NoF2ChkSq 2831  := by decide +kernel
private theorem c2831_nof3  : NoF3ChkSq 2831  := by decide +kernel
private theorem c2831_nof4z : NoF4zChkSq 2831 := by decide +kernel
theorem C'_2831 : C' 2831 :=
  ⟨c2831_sqf, c2831_range, c2831_ell, leafNSq_of_sq c2831_nsq, leafHAr_of_sq c2831_har,
   c2831_r, c2831_e', c2831_f1, leafS2_of_sq c2831_s2, leafS3_of_sq c2831_s3,
   c2831_iso, leafR8_of_sq c2831_nof2 c2831_nof3 c2831_nof4z⟩
theorem not_tile'_2831 (D : CongruentDissection 2831) : False :=
  not_tile_of_conditions' 2831 C'_2831 D

private theorem c2839_sqf   : LeafSqf 2839   := by decide +kernel
private theorem c2839_range : LeafRange 2839  := by decide +kernel
private theorem c2839_ell   : LeafEll 2839    := by decide +kernel
private theorem c2839_nsq   : NSqChkSq 2839   := by decide +kernel
private theorem c2839_har   : HArithChkSq 2839 := by decide +kernel
private theorem c2839_r     : LeafR 2839      := by decide +kernel
private theorem c2839_e'    : LeafE' 2839     := by decide +kernel
private theorem c2839_f1    : LeafF1 2839     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2839_s2    : S2ChkSq 2839    := by decide +kernel
private theorem c2839_s3    : S3ChkSq 2839    := by decide +kernel
private theorem c2839_iso   : LeafIso 2839    := by decide +kernel
private theorem c2839_nof2  : NoF2ChkSq 2839  := by decide +kernel
private theorem c2839_nof3  : NoF3ChkSq 2839  := by decide +kernel
private theorem c2839_nof4z : NoF4zChkSq 2839 := by decide +kernel
theorem C'_2839 : C' 2839 :=
  ⟨c2839_sqf, c2839_range, c2839_ell, leafNSq_of_sq c2839_nsq, leafHAr_of_sq c2839_har,
   c2839_r, c2839_e', c2839_f1, leafS2_of_sq c2839_s2, leafS3_of_sq c2839_s3,
   c2839_iso, leafR8_of_sq c2839_nof2 c2839_nof3 c2839_nof4z⟩
theorem not_tile'_2839 (D : CongruentDissection 2839) : False :=
  not_tile_of_conditions' 2839 C'_2839 D

private theorem c2841_sqf   : LeafSqf 2841   := by decide +kernel
private theorem c2841_range : LeafRange 2841  := by decide +kernel
private theorem c2841_ell   : LeafEll 2841    := by decide +kernel
private theorem c2841_nsq   : NSqChkSq 2841   := by decide +kernel
private theorem c2841_har   : HArithChkSq 2841 := by decide +kernel
private theorem c2841_r     : LeafR 2841      := by decide +kernel
private theorem c2841_e'    : LeafE' 2841     := by decide +kernel
private theorem c2841_f1    : LeafF1 2841     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2841_s2    : S2ChkSq 2841    := by decide +kernel
private theorem c2841_s3    : S3ChkSq 2841    := by decide +kernel
private theorem c2841_iso   : LeafIso 2841    := by decide +kernel
private theorem c2841_nof2  : NoF2ChkSq 2841  := by decide +kernel
private theorem c2841_nof3  : NoF3ChkSq 2841  := by decide +kernel
private theorem c2841_nof4z : NoF4zChkSq 2841 := by decide +kernel
theorem C'_2841 : C' 2841 :=
  ⟨c2841_sqf, c2841_range, c2841_ell, leafNSq_of_sq c2841_nsq, leafHAr_of_sq c2841_har,
   c2841_r, c2841_e', c2841_f1, leafS2_of_sq c2841_s2, leafS3_of_sq c2841_s3,
   c2841_iso, leafR8_of_sq c2841_nof2 c2841_nof3 c2841_nof4z⟩
theorem not_tile'_2841 (D : CongruentDissection 2841) : False :=
  not_tile_of_conditions' 2841 C'_2841 D

end Erdos634.Draft.AllN2

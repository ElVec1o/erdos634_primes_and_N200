/- AllN2Check271: N = 4811, 4814, 4818, 4819, 4821
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4811_sqf   : LeafSqf 4811   := by decide +kernel
private theorem c4811_range : LeafRange 4811  := by decide +kernel
private theorem c4811_ell   : LeafEll 4811    := by decide +kernel
private theorem c4811_nsq   : NSqChkSq 4811   := by decide +kernel
private theorem c4811_har   : HArithChkSq 4811 := by decide +kernel
private theorem c4811_r     : LeafR 4811      := by decide +kernel
private theorem c4811_e'    : LeafE' 4811     := by decide +kernel
private theorem c4811_f1    : LeafF1 4811     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4811_s2    : S2ChkSq 4811    := by decide +kernel
private theorem c4811_s3    : S3ChkSq 4811    := by decide +kernel
private theorem c4811_iso   : LeafIso 4811    := by decide +kernel
private theorem c4811_nof2  : NoF2ChkSq 4811  := by decide +kernel
private theorem c4811_nof3  : NoF3ChkSq 4811  := by decide +kernel
private theorem c4811_nof4z : NoF4zChkSq 4811 := by decide +kernel
theorem C'_4811 : C' 4811 :=
  ⟨c4811_sqf, c4811_range, c4811_ell, leafNSq_of_sq c4811_nsq, leafHAr_of_sq c4811_har,
   c4811_r, c4811_e', c4811_f1, leafS2_of_sq c4811_s2, leafS3_of_sq c4811_s3,
   c4811_iso, leafR8_of_sq c4811_nof2 c4811_nof3 c4811_nof4z⟩
theorem not_tile'_4811 (D : CongruentDissection 4811) : False :=
  not_tile_of_conditions' 4811 C'_4811 D

private theorem c4814_sqf   : LeafSqf 4814   := by decide +kernel
private theorem c4814_range : LeafRange 4814  := by decide +kernel
private theorem c4814_ell   : LeafEll 4814    := by decide +kernel
private theorem c4814_nsq   : NSqChkSq 4814   := by decide +kernel
private theorem c4814_har   : HArithChkSq 4814 := by decide +kernel
private theorem c4814_r     : LeafR 4814      := by decide +kernel
private theorem c4814_e'    : LeafE' 4814     := by decide +kernel
private theorem c4814_f1    : LeafF1 4814     := Or.inl (by decide)
private theorem c4814_s2    : S2ChkSq 4814    := by decide +kernel
private theorem c4814_s3    : S3ChkSq 4814    := by decide +kernel
private theorem c4814_iso   : LeafIso 4814    := by decide +kernel
private theorem c4814_nof2  : NoF2ChkSq 4814  := by decide +kernel
private theorem c4814_nof3  : NoF3ChkSq 4814  := by decide +kernel
private theorem c4814_nof4z : NoF4zChkSq 4814 := by decide +kernel
theorem C'_4814 : C' 4814 :=
  ⟨c4814_sqf, c4814_range, c4814_ell, leafNSq_of_sq c4814_nsq, leafHAr_of_sq c4814_har,
   c4814_r, c4814_e', c4814_f1, leafS2_of_sq c4814_s2, leafS3_of_sq c4814_s3,
   c4814_iso, leafR8_of_sq c4814_nof2 c4814_nof3 c4814_nof4z⟩
theorem not_tile'_4814 (D : CongruentDissection 4814) : False :=
  not_tile_of_conditions' 4814 C'_4814 D

private theorem c4818_sqf   : LeafSqf 4818   := by decide +kernel
private theorem c4818_range : LeafRange 4818  := by decide +kernel
private theorem c4818_ell   : LeafEll 4818    := by decide +kernel
private theorem c4818_nsq   : NSqChkSq 4818   := by decide +kernel
private theorem c4818_har   : HArithChkSq 4818 := by decide +kernel
private theorem c4818_r     : LeafR 4818      := by decide +kernel
private theorem c4818_e'    : LeafE' 4818     := by decide +kernel
private theorem c4818_f1    : LeafF1 4818     := Or.inl (by decide)
private theorem c4818_s2    : S2ChkSq 4818    := by decide +kernel
private theorem c4818_s3    : S3ChkSq 4818    := by decide +kernel
private theorem c4818_iso   : LeafIso 4818    := by decide +kernel
private theorem c4818_nof2  : NoF2ChkSq 4818  := by decide +kernel
private theorem c4818_nof3  : NoF3ChkSq 4818  := by decide +kernel
private theorem c4818_nof4z : NoF4zChkSq 4818 := by decide +kernel
theorem C'_4818 : C' 4818 :=
  ⟨c4818_sqf, c4818_range, c4818_ell, leafNSq_of_sq c4818_nsq, leafHAr_of_sq c4818_har,
   c4818_r, c4818_e', c4818_f1, leafS2_of_sq c4818_s2, leafS3_of_sq c4818_s3,
   c4818_iso, leafR8_of_sq c4818_nof2 c4818_nof3 c4818_nof4z⟩
theorem not_tile'_4818 (D : CongruentDissection 4818) : False :=
  not_tile_of_conditions' 4818 C'_4818 D

private theorem c4819_sqf   : LeafSqf 4819   := by decide +kernel
private theorem c4819_range : LeafRange 4819  := by decide +kernel
private theorem c4819_ell   : LeafEll 4819    := by decide +kernel
private theorem c4819_nsq   : NSqChkSq 4819   := by decide +kernel
private theorem c4819_har   : HArithChkSq 4819 := by decide +kernel
private theorem c4819_r     : LeafR 4819      := by decide +kernel
private theorem c4819_e'    : LeafE' 4819     := by decide +kernel
private theorem c4819_f1    : LeafF1 4819     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4819_s2    : S2ChkSq 4819    := by decide +kernel
private theorem c4819_s3    : S3ChkSq 4819    := by decide +kernel
private theorem c4819_iso   : LeafIso 4819    := by decide +kernel
private theorem c4819_nof2  : NoF2ChkSq 4819  := by decide +kernel
private theorem c4819_nof3  : NoF3ChkSq 4819  := by decide +kernel
private theorem c4819_nof4z : NoF4zChkSq 4819 := by decide +kernel
theorem C'_4819 : C' 4819 :=
  ⟨c4819_sqf, c4819_range, c4819_ell, leafNSq_of_sq c4819_nsq, leafHAr_of_sq c4819_har,
   c4819_r, c4819_e', c4819_f1, leafS2_of_sq c4819_s2, leafS3_of_sq c4819_s3,
   c4819_iso, leafR8_of_sq c4819_nof2 c4819_nof3 c4819_nof4z⟩
theorem not_tile'_4819 (D : CongruentDissection 4819) : False :=
  not_tile_of_conditions' 4819 C'_4819 D

private theorem c4821_sqf   : LeafSqf 4821   := by decide +kernel
private theorem c4821_range : LeafRange 4821  := by decide +kernel
private theorem c4821_ell   : LeafEll 4821    := by decide +kernel
private theorem c4821_nsq   : NSqChkSq 4821   := by decide +kernel
private theorem c4821_har   : HArithChkSq 4821 := by decide +kernel
private theorem c4821_r     : LeafR 4821      := by decide +kernel
private theorem c4821_e'    : LeafE' 4821     := by decide +kernel
private theorem c4821_f1    : LeafF1 4821     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4821_s2    : S2ChkSq 4821    := by decide +kernel
private theorem c4821_s3    : S3ChkSq 4821    := by decide +kernel
private theorem c4821_iso   : LeafIso 4821    := by decide +kernel
private theorem c4821_nof2  : NoF2ChkSq 4821  := by decide +kernel
private theorem c4821_nof3  : NoF3ChkSq 4821  := by decide +kernel
private theorem c4821_nof4z : NoF4zChkSq 4821 := by decide +kernel
theorem C'_4821 : C' 4821 :=
  ⟨c4821_sqf, c4821_range, c4821_ell, leafNSq_of_sq c4821_nsq, leafHAr_of_sq c4821_har,
   c4821_r, c4821_e', c4821_f1, leafS2_of_sq c4821_s2, leafS3_of_sq c4821_s3,
   c4821_iso, leafR8_of_sq c4821_nof2 c4821_nof3 c4821_nof4z⟩
theorem not_tile'_4821 (D : CongruentDissection 4821) : False :=
  not_tile_of_conditions' 4821 C'_4821 D

end Erdos634.Draft.AllN2

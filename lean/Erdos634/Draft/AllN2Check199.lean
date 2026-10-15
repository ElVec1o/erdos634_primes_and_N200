/- AllN2Check199: N = 3899, 3902, 3903, 3907, 3909
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3899_sqf   : LeafSqf 3899   := by decide +kernel
private theorem c3899_range : LeafRange 3899  := by decide +kernel
private theorem c3899_ell   : LeafEll 3899    := by decide +kernel
private theorem c3899_nsq   : NSqChkSq 3899   := by decide +kernel
private theorem c3899_har   : HArithChkSq 3899 := by decide +kernel
private theorem c3899_r     : LeafR 3899      := by decide +kernel
private theorem c3899_e'    : LeafE' 3899     := by decide +kernel
private theorem c3899_f1    : LeafF1 3899     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3899_s2    : S2ChkSq 3899    := by decide +kernel
private theorem c3899_s3    : S3ChkSq 3899    := by decide +kernel
private theorem c3899_iso   : LeafIso 3899    := by decide +kernel
private theorem c3899_nof2  : NoF2ChkSq 3899  := by decide +kernel
private theorem c3899_nof3  : NoF3ChkSq 3899  := by decide +kernel
private theorem c3899_nof4z : NoF4zChkSq 3899 := by decide +kernel
theorem C'_3899 : C' 3899 :=
  ⟨c3899_sqf, c3899_range, c3899_ell, leafNSq_of_sq c3899_nsq, leafHAr_of_sq c3899_har,
   c3899_r, c3899_e', c3899_f1, leafS2_of_sq c3899_s2, leafS3_of_sq c3899_s3,
   c3899_iso, leafR8_of_sq c3899_nof2 c3899_nof3 c3899_nof4z⟩
theorem not_tile'_3899 (D : CongruentDissection 3899) : False :=
  not_tile_of_conditions' 3899 C'_3899 D

private theorem c3902_sqf   : LeafSqf 3902   := by decide +kernel
private theorem c3902_range : LeafRange 3902  := by decide +kernel
private theorem c3902_ell   : LeafEll 3902    := by decide +kernel
private theorem c3902_nsq   : NSqChkSq 3902   := by decide +kernel
private theorem c3902_har   : HArithChkSq 3902 := by decide +kernel
private theorem c3902_r     : LeafR 3902      := by decide +kernel
private theorem c3902_e'    : LeafE' 3902     := by decide +kernel
private theorem c3902_f1    : LeafF1 3902     := Or.inl (by decide)
private theorem c3902_s2    : S2ChkSq 3902    := by decide +kernel
private theorem c3902_s3    : S3ChkSq 3902    := by decide +kernel
private theorem c3902_iso   : LeafIso 3902    := by decide +kernel
private theorem c3902_nof2  : NoF2ChkSq 3902  := by decide +kernel
private theorem c3902_nof3  : NoF3ChkSq 3902  := by decide +kernel
private theorem c3902_nof4z : NoF4zChkSq 3902 := by decide +kernel
theorem C'_3902 : C' 3902 :=
  ⟨c3902_sqf, c3902_range, c3902_ell, leafNSq_of_sq c3902_nsq, leafHAr_of_sq c3902_har,
   c3902_r, c3902_e', c3902_f1, leafS2_of_sq c3902_s2, leafS3_of_sq c3902_s3,
   c3902_iso, leafR8_of_sq c3902_nof2 c3902_nof3 c3902_nof4z⟩
theorem not_tile'_3902 (D : CongruentDissection 3902) : False :=
  not_tile_of_conditions' 3902 C'_3902 D

private theorem c3903_sqf   : LeafSqf 3903   := by decide +kernel
private theorem c3903_range : LeafRange 3903  := by decide +kernel
private theorem c3903_ell   : LeafEll 3903    := by decide +kernel
private theorem c3903_nsq   : NSqChkSq 3903   := by decide +kernel
private theorem c3903_har   : HArithChkSq 3903 := by decide +kernel
private theorem c3903_r     : LeafR 3903      := by decide +kernel
private theorem c3903_e'    : LeafE' 3903     := by decide +kernel
private theorem c3903_f1    : LeafF1 3903     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3903_s2    : S2ChkSq 3903    := by decide +kernel
private theorem c3903_s3    : S3ChkSq 3903    := by decide +kernel
private theorem c3903_iso   : LeafIso 3903    := by decide +kernel
private theorem c3903_nof2  : NoF2ChkSq 3903  := by decide +kernel
private theorem c3903_nof3  : NoF3ChkSq 3903  := by decide +kernel
private theorem c3903_nof4z : NoF4zChkSq 3903 := by decide +kernel
theorem C'_3903 : C' 3903 :=
  ⟨c3903_sqf, c3903_range, c3903_ell, leafNSq_of_sq c3903_nsq, leafHAr_of_sq c3903_har,
   c3903_r, c3903_e', c3903_f1, leafS2_of_sq c3903_s2, leafS3_of_sq c3903_s3,
   c3903_iso, leafR8_of_sq c3903_nof2 c3903_nof3 c3903_nof4z⟩
theorem not_tile'_3903 (D : CongruentDissection 3903) : False :=
  not_tile_of_conditions' 3903 C'_3903 D

private theorem c3907_sqf   : LeafSqf 3907   := by decide +kernel
private theorem c3907_range : LeafRange 3907  := by decide +kernel
private theorem c3907_ell   : LeafEll 3907    := by decide +kernel
private theorem c3907_nsq   : NSqChkSq 3907   := by decide +kernel
private theorem c3907_har   : HArithChkSq 3907 := by decide +kernel
private theorem c3907_r     : LeafR 3907      := by decide +kernel
private theorem c3907_e'    : LeafE' 3907     := by decide +kernel
private theorem c3907_f1    : LeafF1 3907     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3907_s2    : S2ChkSq 3907    := by decide +kernel
private theorem c3907_s3    : S3ChkSq 3907    := by decide +kernel
private theorem c3907_iso   : LeafIso 3907    := by decide +kernel
private theorem c3907_nof2  : NoF2ChkSq 3907  := by decide +kernel
private theorem c3907_nof3  : NoF3ChkSq 3907  := by decide +kernel
private theorem c3907_nof4z : NoF4zChkSq 3907 := by decide +kernel
theorem C'_3907 : C' 3907 :=
  ⟨c3907_sqf, c3907_range, c3907_ell, leafNSq_of_sq c3907_nsq, leafHAr_of_sq c3907_har,
   c3907_r, c3907_e', c3907_f1, leafS2_of_sq c3907_s2, leafS3_of_sq c3907_s3,
   c3907_iso, leafR8_of_sq c3907_nof2 c3907_nof3 c3907_nof4z⟩
theorem not_tile'_3907 (D : CongruentDissection 3907) : False :=
  not_tile_of_conditions' 3907 C'_3907 D

private theorem c3909_sqf   : LeafSqf 3909   := by decide +kernel
private theorem c3909_range : LeafRange 3909  := by decide +kernel
private theorem c3909_ell   : LeafEll 3909    := by decide +kernel
private theorem c3909_nsq   : NSqChkSq 3909   := by decide +kernel
private theorem c3909_har   : HArithChkSq 3909 := by decide +kernel
private theorem c3909_r     : LeafR 3909      := by decide +kernel
private theorem c3909_e'    : LeafE' 3909     := by decide +kernel
private theorem c3909_f1    : LeafF1 3909     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3909_s2    : S2ChkSq 3909    := by decide +kernel
private theorem c3909_s3    : S3ChkSq 3909    := by decide +kernel
private theorem c3909_iso   : LeafIso 3909    := by decide +kernel
private theorem c3909_nof2  : NoF2ChkSq 3909  := by decide +kernel
private theorem c3909_nof3  : NoF3ChkSq 3909  := by decide +kernel
private theorem c3909_nof4z : NoF4zChkSq 3909 := by decide +kernel
theorem C'_3909 : C' 3909 :=
  ⟨c3909_sqf, c3909_range, c3909_ell, leafNSq_of_sq c3909_nsq, leafHAr_of_sq c3909_har,
   c3909_r, c3909_e', c3909_f1, leafS2_of_sq c3909_s2, leafS3_of_sq c3909_s3,
   c3909_iso, leafR8_of_sq c3909_nof2 c3909_nof3 c3909_nof4z⟩
theorem not_tile'_3909 (D : CongruentDissection 3909) : False :=
  not_tile_of_conditions' 3909 C'_3909 D

end Erdos634.Draft.AllN2

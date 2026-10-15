/- AllN2Check201: N = 3919, 3921, 3923, 3926, 3930
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3919_sqf   : LeafSqf 3919   := by decide +kernel
private theorem c3919_range : LeafRange 3919  := by decide +kernel
private theorem c3919_ell   : LeafEll 3919    := by decide +kernel
private theorem c3919_nsq   : NSqChkSq 3919   := by decide +kernel
private theorem c3919_har   : HArithChkSq 3919 := by decide +kernel
private theorem c3919_r     : LeafR 3919      := by decide +kernel
private theorem c3919_e'    : LeafE' 3919     := by decide +kernel
private theorem c3919_f1    : LeafF1 3919     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3919_s2    : S2ChkSq 3919    := by decide +kernel
private theorem c3919_s3    : S3ChkSq 3919    := by decide +kernel
private theorem c3919_iso   : LeafIso 3919    := by decide +kernel
private theorem c3919_nof2  : NoF2ChkSq 3919  := by decide +kernel
private theorem c3919_nof3  : NoF3ChkSq 3919  := by decide +kernel
private theorem c3919_nof4z : NoF4zChkSq 3919 := by decide +kernel
theorem C'_3919 : C' 3919 :=
  ⟨c3919_sqf, c3919_range, c3919_ell, leafNSq_of_sq c3919_nsq, leafHAr_of_sq c3919_har,
   c3919_r, c3919_e', c3919_f1, leafS2_of_sq c3919_s2, leafS3_of_sq c3919_s3,
   c3919_iso, leafR8_of_sq c3919_nof2 c3919_nof3 c3919_nof4z⟩
theorem not_tile'_3919 (D : CongruentDissection 3919) : False :=
  not_tile_of_conditions' 3919 C'_3919 D

private theorem c3921_sqf   : LeafSqf 3921   := by decide +kernel
private theorem c3921_range : LeafRange 3921  := by decide +kernel
private theorem c3921_ell   : LeafEll 3921    := by decide +kernel
private theorem c3921_nsq   : NSqChkSq 3921   := by decide +kernel
private theorem c3921_har   : HArithChkSq 3921 := by decide +kernel
private theorem c3921_r     : LeafR 3921      := by decide +kernel
private theorem c3921_e'    : LeafE' 3921     := by decide +kernel
private theorem c3921_f1    : LeafF1 3921     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3921_s2    : S2ChkSq 3921    := by decide +kernel
private theorem c3921_s3    : S3ChkSq 3921    := by decide +kernel
private theorem c3921_iso   : LeafIso 3921    := by decide +kernel
private theorem c3921_nof2  : NoF2ChkSq 3921  := by decide +kernel
private theorem c3921_nof3  : NoF3ChkSq 3921  := by decide +kernel
private theorem c3921_nof4z : NoF4zChkSq 3921 := by decide +kernel
theorem C'_3921 : C' 3921 :=
  ⟨c3921_sqf, c3921_range, c3921_ell, leafNSq_of_sq c3921_nsq, leafHAr_of_sq c3921_har,
   c3921_r, c3921_e', c3921_f1, leafS2_of_sq c3921_s2, leafS3_of_sq c3921_s3,
   c3921_iso, leafR8_of_sq c3921_nof2 c3921_nof3 c3921_nof4z⟩
theorem not_tile'_3921 (D : CongruentDissection 3921) : False :=
  not_tile_of_conditions' 3921 C'_3921 D

private theorem c3923_sqf   : LeafSqf 3923   := by decide +kernel
private theorem c3923_range : LeafRange 3923  := by decide +kernel
private theorem c3923_ell   : LeafEll 3923    := by decide +kernel
private theorem c3923_nsq   : NSqChkSq 3923   := by decide +kernel
private theorem c3923_har   : HArithChkSq 3923 := by decide +kernel
private theorem c3923_r     : LeafR 3923      := by decide +kernel
private theorem c3923_e'    : LeafE' 3923     := by decide +kernel
private theorem c3923_f1    : LeafF1 3923     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3923_s2    : S2ChkSq 3923    := by decide +kernel
private theorem c3923_s3    : S3ChkSq 3923    := by decide +kernel
private theorem c3923_iso   : LeafIso 3923    := by decide +kernel
private theorem c3923_nof2  : NoF2ChkSq 3923  := by decide +kernel
private theorem c3923_nof3  : NoF3ChkSq 3923  := by decide +kernel
private theorem c3923_nof4z : NoF4zChkSq 3923 := by decide +kernel
theorem C'_3923 : C' 3923 :=
  ⟨c3923_sqf, c3923_range, c3923_ell, leafNSq_of_sq c3923_nsq, leafHAr_of_sq c3923_har,
   c3923_r, c3923_e', c3923_f1, leafS2_of_sq c3923_s2, leafS3_of_sq c3923_s3,
   c3923_iso, leafR8_of_sq c3923_nof2 c3923_nof3 c3923_nof4z⟩
theorem not_tile'_3923 (D : CongruentDissection 3923) : False :=
  not_tile_of_conditions' 3923 C'_3923 D

private theorem c3926_sqf   : LeafSqf 3926   := by decide +kernel
private theorem c3926_range : LeafRange 3926  := by decide +kernel
private theorem c3926_ell   : LeafEll 3926    := by decide +kernel
private theorem c3926_nsq   : NSqChkSq 3926   := by decide +kernel
private theorem c3926_har   : HArithChkSq 3926 := by decide +kernel
private theorem c3926_r     : LeafR 3926      := by decide +kernel
private theorem c3926_e'    : LeafE' 3926     := by decide +kernel
private theorem c3926_f1    : LeafF1 3926     := Or.inl (by decide)
private theorem c3926_s2    : S2ChkSq 3926    := by decide +kernel
private theorem c3926_s3    : S3ChkSq 3926    := by decide +kernel
private theorem c3926_iso   : LeafIso 3926    := by decide +kernel
private theorem c3926_nof2  : NoF2ChkSq 3926  := by decide +kernel
private theorem c3926_nof3  : NoF3ChkSq 3926  := by decide +kernel
private theorem c3926_nof4z : NoF4zChkSq 3926 := by decide +kernel
theorem C'_3926 : C' 3926 :=
  ⟨c3926_sqf, c3926_range, c3926_ell, leafNSq_of_sq c3926_nsq, leafHAr_of_sq c3926_har,
   c3926_r, c3926_e', c3926_f1, leafS2_of_sq c3926_s2, leafS3_of_sq c3926_s3,
   c3926_iso, leafR8_of_sq c3926_nof2 c3926_nof3 c3926_nof4z⟩
theorem not_tile'_3926 (D : CongruentDissection 3926) : False :=
  not_tile_of_conditions' 3926 C'_3926 D

private theorem c3930_sqf   : LeafSqf 3930   := by decide +kernel
private theorem c3930_range : LeafRange 3930  := by decide +kernel
private theorem c3930_ell   : LeafEll 3930    := by decide +kernel
private theorem c3930_nsq   : NSqChkSq 3930   := by decide +kernel
private theorem c3930_har   : HArithChkSq 3930 := by decide +kernel
private theorem c3930_r     : LeafR 3930      := by decide +kernel
private theorem c3930_e'    : LeafE' 3930     := by decide +kernel
private theorem c3930_f1    : LeafF1 3930     := Or.inl (by decide)
private theorem c3930_s2    : S2ChkSq 3930    := by decide +kernel
private theorem c3930_s3    : S3ChkSq 3930    := by decide +kernel
private theorem c3930_iso   : LeafIso 3930    := by decide +kernel
private theorem c3930_nof2  : NoF2ChkSq 3930  := by decide +kernel
private theorem c3930_nof3  : NoF3ChkSq 3930  := by decide +kernel
private theorem c3930_nof4z : NoF4zChkSq 3930 := by decide +kernel
theorem C'_3930 : C' 3930 :=
  ⟨c3930_sqf, c3930_range, c3930_ell, leafNSq_of_sq c3930_nsq, leafHAr_of_sq c3930_har,
   c3930_r, c3930_e', c3930_f1, leafS2_of_sq c3930_s2, leafS3_of_sq c3930_s3,
   c3930_iso, leafR8_of_sq c3930_nof2 c3930_nof3 c3930_nof4z⟩
theorem not_tile'_3930 (D : CongruentDissection 3930) : False :=
  not_tile_of_conditions' 3930 C'_3930 D

end Erdos634.Draft.AllN2

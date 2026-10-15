/- AllN2Check220: N = 4170, 4171, 4174, 4183, 4186
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4170_sqf   : LeafSqf 4170   := by decide +kernel
private theorem c4170_range : LeafRange 4170  := by decide +kernel
private theorem c4170_ell   : LeafEll 4170    := by decide +kernel
private theorem c4170_nsq   : NSqChkSq 4170   := by decide +kernel
private theorem c4170_har   : HArithChkSq 4170 := by decide +kernel
private theorem c4170_r     : LeafR 4170      := by decide +kernel
private theorem c4170_e'    : LeafE' 4170     := by decide +kernel
private theorem c4170_f1    : LeafF1 4170     := Or.inl (by decide)
private theorem c4170_s2    : S2ChkSq 4170    := by decide +kernel
private theorem c4170_s3    : S3ChkSq 4170    := by decide +kernel
private theorem c4170_iso   : LeafIso 4170    := by decide +kernel
private theorem c4170_nof2  : NoF2ChkSq 4170  := by decide +kernel
private theorem c4170_nof3  : NoF3ChkSq 4170  := by decide +kernel
private theorem c4170_nof4z : NoF4zChkSq 4170 := by decide +kernel
theorem C'_4170 : C' 4170 :=
  ⟨c4170_sqf, c4170_range, c4170_ell, leafNSq_of_sq c4170_nsq, leafHAr_of_sq c4170_har,
   c4170_r, c4170_e', c4170_f1, leafS2_of_sq c4170_s2, leafS3_of_sq c4170_s3,
   c4170_iso, leafR8_of_sq c4170_nof2 c4170_nof3 c4170_nof4z⟩
theorem not_tile'_4170 (D : CongruentDissection 4170) : False :=
  not_tile_of_conditions' 4170 C'_4170 D

private theorem c4171_sqf   : LeafSqf 4171   := by decide +kernel
private theorem c4171_range : LeafRange 4171  := by decide +kernel
private theorem c4171_ell   : LeafEll 4171    := by decide +kernel
private theorem c4171_nsq   : NSqChkSq 4171   := by decide +kernel
private theorem c4171_har   : HArithChkSq 4171 := by decide +kernel
private theorem c4171_r     : LeafR 4171      := by decide +kernel
private theorem c4171_e'    : LeafE' 4171     := by decide +kernel
private theorem c4171_f1    : LeafF1 4171     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4171_s2    : S2ChkSq 4171    := by decide +kernel
private theorem c4171_s3    : S3ChkSq 4171    := by decide +kernel
private theorem c4171_iso   : LeafIso 4171    := by decide +kernel
private theorem c4171_nof2  : NoF2ChkSq 4171  := by decide +kernel
private theorem c4171_nof3  : NoF3ChkSq 4171  := by decide +kernel
private theorem c4171_nof4z : NoF4zChkSq 4171 := by decide +kernel
theorem C'_4171 : C' 4171 :=
  ⟨c4171_sqf, c4171_range, c4171_ell, leafNSq_of_sq c4171_nsq, leafHAr_of_sq c4171_har,
   c4171_r, c4171_e', c4171_f1, leafS2_of_sq c4171_s2, leafS3_of_sq c4171_s3,
   c4171_iso, leafR8_of_sq c4171_nof2 c4171_nof3 c4171_nof4z⟩
theorem not_tile'_4171 (D : CongruentDissection 4171) : False :=
  not_tile_of_conditions' 4171 C'_4171 D

private theorem c4174_sqf   : LeafSqf 4174   := by decide +kernel
private theorem c4174_range : LeafRange 4174  := by decide +kernel
private theorem c4174_ell   : LeafEll 4174    := by decide +kernel
private theorem c4174_nsq   : NSqChkSq 4174   := by decide +kernel
private theorem c4174_har   : HArithChkSq 4174 := by decide +kernel
private theorem c4174_r     : LeafR 4174      := by decide +kernel
private theorem c4174_e'    : LeafE' 4174     := by decide +kernel
private theorem c4174_f1    : LeafF1 4174     := Or.inl (by decide)
private theorem c4174_s2    : S2ChkSq 4174    := by decide +kernel
private theorem c4174_s3    : S3ChkSq 4174    := by decide +kernel
private theorem c4174_iso   : LeafIso 4174    := by decide +kernel
private theorem c4174_nof2  : NoF2ChkSq 4174  := by decide +kernel
private theorem c4174_nof3  : NoF3ChkSq 4174  := by decide +kernel
private theorem c4174_nof4z : NoF4zChkSq 4174 := by decide +kernel
theorem C'_4174 : C' 4174 :=
  ⟨c4174_sqf, c4174_range, c4174_ell, leafNSq_of_sq c4174_nsq, leafHAr_of_sq c4174_har,
   c4174_r, c4174_e', c4174_f1, leafS2_of_sq c4174_s2, leafS3_of_sq c4174_s3,
   c4174_iso, leafR8_of_sq c4174_nof2 c4174_nof3 c4174_nof4z⟩
theorem not_tile'_4174 (D : CongruentDissection 4174) : False :=
  not_tile_of_conditions' 4174 C'_4174 D

private theorem c4183_sqf   : LeafSqf 4183   := by decide +kernel
private theorem c4183_range : LeafRange 4183  := by decide +kernel
private theorem c4183_ell   : LeafEll 4183    := by decide +kernel
private theorem c4183_nsq   : NSqChkSq 4183   := by decide +kernel
private theorem c4183_har   : HArithChkSq 4183 := by decide +kernel
private theorem c4183_r     : LeafR 4183      := by decide +kernel
private theorem c4183_e'    : LeafE' 4183     := by decide +kernel
private theorem c4183_f1    : LeafF1 4183     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4183_s2    : S2ChkSq 4183    := by decide +kernel
private theorem c4183_s3    : S3ChkSq 4183    := by decide +kernel
private theorem c4183_iso   : LeafIso 4183    := by decide +kernel
private theorem c4183_nof2  : NoF2ChkSq 4183  := by decide +kernel
private theorem c4183_nof3  : NoF3ChkSq 4183  := by decide +kernel
private theorem c4183_nof4z : NoF4zChkSq 4183 := by decide +kernel
theorem C'_4183 : C' 4183 :=
  ⟨c4183_sqf, c4183_range, c4183_ell, leafNSq_of_sq c4183_nsq, leafHAr_of_sq c4183_har,
   c4183_r, c4183_e', c4183_f1, leafS2_of_sq c4183_s2, leafS3_of_sq c4183_s3,
   c4183_iso, leafR8_of_sq c4183_nof2 c4183_nof3 c4183_nof4z⟩
theorem not_tile'_4183 (D : CongruentDissection 4183) : False :=
  not_tile_of_conditions' 4183 C'_4183 D

private theorem c4186_sqf   : LeafSqf 4186   := by decide +kernel
private theorem c4186_range : LeafRange 4186  := by decide +kernel
private theorem c4186_ell   : LeafEll 4186    := by decide +kernel
private theorem c4186_nsq   : NSqChkSq 4186   := by decide +kernel
private theorem c4186_har   : HArithChkSq 4186 := by decide +kernel
private theorem c4186_r     : LeafR 4186      := by decide +kernel
private theorem c4186_e'    : LeafE' 4186     := by decide +kernel
private theorem c4186_f1    : LeafF1 4186     := Or.inl (by decide)
private theorem c4186_s2    : S2ChkSq 4186    := by decide +kernel
private theorem c4186_s3    : S3ChkSq 4186    := by decide +kernel
private theorem c4186_iso   : LeafIso 4186    := by decide +kernel
private theorem c4186_nof2  : NoF2ChkSq 4186  := by decide +kernel
private theorem c4186_nof3  : NoF3ChkSq 4186  := by decide +kernel
private theorem c4186_nof4z : NoF4zChkSq 4186 := by decide +kernel
theorem C'_4186 : C' 4186 :=
  ⟨c4186_sqf, c4186_range, c4186_ell, leafNSq_of_sq c4186_nsq, leafHAr_of_sq c4186_har,
   c4186_r, c4186_e', c4186_f1, leafS2_of_sq c4186_s2, leafS3_of_sq c4186_s3,
   c4186_iso, leafR8_of_sq c4186_nof2 c4186_nof3 c4186_nof4z⟩
theorem not_tile'_4186 (D : CongruentDissection 4186) : False :=
  not_tile_of_conditions' 4186 C'_4186 D

end Erdos634.Draft.AllN2

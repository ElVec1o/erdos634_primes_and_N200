/- AllN2Check64: N = 2159, 2162, 2167, 2170, 2171
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2159_sqf   : LeafSqf 2159   := by decide +kernel
private theorem c2159_range : LeafRange 2159  := by decide +kernel
private theorem c2159_ell   : LeafEll 2159    := by decide +kernel
private theorem c2159_nsq   : NSqChkSq 2159   := by decide +kernel
private theorem c2159_har   : HArithChkSq 2159 := by decide +kernel
private theorem c2159_r     : LeafR 2159      := by decide +kernel
private theorem c2159_e'    : LeafE' 2159     := by decide +kernel
private theorem c2159_f1    : LeafF1 2159     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2159_s2    : S2ChkSq 2159    := by decide +kernel
private theorem c2159_s3    : S3ChkSq 2159    := by decide +kernel
private theorem c2159_iso   : LeafIso 2159    := by decide +kernel
private theorem c2159_nof2  : NoF2ChkSq 2159  := by decide +kernel
private theorem c2159_nof3  : NoF3ChkSq 2159  := by decide +kernel
private theorem c2159_nof4z : NoF4zChkSq 2159 := by decide +kernel
theorem C'_2159 : C' 2159 :=
  ⟨c2159_sqf, c2159_range, c2159_ell, leafNSq_of_sq c2159_nsq, leafHAr_of_sq c2159_har,
   c2159_r, c2159_e', c2159_f1, leafS2_of_sq c2159_s2, leafS3_of_sq c2159_s3,
   c2159_iso, leafR8_of_sq c2159_nof2 c2159_nof3 c2159_nof4z⟩
theorem not_tile'_2159 (D : CongruentDissection 2159) : False :=
  not_tile_of_conditions' 2159 C'_2159 D

private theorem c2162_sqf   : LeafSqf 2162   := by decide +kernel
private theorem c2162_range : LeafRange 2162  := by decide +kernel
private theorem c2162_ell   : LeafEll 2162    := by decide +kernel
private theorem c2162_nsq   : NSqChkSq 2162   := by decide +kernel
private theorem c2162_har   : HArithChkSq 2162 := by decide +kernel
private theorem c2162_r     : LeafR 2162      := by decide +kernel
private theorem c2162_e'    : LeafE' 2162     := by decide +kernel
private theorem c2162_f1    : LeafF1 2162     := Or.inl (by decide)
private theorem c2162_s2    : S2ChkSq 2162    := by decide +kernel
private theorem c2162_s3    : S3ChkSq 2162    := by decide +kernel
private theorem c2162_iso   : LeafIso 2162    := by decide +kernel
private theorem c2162_nof2  : NoF2ChkSq 2162  := by decide +kernel
private theorem c2162_nof3  : NoF3ChkSq 2162  := by decide +kernel
private theorem c2162_nof4z : NoF4zChkSq 2162 := by decide +kernel
theorem C'_2162 : C' 2162 :=
  ⟨c2162_sqf, c2162_range, c2162_ell, leafNSq_of_sq c2162_nsq, leafHAr_of_sq c2162_har,
   c2162_r, c2162_e', c2162_f1, leafS2_of_sq c2162_s2, leafS3_of_sq c2162_s3,
   c2162_iso, leafR8_of_sq c2162_nof2 c2162_nof3 c2162_nof4z⟩
theorem not_tile'_2162 (D : CongruentDissection 2162) : False :=
  not_tile_of_conditions' 2162 C'_2162 D

private theorem c2167_sqf   : LeafSqf 2167   := by decide +kernel
private theorem c2167_range : LeafRange 2167  := by decide +kernel
private theorem c2167_ell   : LeafEll 2167    := by decide +kernel
private theorem c2167_nsq   : NSqChkSq 2167   := by decide +kernel
private theorem c2167_har   : HArithChkSq 2167 := by decide +kernel
private theorem c2167_r     : LeafR 2167      := by decide +kernel
private theorem c2167_e'    : LeafE' 2167     := by decide +kernel
private theorem c2167_f1    : LeafF1 2167     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2167_s2    : S2ChkSq 2167    := by decide +kernel
private theorem c2167_s3    : S3ChkSq 2167    := by decide +kernel
private theorem c2167_iso   : LeafIso 2167    := by decide +kernel
private theorem c2167_nof2  : NoF2ChkSq 2167  := by decide +kernel
private theorem c2167_nof3  : NoF3ChkSq 2167  := by decide +kernel
private theorem c2167_nof4z : NoF4zChkSq 2167 := by decide +kernel
theorem C'_2167 : C' 2167 :=
  ⟨c2167_sqf, c2167_range, c2167_ell, leafNSq_of_sq c2167_nsq, leafHAr_of_sq c2167_har,
   c2167_r, c2167_e', c2167_f1, leafS2_of_sq c2167_s2, leafS3_of_sq c2167_s3,
   c2167_iso, leafR8_of_sq c2167_nof2 c2167_nof3 c2167_nof4z⟩
theorem not_tile'_2167 (D : CongruentDissection 2167) : False :=
  not_tile_of_conditions' 2167 C'_2167 D

private theorem c2170_sqf   : LeafSqf 2170   := by decide +kernel
private theorem c2170_range : LeafRange 2170  := by decide +kernel
private theorem c2170_ell   : LeafEll 2170    := by decide +kernel
private theorem c2170_nsq   : NSqChkSq 2170   := by decide +kernel
private theorem c2170_har   : HArithChkSq 2170 := by decide +kernel
private theorem c2170_r     : LeafR 2170      := by decide +kernel
private theorem c2170_e'    : LeafE' 2170     := by decide +kernel
private theorem c2170_f1    : LeafF1 2170     := Or.inl (by decide)
private theorem c2170_s2    : S2ChkSq 2170    := by decide +kernel
private theorem c2170_s3    : S3ChkSq 2170    := by decide +kernel
private theorem c2170_iso   : LeafIso 2170    := by decide +kernel
private theorem c2170_nof2  : NoF2ChkSq 2170  := by decide +kernel
private theorem c2170_nof3  : NoF3ChkSq 2170  := by decide +kernel
private theorem c2170_nof4z : NoF4zChkSq 2170 := by decide +kernel
theorem C'_2170 : C' 2170 :=
  ⟨c2170_sqf, c2170_range, c2170_ell, leafNSq_of_sq c2170_nsq, leafHAr_of_sq c2170_har,
   c2170_r, c2170_e', c2170_f1, leafS2_of_sq c2170_s2, leafS3_of_sq c2170_s3,
   c2170_iso, leafR8_of_sq c2170_nof2 c2170_nof3 c2170_nof4z⟩
theorem not_tile'_2170 (D : CongruentDissection 2170) : False :=
  not_tile_of_conditions' 2170 C'_2170 D

private theorem c2171_sqf   : LeafSqf 2171   := by decide +kernel
private theorem c2171_range : LeafRange 2171  := by decide +kernel
private theorem c2171_ell   : LeafEll 2171    := by decide +kernel
private theorem c2171_nsq   : NSqChkSq 2171   := by decide +kernel
private theorem c2171_har   : HArithChkSq 2171 := by decide +kernel
private theorem c2171_r     : LeafR 2171      := by decide +kernel
private theorem c2171_e'    : LeafE' 2171     := by decide +kernel
private theorem c2171_f1    : LeafF1 2171     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2171_s2    : S2ChkSq 2171    := by decide +kernel
private theorem c2171_s3    : S3ChkSq 2171    := by decide +kernel
private theorem c2171_iso   : LeafIso 2171    := by decide +kernel
private theorem c2171_nof2  : NoF2ChkSq 2171  := by decide +kernel
private theorem c2171_nof3  : NoF3ChkSq 2171  := by decide +kernel
private theorem c2171_nof4z : NoF4zChkSq 2171 := by decide +kernel
theorem C'_2171 : C' 2171 :=
  ⟨c2171_sqf, c2171_range, c2171_ell, leafNSq_of_sq c2171_nsq, leafHAr_of_sq c2171_har,
   c2171_r, c2171_e', c2171_f1, leafS2_of_sq c2171_s2, leafS3_of_sq c2171_s3,
   c2171_iso, leafR8_of_sq c2171_nof2 c2171_nof3 c2171_nof4z⟩
theorem not_tile'_2171 (D : CongruentDissection 2171) : False :=
  not_tile_of_conditions' 2171 C'_2171 D

end Erdos634.Draft.AllN2

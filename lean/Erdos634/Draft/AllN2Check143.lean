/- AllN2Check143: N = 3153, 3154, 3155, 3157, 3158
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3153_sqf   : LeafSqf 3153   := by decide +kernel
private theorem c3153_range : LeafRange 3153  := by decide +kernel
private theorem c3153_ell   : LeafEll 3153    := by decide +kernel
private theorem c3153_nsq   : NSqChkSq 3153   := by decide +kernel
private theorem c3153_har   : HArithChkSq 3153 := by decide +kernel
private theorem c3153_r     : LeafR 3153      := by decide +kernel
private theorem c3153_e'    : LeafE' 3153     := by decide +kernel
private theorem c3153_f1    : LeafF1 3153     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3153_s2    : S2ChkSq 3153    := by decide +kernel
private theorem c3153_s3    : S3ChkSq 3153    := by decide +kernel
private theorem c3153_iso   : LeafIso 3153    := by decide +kernel
private theorem c3153_nof2  : NoF2ChkSq 3153  := by decide +kernel
private theorem c3153_nof3  : NoF3ChkSq 3153  := by decide +kernel
private theorem c3153_nof4z : NoF4zChkSq 3153 := by decide +kernel
theorem C'_3153 : C' 3153 :=
  ⟨c3153_sqf, c3153_range, c3153_ell, leafNSq_of_sq c3153_nsq, leafHAr_of_sq c3153_har,
   c3153_r, c3153_e', c3153_f1, leafS2_of_sq c3153_s2, leafS3_of_sq c3153_s3,
   c3153_iso, leafR8_of_sq c3153_nof2 c3153_nof3 c3153_nof4z⟩
theorem not_tile'_3153 (D : CongruentDissection 3153) : False :=
  not_tile_of_conditions' 3153 C'_3153 D

private theorem c3154_sqf   : LeafSqf 3154   := by decide +kernel
private theorem c3154_range : LeafRange 3154  := by decide +kernel
private theorem c3154_ell   : LeafEll 3154    := by decide +kernel
private theorem c3154_nsq   : NSqChkSq 3154   := by decide +kernel
private theorem c3154_har   : HArithChkSq 3154 := by decide +kernel
private theorem c3154_r     : LeafR 3154      := by decide +kernel
private theorem c3154_e'    : LeafE' 3154     := by decide +kernel
private theorem c3154_f1    : LeafF1 3154     := Or.inl (by decide)
private theorem c3154_s2    : S2ChkSq 3154    := by decide +kernel
private theorem c3154_s3    : S3ChkSq 3154    := by decide +kernel
private theorem c3154_iso   : LeafIso 3154    := by decide +kernel
private theorem c3154_nof2  : NoF2ChkSq 3154  := by decide +kernel
private theorem c3154_nof3  : NoF3ChkSq 3154  := by decide +kernel
private theorem c3154_nof4z : NoF4zChkSq 3154 := by decide +kernel
theorem C'_3154 : C' 3154 :=
  ⟨c3154_sqf, c3154_range, c3154_ell, leafNSq_of_sq c3154_nsq, leafHAr_of_sq c3154_har,
   c3154_r, c3154_e', c3154_f1, leafS2_of_sq c3154_s2, leafS3_of_sq c3154_s3,
   c3154_iso, leafR8_of_sq c3154_nof2 c3154_nof3 c3154_nof4z⟩
theorem not_tile'_3154 (D : CongruentDissection 3154) : False :=
  not_tile_of_conditions' 3154 C'_3154 D

private theorem c3155_sqf   : LeafSqf 3155   := by decide +kernel
private theorem c3155_range : LeafRange 3155  := by decide +kernel
private theorem c3155_ell   : LeafEll 3155    := by decide +kernel
private theorem c3155_nsq   : NSqChkSq 3155   := by decide +kernel
private theorem c3155_har   : HArithChkSq 3155 := by decide +kernel
private theorem c3155_r     : LeafR 3155      := by decide +kernel
private theorem c3155_e'    : LeafE' 3155     := by decide +kernel
private theorem c3155_f1    : LeafF1 3155     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3155_s2    : S2ChkSq 3155    := by decide +kernel
private theorem c3155_s3    : S3ChkSq 3155    := by decide +kernel
private theorem c3155_iso   : LeafIso 3155    := by decide +kernel
private theorem c3155_nof2  : NoF2ChkSq 3155  := by decide +kernel
private theorem c3155_nof3  : NoF3ChkSq 3155  := by decide +kernel
private theorem c3155_nof4z : NoF4zChkSq 3155 := by decide +kernel
theorem C'_3155 : C' 3155 :=
  ⟨c3155_sqf, c3155_range, c3155_ell, leafNSq_of_sq c3155_nsq, leafHAr_of_sq c3155_har,
   c3155_r, c3155_e', c3155_f1, leafS2_of_sq c3155_s2, leafS3_of_sq c3155_s3,
   c3155_iso, leafR8_of_sq c3155_nof2 c3155_nof3 c3155_nof4z⟩
theorem not_tile'_3155 (D : CongruentDissection 3155) : False :=
  not_tile_of_conditions' 3155 C'_3155 D

private theorem c3157_sqf   : LeafSqf 3157   := by decide +kernel
private theorem c3157_range : LeafRange 3157  := by decide +kernel
private theorem c3157_ell   : LeafEll 3157    := by decide +kernel
private theorem c3157_nsq   : NSqChkSq 3157   := by decide +kernel
private theorem c3157_har   : HArithChkSq 3157 := by decide +kernel
private theorem c3157_r     : LeafR 3157      := by decide +kernel
private theorem c3157_e'    : LeafE' 3157     := by decide +kernel
private theorem c3157_f1    : LeafF1 3157     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3157_s2    : S2ChkSq 3157    := by decide +kernel
private theorem c3157_s3    : S3ChkSq 3157    := by decide +kernel
private theorem c3157_iso   : LeafIso 3157    := by decide +kernel
private theorem c3157_nof2  : NoF2ChkSq 3157  := by decide +kernel
private theorem c3157_nof3  : NoF3ChkSq 3157  := by decide +kernel
private theorem c3157_nof4z : NoF4zChkSq 3157 := by decide +kernel
theorem C'_3157 : C' 3157 :=
  ⟨c3157_sqf, c3157_range, c3157_ell, leafNSq_of_sq c3157_nsq, leafHAr_of_sq c3157_har,
   c3157_r, c3157_e', c3157_f1, leafS2_of_sq c3157_s2, leafS3_of_sq c3157_s3,
   c3157_iso, leafR8_of_sq c3157_nof2 c3157_nof3 c3157_nof4z⟩
theorem not_tile'_3157 (D : CongruentDissection 3157) : False :=
  not_tile_of_conditions' 3157 C'_3157 D

private theorem c3158_sqf   : LeafSqf 3158   := by decide +kernel
private theorem c3158_range : LeafRange 3158  := by decide +kernel
private theorem c3158_ell   : LeafEll 3158    := by decide +kernel
private theorem c3158_nsq   : NSqChkSq 3158   := by decide +kernel
private theorem c3158_har   : HArithChkSq 3158 := by decide +kernel
private theorem c3158_r     : LeafR 3158      := by decide +kernel
private theorem c3158_e'    : LeafE' 3158     := by decide +kernel
private theorem c3158_f1    : LeafF1 3158     := Or.inl (by decide)
private theorem c3158_s2    : S2ChkSq 3158    := by decide +kernel
private theorem c3158_s3    : S3ChkSq 3158    := by decide +kernel
private theorem c3158_iso   : LeafIso 3158    := by decide +kernel
private theorem c3158_nof2  : NoF2ChkSq 3158  := by decide +kernel
private theorem c3158_nof3  : NoF3ChkSq 3158  := by decide +kernel
private theorem c3158_nof4z : NoF4zChkSq 3158 := by decide +kernel
theorem C'_3158 : C' 3158 :=
  ⟨c3158_sqf, c3158_range, c3158_ell, leafNSq_of_sq c3158_nsq, leafHAr_of_sq c3158_har,
   c3158_r, c3158_e', c3158_f1, leafS2_of_sq c3158_s2, leafS3_of_sq c3158_s3,
   c3158_iso, leafR8_of_sq c3158_nof2 c3158_nof3 c3158_nof4z⟩
theorem not_tile'_3158 (D : CongruentDissection 3158) : False :=
  not_tile_of_conditions' 3158 C'_3158 D

end Erdos634.Draft.AllN2

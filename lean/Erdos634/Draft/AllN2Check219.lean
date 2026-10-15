/- AllN2Check219: N = 4154, 4159, 4163, 4166, 4169
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4154_sqf   : LeafSqf 4154   := by decide +kernel
private theorem c4154_range : LeafRange 4154  := by decide +kernel
private theorem c4154_ell   : LeafEll 4154    := by decide +kernel
private theorem c4154_nsq   : NSqChkSq 4154   := by decide +kernel
private theorem c4154_har   : HArithChkSq 4154 := by decide +kernel
private theorem c4154_r     : LeafR 4154      := by decide +kernel
private theorem c4154_e'    : LeafE' 4154     := by decide +kernel
private theorem c4154_f1    : LeafF1 4154     := Or.inl (by decide)
private theorem c4154_s2    : S2ChkSq 4154    := by decide +kernel
private theorem c4154_s3    : S3ChkSq 4154    := by decide +kernel
private theorem c4154_iso   : LeafIso 4154    := by decide +kernel
private theorem c4154_nof2  : NoF2ChkSq 4154  := by decide +kernel
private theorem c4154_nof3  : NoF3ChkSq 4154  := by decide +kernel
private theorem c4154_nof4z : NoF4zChkSq 4154 := by decide +kernel
theorem C'_4154 : C' 4154 :=
  ⟨c4154_sqf, c4154_range, c4154_ell, leafNSq_of_sq c4154_nsq, leafHAr_of_sq c4154_har,
   c4154_r, c4154_e', c4154_f1, leafS2_of_sq c4154_s2, leafS3_of_sq c4154_s3,
   c4154_iso, leafR8_of_sq c4154_nof2 c4154_nof3 c4154_nof4z⟩
theorem not_tile'_4154 (D : CongruentDissection 4154) : False :=
  not_tile_of_conditions' 4154 C'_4154 D

private theorem c4159_sqf   : LeafSqf 4159   := by decide +kernel
private theorem c4159_range : LeafRange 4159  := by decide +kernel
private theorem c4159_ell   : LeafEll 4159    := by decide +kernel
private theorem c4159_nsq   : NSqChkSq 4159   := by decide +kernel
private theorem c4159_har   : HArithChkSq 4159 := by decide +kernel
private theorem c4159_r     : LeafR 4159      := by decide +kernel
private theorem c4159_e'    : LeafE' 4159     := by decide +kernel
private theorem c4159_f1    : LeafF1 4159     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4159_s2    : S2ChkSq 4159    := by decide +kernel
private theorem c4159_s3    : S3ChkSq 4159    := by decide +kernel
private theorem c4159_iso   : LeafIso 4159    := by decide +kernel
private theorem c4159_nof2  : NoF2ChkSq 4159  := by decide +kernel
private theorem c4159_nof3  : NoF3ChkSq 4159  := by decide +kernel
private theorem c4159_nof4z : NoF4zChkSq 4159 := by decide +kernel
theorem C'_4159 : C' 4159 :=
  ⟨c4159_sqf, c4159_range, c4159_ell, leafNSq_of_sq c4159_nsq, leafHAr_of_sq c4159_har,
   c4159_r, c4159_e', c4159_f1, leafS2_of_sq c4159_s2, leafS3_of_sq c4159_s3,
   c4159_iso, leafR8_of_sq c4159_nof2 c4159_nof3 c4159_nof4z⟩
theorem not_tile'_4159 (D : CongruentDissection 4159) : False :=
  not_tile_of_conditions' 4159 C'_4159 D

private theorem c4163_sqf   : LeafSqf 4163   := by decide +kernel
private theorem c4163_range : LeafRange 4163  := by decide +kernel
private theorem c4163_ell   : LeafEll 4163    := by decide +kernel
private theorem c4163_nsq   : NSqChkSq 4163   := by decide +kernel
private theorem c4163_har   : HArithChkSq 4163 := by decide +kernel
private theorem c4163_r     : LeafR 4163      := by decide +kernel
private theorem c4163_e'    : LeafE' 4163     := by decide +kernel
private theorem c4163_f1    : LeafF1 4163     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4163_s2    : S2ChkSq 4163    := by decide +kernel
private theorem c4163_s3    : S3ChkSq 4163    := by decide +kernel
private theorem c4163_iso   : LeafIso 4163    := by decide +kernel
private theorem c4163_nof2  : NoF2ChkSq 4163  := by decide +kernel
private theorem c4163_nof3  : NoF3ChkSq 4163  := by decide +kernel
private theorem c4163_nof4z : NoF4zChkSq 4163 := by decide +kernel
theorem C'_4163 : C' 4163 :=
  ⟨c4163_sqf, c4163_range, c4163_ell, leafNSq_of_sq c4163_nsq, leafHAr_of_sq c4163_har,
   c4163_r, c4163_e', c4163_f1, leafS2_of_sq c4163_s2, leafS3_of_sq c4163_s3,
   c4163_iso, leafR8_of_sq c4163_nof2 c4163_nof3 c4163_nof4z⟩
theorem not_tile'_4163 (D : CongruentDissection 4163) : False :=
  not_tile_of_conditions' 4163 C'_4163 D

private theorem c4166_sqf   : LeafSqf 4166   := by decide +kernel
private theorem c4166_range : LeafRange 4166  := by decide +kernel
private theorem c4166_ell   : LeafEll 4166    := by decide +kernel
private theorem c4166_nsq   : NSqChkSq 4166   := by decide +kernel
private theorem c4166_har   : HArithChkSq 4166 := by decide +kernel
private theorem c4166_r     : LeafR 4166      := by decide +kernel
private theorem c4166_e'    : LeafE' 4166     := by decide +kernel
private theorem c4166_f1    : LeafF1 4166     := Or.inl (by decide)
private theorem c4166_s2    : S2ChkSq 4166    := by decide +kernel
private theorem c4166_s3    : S3ChkSq 4166    := by decide +kernel
private theorem c4166_iso   : LeafIso 4166    := by decide +kernel
private theorem c4166_nof2  : NoF2ChkSq 4166  := by decide +kernel
private theorem c4166_nof3  : NoF3ChkSq 4166  := by decide +kernel
private theorem c4166_nof4z : NoF4zChkSq 4166 := by decide +kernel
theorem C'_4166 : C' 4166 :=
  ⟨c4166_sqf, c4166_range, c4166_ell, leafNSq_of_sq c4166_nsq, leafHAr_of_sq c4166_har,
   c4166_r, c4166_e', c4166_f1, leafS2_of_sq c4166_s2, leafS3_of_sq c4166_s3,
   c4166_iso, leafR8_of_sq c4166_nof2 c4166_nof3 c4166_nof4z⟩
theorem not_tile'_4166 (D : CongruentDissection 4166) : False :=
  not_tile_of_conditions' 4166 C'_4166 D

private theorem c4169_sqf   : LeafSqf 4169   := by decide +kernel
private theorem c4169_range : LeafRange 4169  := by decide +kernel
private theorem c4169_ell   : LeafEll 4169    := by decide +kernel
private theorem c4169_nsq   : NSqChkSq 4169   := by decide +kernel
private theorem c4169_har   : HArithChkSq 4169 := by decide +kernel
private theorem c4169_r     : LeafR 4169      := by decide +kernel
private theorem c4169_e'    : LeafE' 4169     := by decide +kernel
private theorem c4169_f1    : LeafF1 4169     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4169_s2    : S2ChkSq 4169    := by decide +kernel
private theorem c4169_s3    : S3ChkSq 4169    := by decide +kernel
private theorem c4169_iso   : LeafIso 4169    := by decide +kernel
private theorem c4169_nof2  : NoF2ChkSq 4169  := by decide +kernel
private theorem c4169_nof3  : NoF3ChkSq 4169  := by decide +kernel
private theorem c4169_nof4z : NoF4zChkSq 4169 := by decide +kernel
theorem C'_4169 : C' 4169 :=
  ⟨c4169_sqf, c4169_range, c4169_ell, leafNSq_of_sq c4169_nsq, leafHAr_of_sq c4169_har,
   c4169_r, c4169_e', c4169_f1, leafS2_of_sq c4169_s2, leafS3_of_sq c4169_s3,
   c4169_iso, leafR8_of_sq c4169_nof2 c4169_nof3 c4169_nof4z⟩
theorem not_tile'_4169 (D : CongruentDissection 4169) : False :=
  not_tile_of_conditions' 4169 C'_4169 D

end Erdos634.Draft.AllN2

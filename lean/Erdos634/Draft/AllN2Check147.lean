/- AllN2Check147: N = 3207, 3210, 3214, 3215, 3223
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3207_sqf   : LeafSqf 3207   := by decide +kernel
private theorem c3207_range : LeafRange 3207  := by decide +kernel
private theorem c3207_ell   : LeafEll 3207    := by decide +kernel
private theorem c3207_nsq   : NSqChkSq 3207   := by decide +kernel
private theorem c3207_har   : HArithChkSq 3207 := by decide +kernel
private theorem c3207_r     : LeafR 3207      := by decide +kernel
private theorem c3207_e'    : LeafE' 3207     := by decide +kernel
private theorem c3207_f1    : LeafF1 3207     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3207_s2    : S2ChkSq 3207    := by decide +kernel
private theorem c3207_s3    : S3ChkSq 3207    := by decide +kernel
private theorem c3207_iso   : LeafIso 3207    := by decide +kernel
private theorem c3207_nof2  : NoF2ChkSq 3207  := by decide +kernel
private theorem c3207_nof3  : NoF3ChkSq 3207  := by decide +kernel
private theorem c3207_nof4z : NoF4zChkSq 3207 := by decide +kernel
theorem C'_3207 : C' 3207 :=
  ⟨c3207_sqf, c3207_range, c3207_ell, leafNSq_of_sq c3207_nsq, leafHAr_of_sq c3207_har,
   c3207_r, c3207_e', c3207_f1, leafS2_of_sq c3207_s2, leafS3_of_sq c3207_s3,
   c3207_iso, leafR8_of_sq c3207_nof2 c3207_nof3 c3207_nof4z⟩
theorem not_tile'_3207 (D : CongruentDissection 3207) : False :=
  not_tile_of_conditions' 3207 C'_3207 D

private theorem c3210_sqf   : LeafSqf 3210   := by decide +kernel
private theorem c3210_range : LeafRange 3210  := by decide +kernel
private theorem c3210_ell   : LeafEll 3210    := by decide +kernel
private theorem c3210_nsq   : NSqChkSq 3210   := by decide +kernel
private theorem c3210_har   : HArithChkSq 3210 := by decide +kernel
private theorem c3210_r     : LeafR 3210      := by decide +kernel
private theorem c3210_e'    : LeafE' 3210     := by decide +kernel
private theorem c3210_f1    : LeafF1 3210     := Or.inl (by decide)
private theorem c3210_s2    : S2ChkSq 3210    := by decide +kernel
private theorem c3210_s3    : S3ChkSq 3210    := by decide +kernel
private theorem c3210_iso   : LeafIso 3210    := by decide +kernel
private theorem c3210_nof2  : NoF2ChkSq 3210  := by decide +kernel
private theorem c3210_nof3  : NoF3ChkSq 3210  := by decide +kernel
private theorem c3210_nof4z : NoF4zChkSq 3210 := by decide +kernel
theorem C'_3210 : C' 3210 :=
  ⟨c3210_sqf, c3210_range, c3210_ell, leafNSq_of_sq c3210_nsq, leafHAr_of_sq c3210_har,
   c3210_r, c3210_e', c3210_f1, leafS2_of_sq c3210_s2, leafS3_of_sq c3210_s3,
   c3210_iso, leafR8_of_sq c3210_nof2 c3210_nof3 c3210_nof4z⟩
theorem not_tile'_3210 (D : CongruentDissection 3210) : False :=
  not_tile_of_conditions' 3210 C'_3210 D

private theorem c3214_sqf   : LeafSqf 3214   := by decide +kernel
private theorem c3214_range : LeafRange 3214  := by decide +kernel
private theorem c3214_ell   : LeafEll 3214    := by decide +kernel
private theorem c3214_nsq   : NSqChkSq 3214   := by decide +kernel
private theorem c3214_har   : HArithChkSq 3214 := by decide +kernel
private theorem c3214_r     : LeafR 3214      := by decide +kernel
private theorem c3214_e'    : LeafE' 3214     := by decide +kernel
private theorem c3214_f1    : LeafF1 3214     := Or.inl (by decide)
private theorem c3214_s2    : S2ChkSq 3214    := by decide +kernel
private theorem c3214_s3    : S3ChkSq 3214    := by decide +kernel
private theorem c3214_iso   : LeafIso 3214    := by decide +kernel
private theorem c3214_nof2  : NoF2ChkSq 3214  := by decide +kernel
private theorem c3214_nof3  : NoF3ChkSq 3214  := by decide +kernel
private theorem c3214_nof4z : NoF4zChkSq 3214 := by decide +kernel
theorem C'_3214 : C' 3214 :=
  ⟨c3214_sqf, c3214_range, c3214_ell, leafNSq_of_sq c3214_nsq, leafHAr_of_sq c3214_har,
   c3214_r, c3214_e', c3214_f1, leafS2_of_sq c3214_s2, leafS3_of_sq c3214_s3,
   c3214_iso, leafR8_of_sq c3214_nof2 c3214_nof3 c3214_nof4z⟩
theorem not_tile'_3214 (D : CongruentDissection 3214) : False :=
  not_tile_of_conditions' 3214 C'_3214 D

private theorem c3215_sqf   : LeafSqf 3215   := by decide +kernel
private theorem c3215_range : LeafRange 3215  := by decide +kernel
private theorem c3215_ell   : LeafEll 3215    := by decide +kernel
private theorem c3215_nsq   : NSqChkSq 3215   := by decide +kernel
private theorem c3215_har   : HArithChkSq 3215 := by decide +kernel
private theorem c3215_r     : LeafR 3215      := by decide +kernel
private theorem c3215_e'    : LeafE' 3215     := by decide +kernel
private theorem c3215_f1    : LeafF1 3215     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3215_s2    : S2ChkSq 3215    := by decide +kernel
private theorem c3215_s3    : S3ChkSq 3215    := by decide +kernel
private theorem c3215_iso   : LeafIso 3215    := by decide +kernel
private theorem c3215_nof2  : NoF2ChkSq 3215  := by decide +kernel
private theorem c3215_nof3  : NoF3ChkSq 3215  := by decide +kernel
private theorem c3215_nof4z : NoF4zChkSq 3215 := by decide +kernel
theorem C'_3215 : C' 3215 :=
  ⟨c3215_sqf, c3215_range, c3215_ell, leafNSq_of_sq c3215_nsq, leafHAr_of_sq c3215_har,
   c3215_r, c3215_e', c3215_f1, leafS2_of_sq c3215_s2, leafS3_of_sq c3215_s3,
   c3215_iso, leafR8_of_sq c3215_nof2 c3215_nof3 c3215_nof4z⟩
theorem not_tile'_3215 (D : CongruentDissection 3215) : False :=
  not_tile_of_conditions' 3215 C'_3215 D

private theorem c3223_sqf   : LeafSqf 3223   := by decide +kernel
private theorem c3223_range : LeafRange 3223  := by decide +kernel
private theorem c3223_ell   : LeafEll 3223    := by decide +kernel
private theorem c3223_nsq   : NSqChkSq 3223   := by decide +kernel
private theorem c3223_har   : HArithChkSq 3223 := by decide +kernel
private theorem c3223_r     : LeafR 3223      := by decide +kernel
private theorem c3223_e'    : LeafE' 3223     := by decide +kernel
private theorem c3223_f1    : LeafF1 3223     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3223_s2    : S2ChkSq 3223    := by decide +kernel
private theorem c3223_s3    : S3ChkSq 3223    := by decide +kernel
private theorem c3223_iso   : LeafIso 3223    := by decide +kernel
private theorem c3223_nof2  : NoF2ChkSq 3223  := by decide +kernel
private theorem c3223_nof3  : NoF3ChkSq 3223  := by decide +kernel
private theorem c3223_nof4z : NoF4zChkSq 3223 := by decide +kernel
theorem C'_3223 : C' 3223 :=
  ⟨c3223_sqf, c3223_range, c3223_ell, leafNSq_of_sq c3223_nsq, leafHAr_of_sq c3223_har,
   c3223_r, c3223_e', c3223_f1, leafS2_of_sq c3223_s2, leafS3_of_sq c3223_s3,
   c3223_iso, leafR8_of_sq c3223_nof2 c3223_nof3 c3223_nof4z⟩
theorem not_tile'_3223 (D : CongruentDissection 3223) : False :=
  not_tile_of_conditions' 3223 C'_3223 D

end Erdos634.Draft.AllN2

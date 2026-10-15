/- AllN2Check221: N = 4187, 4189, 4190, 4193, 4195
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4187_sqf   : LeafSqf 4187   := by decide +kernel
private theorem c4187_range : LeafRange 4187  := by decide +kernel
private theorem c4187_ell   : LeafEll 4187    := by decide +kernel
private theorem c4187_nsq   : NSqChkSq 4187   := by decide +kernel
private theorem c4187_har   : HArithChkSq 4187 := by decide +kernel
private theorem c4187_r     : LeafR 4187      := by decide +kernel
private theorem c4187_e'    : LeafE' 4187     := by decide +kernel
private theorem c4187_f1    : LeafF1 4187     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4187_s2    : S2ChkSq 4187    := by decide +kernel
private theorem c4187_s3    : S3ChkSq 4187    := by decide +kernel
private theorem c4187_iso   : LeafIso 4187    := by decide +kernel
private theorem c4187_nof2  : NoF2ChkSq 4187  := by decide +kernel
private theorem c4187_nof3  : NoF3ChkSq 4187  := by decide +kernel
private theorem c4187_nof4z : NoF4zChkSq 4187 := by decide +kernel
theorem C'_4187 : C' 4187 :=
  ⟨c4187_sqf, c4187_range, c4187_ell, leafNSq_of_sq c4187_nsq, leafHAr_of_sq c4187_har,
   c4187_r, c4187_e', c4187_f1, leafS2_of_sq c4187_s2, leafS3_of_sq c4187_s3,
   c4187_iso, leafR8_of_sq c4187_nof2 c4187_nof3 c4187_nof4z⟩
theorem not_tile'_4187 (D : CongruentDissection 4187) : False :=
  not_tile_of_conditions' 4187 C'_4187 D

private theorem c4189_sqf   : LeafSqf 4189   := by decide +kernel
private theorem c4189_range : LeafRange 4189  := by decide +kernel
private theorem c4189_ell   : LeafEll 4189    := by decide +kernel
private theorem c4189_nsq   : NSqChkSq 4189   := by decide +kernel
private theorem c4189_har   : HArithChkSq 4189 := by decide +kernel
private theorem c4189_r     : LeafR 4189      := by decide +kernel
private theorem c4189_e'    : LeafE' 4189     := by decide +kernel
private theorem c4189_f1    : LeafF1 4189     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4189_s2    : S2ChkSq 4189    := by decide +kernel
private theorem c4189_s3    : S3ChkSq 4189    := by decide +kernel
private theorem c4189_iso   : LeafIso 4189    := by decide +kernel
private theorem c4189_nof2  : NoF2ChkSq 4189  := by decide +kernel
private theorem c4189_nof3  : NoF3ChkSq 4189  := by decide +kernel
private theorem c4189_nof4z : NoF4zChkSq 4189 := by decide +kernel
theorem C'_4189 : C' 4189 :=
  ⟨c4189_sqf, c4189_range, c4189_ell, leafNSq_of_sq c4189_nsq, leafHAr_of_sq c4189_har,
   c4189_r, c4189_e', c4189_f1, leafS2_of_sq c4189_s2, leafS3_of_sq c4189_s3,
   c4189_iso, leafR8_of_sq c4189_nof2 c4189_nof3 c4189_nof4z⟩
theorem not_tile'_4189 (D : CongruentDissection 4189) : False :=
  not_tile_of_conditions' 4189 C'_4189 D

private theorem c4190_sqf   : LeafSqf 4190   := by decide +kernel
private theorem c4190_range : LeafRange 4190  := by decide +kernel
private theorem c4190_ell   : LeafEll 4190    := by decide +kernel
private theorem c4190_nsq   : NSqChkSq 4190   := by decide +kernel
private theorem c4190_har   : HArithChkSq 4190 := by decide +kernel
private theorem c4190_r     : LeafR 4190      := by decide +kernel
private theorem c4190_e'    : LeafE' 4190     := by decide +kernel
private theorem c4190_f1    : LeafF1 4190     := Or.inl (by decide)
private theorem c4190_s2    : S2ChkSq 4190    := by decide +kernel
private theorem c4190_s3    : S3ChkSq 4190    := by decide +kernel
private theorem c4190_iso   : LeafIso 4190    := by decide +kernel
private theorem c4190_nof2  : NoF2ChkSq 4190  := by decide +kernel
private theorem c4190_nof3  : NoF3ChkSq 4190  := by decide +kernel
private theorem c4190_nof4z : NoF4zChkSq 4190 := by decide +kernel
theorem C'_4190 : C' 4190 :=
  ⟨c4190_sqf, c4190_range, c4190_ell, leafNSq_of_sq c4190_nsq, leafHAr_of_sq c4190_har,
   c4190_r, c4190_e', c4190_f1, leafS2_of_sq c4190_s2, leafS3_of_sq c4190_s3,
   c4190_iso, leafR8_of_sq c4190_nof2 c4190_nof3 c4190_nof4z⟩
theorem not_tile'_4190 (D : CongruentDissection 4190) : False :=
  not_tile_of_conditions' 4190 C'_4190 D

private theorem c4193_sqf   : LeafSqf 4193   := by decide +kernel
private theorem c4193_range : LeafRange 4193  := by decide +kernel
private theorem c4193_ell   : LeafEll 4193    := by decide +kernel
private theorem c4193_nsq   : NSqChkSq 4193   := by decide +kernel
private theorem c4193_har   : HArithChkSq 4193 := by decide +kernel
private theorem c4193_r     : LeafR 4193      := by decide +kernel
private theorem c4193_e'    : LeafE' 4193     := by decide +kernel
private theorem c4193_f1    : LeafF1 4193     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4193_s2    : S2ChkSq 4193    := by decide +kernel
private theorem c4193_s3    : S3ChkSq 4193    := by decide +kernel
private theorem c4193_iso   : LeafIso 4193    := by decide +kernel
private theorem c4193_nof2  : NoF2ChkSq 4193  := by decide +kernel
private theorem c4193_nof3  : NoF3ChkSq 4193  := by decide +kernel
private theorem c4193_nof4z : NoF4zChkSq 4193 := by decide +kernel
theorem C'_4193 : C' 4193 :=
  ⟨c4193_sqf, c4193_range, c4193_ell, leafNSq_of_sq c4193_nsq, leafHAr_of_sq c4193_har,
   c4193_r, c4193_e', c4193_f1, leafS2_of_sq c4193_s2, leafS3_of_sq c4193_s3,
   c4193_iso, leafR8_of_sq c4193_nof2 c4193_nof3 c4193_nof4z⟩
theorem not_tile'_4193 (D : CongruentDissection 4193) : False :=
  not_tile_of_conditions' 4193 C'_4193 D

private theorem c4195_sqf   : LeafSqf 4195   := by decide +kernel
private theorem c4195_range : LeafRange 4195  := by decide +kernel
private theorem c4195_ell   : LeafEll 4195    := by decide +kernel
private theorem c4195_nsq   : NSqChkSq 4195   := by decide +kernel
private theorem c4195_har   : HArithChkSq 4195 := by decide +kernel
private theorem c4195_r     : LeafR 4195      := by decide +kernel
private theorem c4195_e'    : LeafE' 4195     := by decide +kernel
private theorem c4195_f1    : LeafF1 4195     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4195_s2    : S2ChkSq 4195    := by decide +kernel
private theorem c4195_s3    : S3ChkSq 4195    := by decide +kernel
private theorem c4195_iso   : LeafIso 4195    := by decide +kernel
private theorem c4195_nof2  : NoF2ChkSq 4195  := by decide +kernel
private theorem c4195_nof3  : NoF3ChkSq 4195  := by decide +kernel
private theorem c4195_nof4z : NoF4zChkSq 4195 := by decide +kernel
theorem C'_4195 : C' 4195 :=
  ⟨c4195_sqf, c4195_range, c4195_ell, leafNSq_of_sq c4195_nsq, leafHAr_of_sq c4195_har,
   c4195_r, c4195_e', c4195_f1, leafS2_of_sq c4195_s2, leafS3_of_sq c4195_s3,
   c4195_iso, leafR8_of_sq c4195_nof2 c4195_nof3 c4195_nof4z⟩
theorem not_tile'_4195 (D : CongruentDissection 4195) : False :=
  not_tile_of_conditions' 4195 C'_4195 D

end Erdos634.Draft.AllN2

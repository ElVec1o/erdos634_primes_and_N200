/- AllN2Check223: N = 4207, 4209, 4211, 4213, 4219
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4207_sqf   : LeafSqf 4207   := by decide +kernel
private theorem c4207_range : LeafRange 4207  := by decide +kernel
private theorem c4207_ell   : LeafEll 4207    := by decide +kernel
private theorem c4207_nsq   : NSqChkSq 4207   := by decide +kernel
private theorem c4207_har   : HArithChkSq 4207 := by decide +kernel
private theorem c4207_r     : LeafR 4207      := by decide +kernel
private theorem c4207_e'    : LeafE' 4207     := by decide +kernel
private theorem c4207_f1    : LeafF1 4207     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4207_s2    : S2ChkSq 4207    := by decide +kernel
private theorem c4207_s3    : S3ChkSq 4207    := by decide +kernel
private theorem c4207_iso   : LeafIso 4207    := by decide +kernel
private theorem c4207_nof2  : NoF2ChkSq 4207  := by decide +kernel
private theorem c4207_nof3  : NoF3ChkSq 4207  := by decide +kernel
private theorem c4207_nof4z : NoF4zChkSq 4207 := by decide +kernel
theorem C'_4207 : C' 4207 :=
  ⟨c4207_sqf, c4207_range, c4207_ell, leafNSq_of_sq c4207_nsq, leafHAr_of_sq c4207_har,
   c4207_r, c4207_e', c4207_f1, leafS2_of_sq c4207_s2, leafS3_of_sq c4207_s3,
   c4207_iso, leafR8_of_sq c4207_nof2 c4207_nof3 c4207_nof4z⟩
theorem not_tile'_4207 (D : CongruentDissection 4207) : False :=
  not_tile_of_conditions' 4207 C'_4207 D

private theorem c4209_sqf   : LeafSqf 4209   := by decide +kernel
private theorem c4209_range : LeafRange 4209  := by decide +kernel
private theorem c4209_ell   : LeafEll 4209    := by decide +kernel
private theorem c4209_nsq   : NSqChkSq 4209   := by decide +kernel
private theorem c4209_har   : HArithChkSq 4209 := by decide +kernel
private theorem c4209_r     : LeafR 4209      := by decide +kernel
private theorem c4209_e'    : LeafE' 4209     := by decide +kernel
private theorem c4209_f1    : LeafF1 4209     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4209_s2    : S2ChkSq 4209    := by decide +kernel
private theorem c4209_s3    : S3ChkSq 4209    := by decide +kernel
private theorem c4209_iso   : LeafIso 4209    := by decide +kernel
private theorem c4209_nof2  : NoF2ChkSq 4209  := by decide +kernel
private theorem c4209_nof3  : NoF3ChkSq 4209  := by decide +kernel
private theorem c4209_nof4z : NoF4zChkSq 4209 := by decide +kernel
theorem C'_4209 : C' 4209 :=
  ⟨c4209_sqf, c4209_range, c4209_ell, leafNSq_of_sq c4209_nsq, leafHAr_of_sq c4209_har,
   c4209_r, c4209_e', c4209_f1, leafS2_of_sq c4209_s2, leafS3_of_sq c4209_s3,
   c4209_iso, leafR8_of_sq c4209_nof2 c4209_nof3 c4209_nof4z⟩
theorem not_tile'_4209 (D : CongruentDissection 4209) : False :=
  not_tile_of_conditions' 4209 C'_4209 D

private theorem c4211_sqf   : LeafSqf 4211   := by decide +kernel
private theorem c4211_range : LeafRange 4211  := by decide +kernel
private theorem c4211_ell   : LeafEll 4211    := by decide +kernel
private theorem c4211_nsq   : NSqChkSq 4211   := by decide +kernel
private theorem c4211_har   : HArithChkSq 4211 := by decide +kernel
private theorem c4211_r     : LeafR 4211      := by decide +kernel
private theorem c4211_e'    : LeafE' 4211     := by decide +kernel
private theorem c4211_f1    : LeafF1 4211     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4211_s2    : S2ChkSq 4211    := by decide +kernel
private theorem c4211_s3    : S3ChkSq 4211    := by decide +kernel
private theorem c4211_iso   : LeafIso 4211    := by decide +kernel
private theorem c4211_nof2  : NoF2ChkSq 4211  := by decide +kernel
private theorem c4211_nof3  : NoF3ChkSq 4211  := by decide +kernel
private theorem c4211_nof4z : NoF4zChkSq 4211 := by decide +kernel
theorem C'_4211 : C' 4211 :=
  ⟨c4211_sqf, c4211_range, c4211_ell, leafNSq_of_sq c4211_nsq, leafHAr_of_sq c4211_har,
   c4211_r, c4211_e', c4211_f1, leafS2_of_sq c4211_s2, leafS3_of_sq c4211_s3,
   c4211_iso, leafR8_of_sq c4211_nof2 c4211_nof3 c4211_nof4z⟩
theorem not_tile'_4211 (D : CongruentDissection 4211) : False :=
  not_tile_of_conditions' 4211 C'_4211 D

private theorem c4213_sqf   : LeafSqf 4213   := by decide +kernel
private theorem c4213_range : LeafRange 4213  := by decide +kernel
private theorem c4213_ell   : LeafEll 4213    := by decide +kernel
private theorem c4213_nsq   : NSqChkSq 4213   := by decide +kernel
private theorem c4213_har   : HArithChkSq 4213 := by decide +kernel
private theorem c4213_r     : LeafR 4213      := by decide +kernel
private theorem c4213_e'    : LeafE' 4213     := by decide +kernel
private theorem c4213_f1    : LeafF1 4213     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4213_s2    : S2ChkSq 4213    := by decide +kernel
private theorem c4213_s3    : S3ChkSq 4213    := by decide +kernel
private theorem c4213_iso   : LeafIso 4213    := by decide +kernel
private theorem c4213_nof2  : NoF2ChkSq 4213  := by decide +kernel
private theorem c4213_nof3  : NoF3ChkSq 4213  := by decide +kernel
private theorem c4213_nof4z : NoF4zChkSq 4213 := by decide +kernel
theorem C'_4213 : C' 4213 :=
  ⟨c4213_sqf, c4213_range, c4213_ell, leafNSq_of_sq c4213_nsq, leafHAr_of_sq c4213_har,
   c4213_r, c4213_e', c4213_f1, leafS2_of_sq c4213_s2, leafS3_of_sq c4213_s3,
   c4213_iso, leafR8_of_sq c4213_nof2 c4213_nof3 c4213_nof4z⟩
theorem not_tile'_4213 (D : CongruentDissection 4213) : False :=
  not_tile_of_conditions' 4213 C'_4213 D

private theorem c4219_sqf   : LeafSqf 4219   := by decide +kernel
private theorem c4219_range : LeafRange 4219  := by decide +kernel
private theorem c4219_ell   : LeafEll 4219    := by decide +kernel
private theorem c4219_nsq   : NSqChkSq 4219   := by decide +kernel
private theorem c4219_har   : HArithChkSq 4219 := by decide +kernel
private theorem c4219_r     : LeafR 4219      := by decide +kernel
private theorem c4219_e'    : LeafE' 4219     := by decide +kernel
private theorem c4219_f1    : LeafF1 4219     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4219_s2    : S2ChkSq 4219    := by decide +kernel
private theorem c4219_s3    : S3ChkSq 4219    := by decide +kernel
private theorem c4219_iso   : LeafIso 4219    := by decide +kernel
private theorem c4219_nof2  : NoF2ChkSq 4219  := by decide +kernel
private theorem c4219_nof3  : NoF3ChkSq 4219  := by decide +kernel
private theorem c4219_nof4z : NoF4zChkSq 4219 := by decide +kernel
theorem C'_4219 : C' 4219 :=
  ⟨c4219_sqf, c4219_range, c4219_ell, leafNSq_of_sq c4219_nsq, leafHAr_of_sq c4219_har,
   c4219_r, c4219_e', c4219_f1, leafS2_of_sq c4219_s2, leafS3_of_sq c4219_s3,
   c4219_iso, leafR8_of_sq c4219_nof2 c4219_nof3 c4219_nof4z⟩
theorem not_tile'_4219 (D : CongruentDissection 4219) : False :=
  not_tile_of_conditions' 4219 C'_4219 D

end Erdos634.Draft.AllN2

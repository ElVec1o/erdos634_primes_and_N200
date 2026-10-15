/- AllN2Check10: N = 213, 219
   Squarefree exclusions via C' with sqrt-bounded checks (Wave-2 OOM fix). -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c213_sqf   : LeafSqf 213   := by decide +kernel
private theorem c213_range : LeafRange 213  := by decide +kernel
private theorem c213_ell   : LeafEll 213    := by decide +kernel
private theorem c213_nsq   : NSqChkSq 213   := by decide +kernel
private theorem c213_har   : HArithChkSq 213 := by decide +kernel
private theorem c213_r     : LeafR 213      := by decide +kernel
private theorem c213_e'    : LeafE' 213     := by decide +kernel
private theorem c213_f1    : LeafF1 213     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c213_s2    : S2ChkSq 213    := by decide +kernel
private theorem c213_s3    : S3ChkSq 213    := by decide +kernel
private theorem c213_iso   : LeafIso 213    := by decide +kernel
private theorem c213_nof2  : NoF2ChkSq 213  := by decide +kernel
private theorem c213_nof3  : NoF3ChkSq 213  := by decide +kernel
private theorem c213_nof4z : NoF4zChkSq 213 := by decide +kernel
theorem C'_213 : C' 213 :=
  ⟨c213_sqf, c213_range, c213_ell, leafNSq_of_sq c213_nsq, leafHAr_of_sq c213_har,
   c213_r, c213_e', c213_f1, leafS2_of_sq c213_s2, leafS3_of_sq c213_s3,
   c213_iso, leafR8_of_sq c213_nof2 c213_nof3 c213_nof4z⟩
theorem not_tile'_213 (D : CongruentDissection 213) : False :=
  not_tile_of_conditions' 213 C'_213 D

private theorem c219_sqf   : LeafSqf 219   := by decide +kernel
private theorem c219_range : LeafRange 219  := by decide +kernel
private theorem c219_ell   : LeafEll 219    := by decide +kernel
private theorem c219_nsq   : NSqChkSq 219   := by decide +kernel
private theorem c219_har   : HArithChkSq 219 := by decide +kernel
private theorem c219_r     : LeafR 219      := by decide +kernel
private theorem c219_e'    : LeafE' 219     := by decide +kernel
private theorem c219_f1    : LeafF1 219     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c219_s2    : S2ChkSq 219    := by decide +kernel
private theorem c219_s3    : S3ChkSq 219    := by decide +kernel
private theorem c219_iso   : LeafIso 219    := by decide +kernel
private theorem c219_nof2  : NoF2ChkSq 219  := by decide +kernel
private theorem c219_nof3  : NoF3ChkSq 219  := by decide +kernel
private theorem c219_nof4z : NoF4zChkSq 219 := by decide +kernel
theorem C'_219 : C' 219 :=
  ⟨c219_sqf, c219_range, c219_ell, leafNSq_of_sq c219_nsq, leafHAr_of_sq c219_har,
   c219_r, c219_e', c219_f1, leafS2_of_sq c219_s2, leafS3_of_sq c219_s3,
   c219_iso, leafR8_of_sq c219_nof2 c219_nof3 c219_nof4z⟩
theorem not_tile'_219 (D : CongruentDissection 219) : False :=
  not_tile_of_conditions' 219 C'_219 D

end Erdos634.Draft.AllN2

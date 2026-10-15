/- AllN2Check287: N = 4997, 4999
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4997_sqf   : LeafSqf 4997   := by decide +kernel
private theorem c4997_range : LeafRange 4997  := by decide +kernel
private theorem c4997_ell   : LeafEll 4997    := by decide +kernel
private theorem c4997_nsq   : NSqChkSq 4997   := by decide +kernel
private theorem c4997_har   : HArithChkSq 4997 := by decide +kernel
private theorem c4997_r     : LeafR 4997      := by decide +kernel
private theorem c4997_e'    : LeafE' 4997     := by decide +kernel
private theorem c4997_f1    : LeafF1 4997     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4997_s2    : S2ChkSq 4997    := by decide +kernel
private theorem c4997_s3    : S3ChkSq 4997    := by decide +kernel
private theorem c4997_iso   : LeafIso 4997    := by decide +kernel
private theorem c4997_nof2  : NoF2ChkSq 4997  := by decide +kernel
private theorem c4997_nof3  : NoF3ChkSq 4997  := by decide +kernel
private theorem c4997_nof4z : NoF4zChkSq 4997 := by decide +kernel
theorem C'_4997 : C' 4997 :=
  ⟨c4997_sqf, c4997_range, c4997_ell, leafNSq_of_sq c4997_nsq, leafHAr_of_sq c4997_har,
   c4997_r, c4997_e', c4997_f1, leafS2_of_sq c4997_s2, leafS3_of_sq c4997_s3,
   c4997_iso, leafR8_of_sq c4997_nof2 c4997_nof3 c4997_nof4z⟩
theorem not_tile'_4997 (D : CongruentDissection 4997) : False :=
  not_tile_of_conditions' 4997 C'_4997 D

private theorem c4999_sqf   : LeafSqf 4999   := by decide +kernel
private theorem c4999_range : LeafRange 4999  := by decide +kernel
private theorem c4999_ell   : LeafEll 4999    := by decide +kernel
private theorem c4999_nsq   : NSqChkSq 4999   := by decide +kernel
private theorem c4999_har   : HArithChkSq 4999 := by decide +kernel
private theorem c4999_r     : LeafR 4999      := by decide +kernel
private theorem c4999_e'    : LeafE' 4999     := by decide +kernel
private theorem c4999_f1    : LeafF1 4999     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4999_s2    : S2ChkSq 4999    := by decide +kernel
private theorem c4999_s3    : S3ChkSq 4999    := by decide +kernel
private theorem c4999_iso   : LeafIso 4999    := by decide +kernel
private theorem c4999_nof2  : NoF2ChkSq 4999  := by decide +kernel
private theorem c4999_nof3  : NoF3ChkSq 4999  := by decide +kernel
private theorem c4999_nof4z : NoF4zChkSq 4999 := by decide +kernel
theorem C'_4999 : C' 4999 :=
  ⟨c4999_sqf, c4999_range, c4999_ell, leafNSq_of_sq c4999_nsq, leafHAr_of_sq c4999_har,
   c4999_r, c4999_e', c4999_f1, leafS2_of_sq c4999_s2, leafS3_of_sq c4999_s3,
   c4999_iso, leafR8_of_sq c4999_nof2 c4999_nof3 c4999_nof4z⟩
theorem not_tile'_4999 (D : CongruentDissection 4999) : False :=
  not_tile_of_conditions' 4999 C'_4999 D

end Erdos634.Draft.AllN2

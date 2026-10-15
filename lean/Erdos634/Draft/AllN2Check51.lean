/- AllN2Check51: N = 1991
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1991_sqf   : LeafSqf 1991   := by decide +kernel
private theorem c1991_range : LeafRange 1991  := by decide +kernel
private theorem c1991_ell   : LeafEll 1991    := by decide +kernel
private theorem c1991_nsq   : NSqChkSq 1991   := by decide +kernel
private theorem c1991_har   : HArithChkSq 1991 := by decide +kernel
private theorem c1991_r     : LeafR 1991      := by decide +kernel
private theorem c1991_e'    : LeafE' 1991     := by decide +kernel
private theorem c1991_f1    : LeafF1 1991     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1991_s2    : S2ChkSq 1991    := by decide +kernel
private theorem c1991_s3    : S3ChkSq 1991    := by decide +kernel
private theorem c1991_iso   : LeafIso 1991    := by decide +kernel
private theorem c1991_nof2  : NoF2ChkSq 1991  := by decide +kernel
private theorem c1991_nof3  : NoF3ChkSq 1991  := by decide +kernel
private theorem c1991_nof4z : NoF4zChkSq 1991 := by decide +kernel
theorem C'_1991 : C' 1991 :=
  ⟨c1991_sqf, c1991_range, c1991_ell, leafNSq_of_sq c1991_nsq, leafHAr_of_sq c1991_har,
   c1991_r, c1991_e', c1991_f1, leafS2_of_sq c1991_s2, leafS3_of_sq c1991_s3,
   c1991_iso, leafR8_of_sq c1991_nof2 c1991_nof3 c1991_nof4z⟩
theorem not_tile'_1991 (D : CongruentDissection 1991) : False :=
  not_tile_of_conditions' 1991 C'_1991 D

end Erdos634.Draft.AllN2

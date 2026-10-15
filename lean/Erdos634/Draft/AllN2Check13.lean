/- AllN2Check13: N = 201
   Squarefree exclusions via C' with sqrt-bounded checks (Wave-2 OOM fix). -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c201_sqf   : LeafSqf 201   := by decide +kernel
private theorem c201_range : LeafRange 201  := by decide +kernel
private theorem c201_ell   : LeafEll 201    := by decide +kernel
private theorem c201_nsq   : NSqChkSq 201   := by decide +kernel
private theorem c201_har   : HArithChkSq 201 := by decide +kernel
private theorem c201_r     : LeafR 201      := by decide +kernel
private theorem c201_e'    : LeafE' 201     := by decide +kernel
private theorem c201_f1    : LeafF1 201     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c201_s2    : S2ChkSq 201    := by decide +kernel
private theorem c201_s3    : S3ChkSq 201    := by decide +kernel
private theorem c201_iso   : LeafIso 201    := by decide +kernel
private theorem c201_nof2  : NoF2ChkSq 201  := by decide +kernel
private theorem c201_nof3  : NoF3ChkSq 201  := by decide +kernel
private theorem c201_nof4z : NoF4zChkSq 201 := by decide +kernel
theorem C'_201 : C' 201 :=
  ⟨c201_sqf, c201_range, c201_ell, leafNSq_of_sq c201_nsq, leafHAr_of_sq c201_har,
   c201_r, c201_e', c201_f1, leafS2_of_sq c201_s2, leafS3_of_sq c201_s3,
   c201_iso, leafR8_of_sq c201_nof2 c201_nof3 c201_nof4z⟩
theorem not_tile'_201 (D : CongruentDissection 201) : False :=
  not_tile_of_conditions' 201 C'_201 D

end Erdos634.Draft.AllN2

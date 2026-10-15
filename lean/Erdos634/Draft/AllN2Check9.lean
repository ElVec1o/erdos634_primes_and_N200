/- AllN2Check9: N = 183
   Squarefree exclusions via C' with sqrt-bounded checks (Wave-2 OOM fix). -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c183_sqf   : LeafSqf 183   := by decide +kernel
private theorem c183_range : LeafRange 183  := by decide +kernel
private theorem c183_ell   : LeafEll 183    := by decide +kernel
private theorem c183_nsq   : NSqChkSq 183   := by decide +kernel
private theorem c183_har   : HArithChkSq 183 := by decide +kernel
private theorem c183_r     : LeafR 183      := by decide +kernel
private theorem c183_e'    : LeafE' 183     := by decide +kernel
private theorem c183_f1    : LeafF1 183     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c183_s2    : S2ChkSq 183    := by decide +kernel
private theorem c183_s3    : S3ChkSq 183    := by decide +kernel
private theorem c183_iso   : LeafIso 183    := by decide +kernel
private theorem c183_nof2  : NoF2ChkSq 183  := by decide +kernel
private theorem c183_nof3  : NoF3ChkSq 183  := by decide +kernel
private theorem c183_nof4z : NoF4zChkSq 183 := by decide +kernel
theorem C'_183 : C' 183 :=
  ⟨c183_sqf, c183_range, c183_ell, leafNSq_of_sq c183_nsq, leafHAr_of_sq c183_har,
   c183_r, c183_e', c183_f1, leafS2_of_sq c183_s2, leafS3_of_sq c183_s3,
   c183_iso, leafR8_of_sq c183_nof2 c183_nof3 c183_nof4z⟩
theorem not_tile'_183 (D : CongruentDissection 183) : False :=
  not_tile_of_conditions' 183 C'_183 D

end Erdos634.Draft.AllN2

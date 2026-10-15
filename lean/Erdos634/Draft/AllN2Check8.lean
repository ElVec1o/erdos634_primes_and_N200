/- AllN2Check8: N = 165, 177
   Squarefree exclusions via C' with sqrt-bounded checks (Wave-2 OOM fix). -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c165_sqf   : LeafSqf 165   := by decide +kernel
private theorem c165_range : LeafRange 165  := by decide +kernel
private theorem c165_ell   : LeafEll 165    := by decide +kernel
private theorem c165_nsq   : NSqChkSq 165   := by decide +kernel
private theorem c165_har   : HArithChkSq 165 := by decide +kernel
private theorem c165_r     : LeafR 165      := by decide +kernel
private theorem c165_e'    : LeafE' 165     := by decide +kernel
private theorem c165_f1    : LeafF1 165     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c165_s2    : S2ChkSq 165    := by decide +kernel
private theorem c165_s3    : S3ChkSq 165    := by decide +kernel
private theorem c165_iso   : LeafIso 165    := by decide +kernel
private theorem c165_nof2  : NoF2ChkSq 165  := by decide +kernel
private theorem c165_nof3  : NoF3ChkSq 165  := by decide +kernel
private theorem c165_nof4z : NoF4zChkSq 165 := by decide +kernel
theorem C'_165 : C' 165 :=
  ⟨c165_sqf, c165_range, c165_ell, leafNSq_of_sq c165_nsq, leafHAr_of_sq c165_har,
   c165_r, c165_e', c165_f1, leafS2_of_sq c165_s2, leafS3_of_sq c165_s3,
   c165_iso, leafR8_of_sq c165_nof2 c165_nof3 c165_nof4z⟩
theorem not_tile'_165 (D : CongruentDissection 165) : False :=
  not_tile_of_conditions' 165 C'_165 D

private theorem c177_sqf   : LeafSqf 177   := by decide +kernel
private theorem c177_range : LeafRange 177  := by decide +kernel
private theorem c177_ell   : LeafEll 177    := by decide +kernel
private theorem c177_nsq   : NSqChkSq 177   := by decide +kernel
private theorem c177_har   : HArithChkSq 177 := by decide +kernel
private theorem c177_r     : LeafR 177      := by decide +kernel
private theorem c177_e'    : LeafE' 177     := by decide +kernel
private theorem c177_f1    : LeafF1 177     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c177_s2    : S2ChkSq 177    := by decide +kernel
private theorem c177_s3    : S3ChkSq 177    := by decide +kernel
private theorem c177_iso   : LeafIso 177    := by decide +kernel
private theorem c177_nof2  : NoF2ChkSq 177  := by decide +kernel
private theorem c177_nof3  : NoF3ChkSq 177  := by decide +kernel
private theorem c177_nof4z : NoF4zChkSq 177 := by decide +kernel
theorem C'_177 : C' 177 :=
  ⟨c177_sqf, c177_range, c177_ell, leafNSq_of_sq c177_nsq, leafHAr_of_sq c177_har,
   c177_r, c177_e', c177_f1, leafS2_of_sq c177_s2, leafS3_of_sq c177_s3,
   c177_iso, leafR8_of_sq c177_nof2 c177_nof3 c177_nof4z⟩
theorem not_tile'_177 (D : CongruentDissection 177) : False :=
  not_tile_of_conditions' 177 C'_177 D

end Erdos634.Draft.AllN2

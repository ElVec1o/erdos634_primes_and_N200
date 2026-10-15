/- AllN2Check12: N = 195
   Squarefree exclusions via C' with sqrt-bounded checks (Wave-2 OOM fix). -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c195_sqf   : LeafSqf 195   := by decide +kernel
private theorem c195_range : LeafRange 195  := by decide +kernel
private theorem c195_ell   : LeafEll 195    := by decide +kernel
private theorem c195_nsq   : NSqChkSq 195   := by decide +kernel
private theorem c195_har   : HArithChkSq 195 := by decide +kernel
private theorem c195_r     : LeafR 195      := by decide +kernel
private theorem c195_e'    : LeafE' 195     := by decide +kernel
private theorem c195_f1    : LeafF1 195     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c195_s2    : S2ChkSq 195    := by decide +kernel
private theorem c195_s3    : S3ChkSq 195    := by decide +kernel
private theorem c195_iso   : LeafIso 195    := by decide +kernel
private theorem c195_nof2  : NoF2ChkSq 195  := by decide +kernel
private theorem c195_nof3  : NoF3ChkSq 195  := by decide +kernel
private theorem c195_nof4z : NoF4zChkSq 195 := by decide +kernel
theorem C'_195 : C' 195 :=
  ⟨c195_sqf, c195_range, c195_ell, leafNSq_of_sq c195_nsq, leafHAr_of_sq c195_har,
   c195_r, c195_e', c195_f1, leafS2_of_sq c195_s2, leafS3_of_sq c195_s3,
   c195_iso, leafR8_of_sq c195_nof2 c195_nof3 c195_nof4z⟩
theorem not_tile'_195 (D : CongruentDissection 195) : False :=
  not_tile_of_conditions' 195 C'_195 D

end Erdos634.Draft.AllN2

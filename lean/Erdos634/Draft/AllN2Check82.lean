/- AllN2Check82: N = 2398, 2399
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2398_sqf   : LeafSqf 2398   := by decide +kernel
private theorem c2398_range : LeafRange 2398  := by decide +kernel
private theorem c2398_ell   : LeafEll 2398    := by decide +kernel
private theorem c2398_nsq   : NSqChkSq 2398   := by decide +kernel
private theorem c2398_har   : HArithChkSq 2398 := by decide +kernel
private theorem c2398_r     : LeafR 2398      := by decide +kernel
private theorem c2398_e'    : LeafE' 2398     := by decide +kernel
private theorem c2398_f1    : LeafF1 2398     := Or.inl (by decide)
private theorem c2398_s2    : S2ChkSq 2398    := by decide +kernel
private theorem c2398_s3    : S3ChkSq 2398    := by decide +kernel
private theorem c2398_iso   : LeafIso 2398    := by decide +kernel
private theorem c2398_nof2  : NoF2ChkSq 2398  := by decide +kernel
private theorem c2398_nof3  : NoF3ChkSq 2398  := by decide +kernel
private theorem c2398_nof4z : NoF4zChkSq 2398 := by decide +kernel
theorem C'_2398 : C' 2398 :=
  ⟨c2398_sqf, c2398_range, c2398_ell, leafNSq_of_sq c2398_nsq, leafHAr_of_sq c2398_har,
   c2398_r, c2398_e', c2398_f1, leafS2_of_sq c2398_s2, leafS3_of_sq c2398_s3,
   c2398_iso, leafR8_of_sq c2398_nof2 c2398_nof3 c2398_nof4z⟩
theorem not_tile'_2398 (D : CongruentDissection 2398) : False :=
  not_tile_of_conditions' 2398 C'_2398 D

private theorem c2399_sqf   : LeafSqf 2399   := by decide +kernel
private theorem c2399_range : LeafRange 2399  := by decide +kernel
private theorem c2399_ell   : LeafEll 2399    := by decide +kernel
private theorem c2399_nsq   : NSqChkSq 2399   := by decide +kernel
private theorem c2399_har   : HArithChkSq 2399 := by decide +kernel
private theorem c2399_r     : LeafR 2399      := by decide +kernel
private theorem c2399_e'    : LeafE' 2399     := by decide +kernel
private theorem c2399_f1    : LeafF1 2399     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2399_s2    : S2ChkSq 2399    := by decide +kernel
private theorem c2399_s3    : S3ChkSq 2399    := by decide +kernel
private theorem c2399_iso   : LeafIso 2399    := by decide +kernel
private theorem c2399_nof2  : NoF2ChkSq 2399  := by decide +kernel
private theorem c2399_nof3  : NoF3ChkSq 2399  := by decide +kernel
private theorem c2399_nof4z : NoF4zChkSq 2399 := by decide +kernel
theorem C'_2399 : C' 2399 :=
  ⟨c2399_sqf, c2399_range, c2399_ell, leafNSq_of_sq c2399_nsq, leafHAr_of_sq c2399_har,
   c2399_r, c2399_e', c2399_f1, leafS2_of_sq c2399_s2, leafS3_of_sq c2399_s3,
   c2399_iso, leafR8_of_sq c2399_nof2 c2399_nof3 c2399_nof4z⟩
theorem not_tile'_2399 (D : CongruentDissection 2399) : False :=
  not_tile_of_conditions' 2399 C'_2399 D

end Erdos634.Draft.AllN2

/- AllN2Check98: N = 2585, 2586, 2587, 2589, 2590
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2585_sqf   : LeafSqf 2585   := by decide +kernel
private theorem c2585_range : LeafRange 2585  := by decide +kernel
private theorem c2585_ell   : LeafEll 2585    := by decide +kernel
private theorem c2585_nsq   : NSqChkSq 2585   := by decide +kernel
private theorem c2585_har   : HArithChkSq 2585 := by decide +kernel
private theorem c2585_r     : LeafR 2585      := by decide +kernel
private theorem c2585_e'    : LeafE' 2585     := by decide +kernel
private theorem c2585_f1    : LeafF1 2585     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2585_s2    : S2ChkSq 2585    := by decide +kernel
private theorem c2585_s3    : S3ChkSq 2585    := by decide +kernel
private theorem c2585_iso   : LeafIso 2585    := by decide +kernel
private theorem c2585_nof2  : NoF2ChkSq 2585  := by decide +kernel
private theorem c2585_nof3  : NoF3ChkSq 2585  := by decide +kernel
private theorem c2585_nof4z : NoF4zChkSq 2585 := by decide +kernel
theorem C'_2585 : C' 2585 :=
  ⟨c2585_sqf, c2585_range, c2585_ell, leafNSq_of_sq c2585_nsq, leafHAr_of_sq c2585_har,
   c2585_r, c2585_e', c2585_f1, leafS2_of_sq c2585_s2, leafS3_of_sq c2585_s3,
   c2585_iso, leafR8_of_sq c2585_nof2 c2585_nof3 c2585_nof4z⟩
theorem not_tile'_2585 (D : CongruentDissection 2585) : False :=
  not_tile_of_conditions' 2585 C'_2585 D

private theorem c2586_sqf   : LeafSqf 2586   := by decide +kernel
private theorem c2586_range : LeafRange 2586  := by decide +kernel
private theorem c2586_ell   : LeafEll 2586    := by decide +kernel
private theorem c2586_nsq   : NSqChkSq 2586   := by decide +kernel
private theorem c2586_har   : HArithChkSq 2586 := by decide +kernel
private theorem c2586_r     : LeafR 2586      := by decide +kernel
private theorem c2586_e'    : LeafE' 2586     := by decide +kernel
private theorem c2586_f1    : LeafF1 2586     := Or.inl (by decide)
private theorem c2586_s2    : S2ChkSq 2586    := by decide +kernel
private theorem c2586_s3    : S3ChkSq 2586    := by decide +kernel
private theorem c2586_iso   : LeafIso 2586    := by decide +kernel
private theorem c2586_nof2  : NoF2ChkSq 2586  := by decide +kernel
private theorem c2586_nof3  : NoF3ChkSq 2586  := by decide +kernel
private theorem c2586_nof4z : NoF4zChkSq 2586 := by decide +kernel
theorem C'_2586 : C' 2586 :=
  ⟨c2586_sqf, c2586_range, c2586_ell, leafNSq_of_sq c2586_nsq, leafHAr_of_sq c2586_har,
   c2586_r, c2586_e', c2586_f1, leafS2_of_sq c2586_s2, leafS3_of_sq c2586_s3,
   c2586_iso, leafR8_of_sq c2586_nof2 c2586_nof3 c2586_nof4z⟩
theorem not_tile'_2586 (D : CongruentDissection 2586) : False :=
  not_tile_of_conditions' 2586 C'_2586 D

private theorem c2587_sqf   : LeafSqf 2587   := by decide +kernel
private theorem c2587_range : LeafRange 2587  := by decide +kernel
private theorem c2587_ell   : LeafEll 2587    := by decide +kernel
private theorem c2587_nsq   : NSqChkSq 2587   := by decide +kernel
private theorem c2587_har   : HArithChkSq 2587 := by decide +kernel
private theorem c2587_r     : LeafR 2587      := by decide +kernel
private theorem c2587_e'    : LeafE' 2587     := by decide +kernel
private theorem c2587_f1    : LeafF1 2587     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2587_s2    : S2ChkSq 2587    := by decide +kernel
private theorem c2587_s3    : S3ChkSq 2587    := by decide +kernel
private theorem c2587_iso   : LeafIso 2587    := by decide +kernel
private theorem c2587_nof2  : NoF2ChkSq 2587  := by decide +kernel
private theorem c2587_nof3  : NoF3ChkSq 2587  := by decide +kernel
private theorem c2587_nof4z : NoF4zChkSq 2587 := by decide +kernel
theorem C'_2587 : C' 2587 :=
  ⟨c2587_sqf, c2587_range, c2587_ell, leafNSq_of_sq c2587_nsq, leafHAr_of_sq c2587_har,
   c2587_r, c2587_e', c2587_f1, leafS2_of_sq c2587_s2, leafS3_of_sq c2587_s3,
   c2587_iso, leafR8_of_sq c2587_nof2 c2587_nof3 c2587_nof4z⟩
theorem not_tile'_2587 (D : CongruentDissection 2587) : False :=
  not_tile_of_conditions' 2587 C'_2587 D

private theorem c2589_sqf   : LeafSqf 2589   := by decide +kernel
private theorem c2589_range : LeafRange 2589  := by decide +kernel
private theorem c2589_ell   : LeafEll 2589    := by decide +kernel
private theorem c2589_nsq   : NSqChkSq 2589   := by decide +kernel
private theorem c2589_har   : HArithChkSq 2589 := by decide +kernel
private theorem c2589_r     : LeafR 2589      := by decide +kernel
private theorem c2589_e'    : LeafE' 2589     := by decide +kernel
private theorem c2589_f1    : LeafF1 2589     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2589_s2    : S2ChkSq 2589    := by decide +kernel
private theorem c2589_s3    : S3ChkSq 2589    := by decide +kernel
private theorem c2589_iso   : LeafIso 2589    := by decide +kernel
private theorem c2589_nof2  : NoF2ChkSq 2589  := by decide +kernel
private theorem c2589_nof3  : NoF3ChkSq 2589  := by decide +kernel
private theorem c2589_nof4z : NoF4zChkSq 2589 := by decide +kernel
theorem C'_2589 : C' 2589 :=
  ⟨c2589_sqf, c2589_range, c2589_ell, leafNSq_of_sq c2589_nsq, leafHAr_of_sq c2589_har,
   c2589_r, c2589_e', c2589_f1, leafS2_of_sq c2589_s2, leafS3_of_sq c2589_s3,
   c2589_iso, leafR8_of_sq c2589_nof2 c2589_nof3 c2589_nof4z⟩
theorem not_tile'_2589 (D : CongruentDissection 2589) : False :=
  not_tile_of_conditions' 2589 C'_2589 D

private theorem c2590_sqf   : LeafSqf 2590   := by decide +kernel
private theorem c2590_range : LeafRange 2590  := by decide +kernel
private theorem c2590_ell   : LeafEll 2590    := by decide +kernel
private theorem c2590_nsq   : NSqChkSq 2590   := by decide +kernel
private theorem c2590_har   : HArithChkSq 2590 := by decide +kernel
private theorem c2590_r     : LeafR 2590      := by decide +kernel
private theorem c2590_e'    : LeafE' 2590     := by decide +kernel
private theorem c2590_f1    : LeafF1 2590     := Or.inl (by decide)
private theorem c2590_s2    : S2ChkSq 2590    := by decide +kernel
private theorem c2590_s3    : S3ChkSq 2590    := by decide +kernel
private theorem c2590_iso   : LeafIso 2590    := by decide +kernel
private theorem c2590_nof2  : NoF2ChkSq 2590  := by decide +kernel
private theorem c2590_nof3  : NoF3ChkSq 2590  := by decide +kernel
private theorem c2590_nof4z : NoF4zChkSq 2590 := by decide +kernel
theorem C'_2590 : C' 2590 :=
  ⟨c2590_sqf, c2590_range, c2590_ell, leafNSq_of_sq c2590_nsq, leafHAr_of_sq c2590_har,
   c2590_r, c2590_e', c2590_f1, leafS2_of_sq c2590_s2, leafS3_of_sq c2590_s3,
   c2590_iso, leafR8_of_sq c2590_nof2 c2590_nof3 c2590_nof4z⟩
theorem not_tile'_2590 (D : CongruentDissection 2590) : False :=
  not_tile_of_conditions' 2590 C'_2590 D

end Erdos634.Draft.AllN2

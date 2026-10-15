/- AllN2Check103: N = 2647, 2649, 2651, 2653, 2654
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2647_sqf   : LeafSqf 2647   := by decide +kernel
private theorem c2647_range : LeafRange 2647  := by decide +kernel
private theorem c2647_ell   : LeafEll 2647    := by decide +kernel
private theorem c2647_nsq   : NSqChkSq 2647   := by decide +kernel
private theorem c2647_har   : HArithChkSq 2647 := by decide +kernel
private theorem c2647_r     : LeafR 2647      := by decide +kernel
private theorem c2647_e'    : LeafE' 2647     := by decide +kernel
private theorem c2647_f1    : LeafF1 2647     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2647_s2    : S2ChkSq 2647    := by decide +kernel
private theorem c2647_s3    : S3ChkSq 2647    := by decide +kernel
private theorem c2647_iso   : LeafIso 2647    := by decide +kernel
private theorem c2647_nof2  : NoF2ChkSq 2647  := by decide +kernel
private theorem c2647_nof3  : NoF3ChkSq 2647  := by decide +kernel
private theorem c2647_nof4z : NoF4zChkSq 2647 := by decide +kernel
theorem C'_2647 : C' 2647 :=
  ⟨c2647_sqf, c2647_range, c2647_ell, leafNSq_of_sq c2647_nsq, leafHAr_of_sq c2647_har,
   c2647_r, c2647_e', c2647_f1, leafS2_of_sq c2647_s2, leafS3_of_sq c2647_s3,
   c2647_iso, leafR8_of_sq c2647_nof2 c2647_nof3 c2647_nof4z⟩
theorem not_tile'_2647 (D : CongruentDissection 2647) : False :=
  not_tile_of_conditions' 2647 C'_2647 D

private theorem c2649_sqf   : LeafSqf 2649   := by decide +kernel
private theorem c2649_range : LeafRange 2649  := by decide +kernel
private theorem c2649_ell   : LeafEll 2649    := by decide +kernel
private theorem c2649_nsq   : NSqChkSq 2649   := by decide +kernel
private theorem c2649_har   : HArithChkSq 2649 := by decide +kernel
private theorem c2649_r     : LeafR 2649      := by decide +kernel
private theorem c2649_e'    : LeafE' 2649     := by decide +kernel
private theorem c2649_f1    : LeafF1 2649     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2649_s2    : S2ChkSq 2649    := by decide +kernel
private theorem c2649_s3    : S3ChkSq 2649    := by decide +kernel
private theorem c2649_iso   : LeafIso 2649    := by decide +kernel
private theorem c2649_nof2  : NoF2ChkSq 2649  := by decide +kernel
private theorem c2649_nof3  : NoF3ChkSq 2649  := by decide +kernel
private theorem c2649_nof4z : NoF4zChkSq 2649 := by decide +kernel
theorem C'_2649 : C' 2649 :=
  ⟨c2649_sqf, c2649_range, c2649_ell, leafNSq_of_sq c2649_nsq, leafHAr_of_sq c2649_har,
   c2649_r, c2649_e', c2649_f1, leafS2_of_sq c2649_s2, leafS3_of_sq c2649_s3,
   c2649_iso, leafR8_of_sq c2649_nof2 c2649_nof3 c2649_nof4z⟩
theorem not_tile'_2649 (D : CongruentDissection 2649) : False :=
  not_tile_of_conditions' 2649 C'_2649 D

private theorem c2651_sqf   : LeafSqf 2651   := by decide +kernel
private theorem c2651_range : LeafRange 2651  := by decide +kernel
private theorem c2651_ell   : LeafEll 2651    := by decide +kernel
private theorem c2651_nsq   : NSqChkSq 2651   := by decide +kernel
private theorem c2651_har   : HArithChkSq 2651 := by decide +kernel
private theorem c2651_r     : LeafR 2651      := by decide +kernel
private theorem c2651_e'    : LeafE' 2651     := by decide +kernel
private theorem c2651_f1    : LeafF1 2651     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2651_s2    : S2ChkSq 2651    := by decide +kernel
private theorem c2651_s3    : S3ChkSq 2651    := by decide +kernel
private theorem c2651_iso   : LeafIso 2651    := by decide +kernel
private theorem c2651_nof2  : NoF2ChkSq 2651  := by decide +kernel
private theorem c2651_nof3  : NoF3ChkSq 2651  := by decide +kernel
private theorem c2651_nof4z : NoF4zChkSq 2651 := by decide +kernel
theorem C'_2651 : C' 2651 :=
  ⟨c2651_sqf, c2651_range, c2651_ell, leafNSq_of_sq c2651_nsq, leafHAr_of_sq c2651_har,
   c2651_r, c2651_e', c2651_f1, leafS2_of_sq c2651_s2, leafS3_of_sq c2651_s3,
   c2651_iso, leafR8_of_sq c2651_nof2 c2651_nof3 c2651_nof4z⟩
theorem not_tile'_2651 (D : CongruentDissection 2651) : False :=
  not_tile_of_conditions' 2651 C'_2651 D

private theorem c2653_sqf   : LeafSqf 2653   := by decide +kernel
private theorem c2653_range : LeafRange 2653  := by decide +kernel
private theorem c2653_ell   : LeafEll 2653    := by decide +kernel
private theorem c2653_nsq   : NSqChkSq 2653   := by decide +kernel
private theorem c2653_har   : HArithChkSq 2653 := by decide +kernel
private theorem c2653_r     : LeafR 2653      := by decide +kernel
private theorem c2653_e'    : LeafE' 2653     := by decide +kernel
private theorem c2653_f1    : LeafF1 2653     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2653_s2    : S2ChkSq 2653    := by decide +kernel
private theorem c2653_s3    : S3ChkSq 2653    := by decide +kernel
private theorem c2653_iso   : LeafIso 2653    := by decide +kernel
private theorem c2653_nof2  : NoF2ChkSq 2653  := by decide +kernel
private theorem c2653_nof3  : NoF3ChkSq 2653  := by decide +kernel
private theorem c2653_nof4z : NoF4zChkSq 2653 := by decide +kernel
theorem C'_2653 : C' 2653 :=
  ⟨c2653_sqf, c2653_range, c2653_ell, leafNSq_of_sq c2653_nsq, leafHAr_of_sq c2653_har,
   c2653_r, c2653_e', c2653_f1, leafS2_of_sq c2653_s2, leafS3_of_sq c2653_s3,
   c2653_iso, leafR8_of_sq c2653_nof2 c2653_nof3 c2653_nof4z⟩
theorem not_tile'_2653 (D : CongruentDissection 2653) : False :=
  not_tile_of_conditions' 2653 C'_2653 D

private theorem c2654_sqf   : LeafSqf 2654   := by decide +kernel
private theorem c2654_range : LeafRange 2654  := by decide +kernel
private theorem c2654_ell   : LeafEll 2654    := by decide +kernel
private theorem c2654_nsq   : NSqChkSq 2654   := by decide +kernel
private theorem c2654_har   : HArithChkSq 2654 := by decide +kernel
private theorem c2654_r     : LeafR 2654      := by decide +kernel
private theorem c2654_e'    : LeafE' 2654     := by decide +kernel
private theorem c2654_f1    : LeafF1 2654     := Or.inl (by decide)
private theorem c2654_s2    : S2ChkSq 2654    := by decide +kernel
private theorem c2654_s3    : S3ChkSq 2654    := by decide +kernel
private theorem c2654_iso   : LeafIso 2654    := by decide +kernel
private theorem c2654_nof2  : NoF2ChkSq 2654  := by decide +kernel
private theorem c2654_nof3  : NoF3ChkSq 2654  := by decide +kernel
private theorem c2654_nof4z : NoF4zChkSq 2654 := by decide +kernel
theorem C'_2654 : C' 2654 :=
  ⟨c2654_sqf, c2654_range, c2654_ell, leafNSq_of_sq c2654_nsq, leafHAr_of_sq c2654_har,
   c2654_r, c2654_e', c2654_f1, leafS2_of_sq c2654_s2, leafS3_of_sq c2654_s3,
   c2654_iso, leafR8_of_sq c2654_nof2 c2654_nof3 c2654_nof4z⟩
theorem not_tile'_2654 (D : CongruentDissection 2654) : False :=
  not_tile_of_conditions' 2654 C'_2654 D

end Erdos634.Draft.AllN2

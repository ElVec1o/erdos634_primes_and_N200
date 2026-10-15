/- AllN2Check107: N = 2698, 2699, 2702, 2707, 2710
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2698_sqf   : LeafSqf 2698   := by decide +kernel
private theorem c2698_range : LeafRange 2698  := by decide +kernel
private theorem c2698_ell   : LeafEll 2698    := by decide +kernel
private theorem c2698_nsq   : NSqChkSq 2698   := by decide +kernel
private theorem c2698_har   : HArithChkSq 2698 := by decide +kernel
private theorem c2698_r     : LeafR 2698      := by decide +kernel
private theorem c2698_e'    : LeafE' 2698     := by decide +kernel
private theorem c2698_f1    : LeafF1 2698     := Or.inl (by decide)
private theorem c2698_s2    : S2ChkSq 2698    := by decide +kernel
private theorem c2698_s3    : S3ChkSq 2698    := by decide +kernel
private theorem c2698_iso   : LeafIso 2698    := by decide +kernel
private theorem c2698_nof2  : NoF2ChkSq 2698  := by decide +kernel
private theorem c2698_nof3  : NoF3ChkSq 2698  := by decide +kernel
private theorem c2698_nof4z : NoF4zChkSq 2698 := by decide +kernel
theorem C'_2698 : C' 2698 :=
  ⟨c2698_sqf, c2698_range, c2698_ell, leafNSq_of_sq c2698_nsq, leafHAr_of_sq c2698_har,
   c2698_r, c2698_e', c2698_f1, leafS2_of_sq c2698_s2, leafS3_of_sq c2698_s3,
   c2698_iso, leafR8_of_sq c2698_nof2 c2698_nof3 c2698_nof4z⟩
theorem not_tile'_2698 (D : CongruentDissection 2698) : False :=
  not_tile_of_conditions' 2698 C'_2698 D

private theorem c2699_sqf   : LeafSqf 2699   := by decide +kernel
private theorem c2699_range : LeafRange 2699  := by decide +kernel
private theorem c2699_ell   : LeafEll 2699    := by decide +kernel
private theorem c2699_nsq   : NSqChkSq 2699   := by decide +kernel
private theorem c2699_har   : HArithChkSq 2699 := by decide +kernel
private theorem c2699_r     : LeafR 2699      := by decide +kernel
private theorem c2699_e'    : LeafE' 2699     := by decide +kernel
private theorem c2699_f1    : LeafF1 2699     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2699_s2    : S2ChkSq 2699    := by decide +kernel
private theorem c2699_s3    : S3ChkSq 2699    := by decide +kernel
private theorem c2699_iso   : LeafIso 2699    := by decide +kernel
private theorem c2699_nof2  : NoF2ChkSq 2699  := by decide +kernel
private theorem c2699_nof3  : NoF3ChkSq 2699  := by decide +kernel
private theorem c2699_nof4z : NoF4zChkSq 2699 := by decide +kernel
theorem C'_2699 : C' 2699 :=
  ⟨c2699_sqf, c2699_range, c2699_ell, leafNSq_of_sq c2699_nsq, leafHAr_of_sq c2699_har,
   c2699_r, c2699_e', c2699_f1, leafS2_of_sq c2699_s2, leafS3_of_sq c2699_s3,
   c2699_iso, leafR8_of_sq c2699_nof2 c2699_nof3 c2699_nof4z⟩
theorem not_tile'_2699 (D : CongruentDissection 2699) : False :=
  not_tile_of_conditions' 2699 C'_2699 D

private theorem c2702_sqf   : LeafSqf 2702   := by decide +kernel
private theorem c2702_range : LeafRange 2702  := by decide +kernel
private theorem c2702_ell   : LeafEll 2702    := by decide +kernel
private theorem c2702_nsq   : NSqChkSq 2702   := by decide +kernel
private theorem c2702_har   : HArithChkSq 2702 := by decide +kernel
private theorem c2702_r     : LeafR 2702      := by decide +kernel
private theorem c2702_e'    : LeafE' 2702     := by decide +kernel
private theorem c2702_f1    : LeafF1 2702     := Or.inl (by decide)
private theorem c2702_s2    : S2ChkSq 2702    := by decide +kernel
private theorem c2702_s3    : S3ChkSq 2702    := by decide +kernel
private theorem c2702_iso   : LeafIso 2702    := by decide +kernel
private theorem c2702_nof2  : NoF2ChkSq 2702  := by decide +kernel
private theorem c2702_nof3  : NoF3ChkSq 2702  := by decide +kernel
private theorem c2702_nof4z : NoF4zChkSq 2702 := by decide +kernel
theorem C'_2702 : C' 2702 :=
  ⟨c2702_sqf, c2702_range, c2702_ell, leafNSq_of_sq c2702_nsq, leafHAr_of_sq c2702_har,
   c2702_r, c2702_e', c2702_f1, leafS2_of_sq c2702_s2, leafS3_of_sq c2702_s3,
   c2702_iso, leafR8_of_sq c2702_nof2 c2702_nof3 c2702_nof4z⟩
theorem not_tile'_2702 (D : CongruentDissection 2702) : False :=
  not_tile_of_conditions' 2702 C'_2702 D

private theorem c2707_sqf   : LeafSqf 2707   := by decide +kernel
private theorem c2707_range : LeafRange 2707  := by decide +kernel
private theorem c2707_ell   : LeafEll 2707    := by decide +kernel
private theorem c2707_nsq   : NSqChkSq 2707   := by decide +kernel
private theorem c2707_har   : HArithChkSq 2707 := by decide +kernel
private theorem c2707_r     : LeafR 2707      := by decide +kernel
private theorem c2707_e'    : LeafE' 2707     := by decide +kernel
private theorem c2707_f1    : LeafF1 2707     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2707_s2    : S2ChkSq 2707    := by decide +kernel
private theorem c2707_s3    : S3ChkSq 2707    := by decide +kernel
private theorem c2707_iso   : LeafIso 2707    := by decide +kernel
private theorem c2707_nof2  : NoF2ChkSq 2707  := by decide +kernel
private theorem c2707_nof3  : NoF3ChkSq 2707  := by decide +kernel
private theorem c2707_nof4z : NoF4zChkSq 2707 := by decide +kernel
theorem C'_2707 : C' 2707 :=
  ⟨c2707_sqf, c2707_range, c2707_ell, leafNSq_of_sq c2707_nsq, leafHAr_of_sq c2707_har,
   c2707_r, c2707_e', c2707_f1, leafS2_of_sq c2707_s2, leafS3_of_sq c2707_s3,
   c2707_iso, leafR8_of_sq c2707_nof2 c2707_nof3 c2707_nof4z⟩
theorem not_tile'_2707 (D : CongruentDissection 2707) : False :=
  not_tile_of_conditions' 2707 C'_2707 D

private theorem c2710_sqf   : LeafSqf 2710   := by decide +kernel
private theorem c2710_range : LeafRange 2710  := by decide +kernel
private theorem c2710_ell   : LeafEll 2710    := by decide +kernel
private theorem c2710_nsq   : NSqChkSq 2710   := by decide +kernel
private theorem c2710_har   : HArithChkSq 2710 := by decide +kernel
private theorem c2710_r     : LeafR 2710      := by decide +kernel
private theorem c2710_e'    : LeafE' 2710     := by decide +kernel
private theorem c2710_f1    : LeafF1 2710     := Or.inl (by decide)
private theorem c2710_s2    : S2ChkSq 2710    := by decide +kernel
private theorem c2710_s3    : S3ChkSq 2710    := by decide +kernel
private theorem c2710_iso   : LeafIso 2710    := by decide +kernel
private theorem c2710_nof2  : NoF2ChkSq 2710  := by decide +kernel
private theorem c2710_nof3  : NoF3ChkSq 2710  := by decide +kernel
private theorem c2710_nof4z : NoF4zChkSq 2710 := by decide +kernel
theorem C'_2710 : C' 2710 :=
  ⟨c2710_sqf, c2710_range, c2710_ell, leafNSq_of_sq c2710_nsq, leafHAr_of_sq c2710_har,
   c2710_r, c2710_e', c2710_f1, leafS2_of_sq c2710_s2, leafS3_of_sq c2710_s3,
   c2710_iso, leafR8_of_sq c2710_nof2 c2710_nof3 c2710_nof4z⟩
theorem not_tile'_2710 (D : CongruentDissection 2710) : False :=
  not_tile_of_conditions' 2710 C'_2710 D

end Erdos634.Draft.AllN2

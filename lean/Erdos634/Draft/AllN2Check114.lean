/- AllN2Check114: N = 2791, 2794, 2795, 2798, 2802
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2791_sqf   : LeafSqf 2791   := by decide +kernel
private theorem c2791_range : LeafRange 2791  := by decide +kernel
private theorem c2791_ell   : LeafEll 2791    := by decide +kernel
private theorem c2791_nsq   : NSqChkSq 2791   := by decide +kernel
private theorem c2791_har   : HArithChkSq 2791 := by decide +kernel
private theorem c2791_r     : LeafR 2791      := by decide +kernel
private theorem c2791_e'    : LeafE' 2791     := by decide +kernel
private theorem c2791_f1    : LeafF1 2791     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2791_s2    : S2ChkSq 2791    := by decide +kernel
private theorem c2791_s3    : S3ChkSq 2791    := by decide +kernel
private theorem c2791_iso   : LeafIso 2791    := by decide +kernel
private theorem c2791_nof2  : NoF2ChkSq 2791  := by decide +kernel
private theorem c2791_nof3  : NoF3ChkSq 2791  := by decide +kernel
private theorem c2791_nof4z : NoF4zChkSq 2791 := by decide +kernel
theorem C'_2791 : C' 2791 :=
  ⟨c2791_sqf, c2791_range, c2791_ell, leafNSq_of_sq c2791_nsq, leafHAr_of_sq c2791_har,
   c2791_r, c2791_e', c2791_f1, leafS2_of_sq c2791_s2, leafS3_of_sq c2791_s3,
   c2791_iso, leafR8_of_sq c2791_nof2 c2791_nof3 c2791_nof4z⟩
theorem not_tile'_2791 (D : CongruentDissection 2791) : False :=
  not_tile_of_conditions' 2791 C'_2791 D

private theorem c2794_sqf   : LeafSqf 2794   := by decide +kernel
private theorem c2794_range : LeafRange 2794  := by decide +kernel
private theorem c2794_ell   : LeafEll 2794    := by decide +kernel
private theorem c2794_nsq   : NSqChkSq 2794   := by decide +kernel
private theorem c2794_har   : HArithChkSq 2794 := by decide +kernel
private theorem c2794_r     : LeafR 2794      := by decide +kernel
private theorem c2794_e'    : LeafE' 2794     := by decide +kernel
private theorem c2794_f1    : LeafF1 2794     := Or.inl (by decide)
private theorem c2794_s2    : S2ChkSq 2794    := by decide +kernel
private theorem c2794_s3    : S3ChkSq 2794    := by decide +kernel
private theorem c2794_iso   : LeafIso 2794    := by decide +kernel
private theorem c2794_nof2  : NoF2ChkSq 2794  := by decide +kernel
private theorem c2794_nof3  : NoF3ChkSq 2794  := by decide +kernel
private theorem c2794_nof4z : NoF4zChkSq 2794 := by decide +kernel
theorem C'_2794 : C' 2794 :=
  ⟨c2794_sqf, c2794_range, c2794_ell, leafNSq_of_sq c2794_nsq, leafHAr_of_sq c2794_har,
   c2794_r, c2794_e', c2794_f1, leafS2_of_sq c2794_s2, leafS3_of_sq c2794_s3,
   c2794_iso, leafR8_of_sq c2794_nof2 c2794_nof3 c2794_nof4z⟩
theorem not_tile'_2794 (D : CongruentDissection 2794) : False :=
  not_tile_of_conditions' 2794 C'_2794 D

private theorem c2795_sqf   : LeafSqf 2795   := by decide +kernel
private theorem c2795_range : LeafRange 2795  := by decide +kernel
private theorem c2795_ell   : LeafEll 2795    := by decide +kernel
private theorem c2795_nsq   : NSqChkSq 2795   := by decide +kernel
private theorem c2795_har   : HArithChkSq 2795 := by decide +kernel
private theorem c2795_r     : LeafR 2795      := by decide +kernel
private theorem c2795_e'    : LeafE' 2795     := by decide +kernel
private theorem c2795_f1    : LeafF1 2795     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2795_s2    : S2ChkSq 2795    := by decide +kernel
private theorem c2795_s3    : S3ChkSq 2795    := by decide +kernel
private theorem c2795_iso   : LeafIso 2795    := by decide +kernel
private theorem c2795_nof2  : NoF2ChkSq 2795  := by decide +kernel
private theorem c2795_nof3  : NoF3ChkSq 2795  := by decide +kernel
private theorem c2795_nof4z : NoF4zChkSq 2795 := by decide +kernel
theorem C'_2795 : C' 2795 :=
  ⟨c2795_sqf, c2795_range, c2795_ell, leafNSq_of_sq c2795_nsq, leafHAr_of_sq c2795_har,
   c2795_r, c2795_e', c2795_f1, leafS2_of_sq c2795_s2, leafS3_of_sq c2795_s3,
   c2795_iso, leafR8_of_sq c2795_nof2 c2795_nof3 c2795_nof4z⟩
theorem not_tile'_2795 (D : CongruentDissection 2795) : False :=
  not_tile_of_conditions' 2795 C'_2795 D

private theorem c2798_sqf   : LeafSqf 2798   := by decide +kernel
private theorem c2798_range : LeafRange 2798  := by decide +kernel
private theorem c2798_ell   : LeafEll 2798    := by decide +kernel
private theorem c2798_nsq   : NSqChkSq 2798   := by decide +kernel
private theorem c2798_har   : HArithChkSq 2798 := by decide +kernel
private theorem c2798_r     : LeafR 2798      := by decide +kernel
private theorem c2798_e'    : LeafE' 2798     := by decide +kernel
private theorem c2798_f1    : LeafF1 2798     := Or.inl (by decide)
private theorem c2798_s2    : S2ChkSq 2798    := by decide +kernel
private theorem c2798_s3    : S3ChkSq 2798    := by decide +kernel
private theorem c2798_iso   : LeafIso 2798    := by decide +kernel
private theorem c2798_nof2  : NoF2ChkSq 2798  := by decide +kernel
private theorem c2798_nof3  : NoF3ChkSq 2798  := by decide +kernel
private theorem c2798_nof4z : NoF4zChkSq 2798 := by decide +kernel
theorem C'_2798 : C' 2798 :=
  ⟨c2798_sqf, c2798_range, c2798_ell, leafNSq_of_sq c2798_nsq, leafHAr_of_sq c2798_har,
   c2798_r, c2798_e', c2798_f1, leafS2_of_sq c2798_s2, leafS3_of_sq c2798_s3,
   c2798_iso, leafR8_of_sq c2798_nof2 c2798_nof3 c2798_nof4z⟩
theorem not_tile'_2798 (D : CongruentDissection 2798) : False :=
  not_tile_of_conditions' 2798 C'_2798 D

private theorem c2802_sqf   : LeafSqf 2802   := by decide +kernel
private theorem c2802_range : LeafRange 2802  := by decide +kernel
private theorem c2802_ell   : LeafEll 2802    := by decide +kernel
private theorem c2802_nsq   : NSqChkSq 2802   := by decide +kernel
private theorem c2802_har   : HArithChkSq 2802 := by decide +kernel
private theorem c2802_r     : LeafR 2802      := by decide +kernel
private theorem c2802_e'    : LeafE' 2802     := by decide +kernel
private theorem c2802_f1    : LeafF1 2802     := Or.inl (by decide)
private theorem c2802_s2    : S2ChkSq 2802    := by decide +kernel
private theorem c2802_s3    : S3ChkSq 2802    := by decide +kernel
private theorem c2802_iso   : LeafIso 2802    := by decide +kernel
private theorem c2802_nof2  : NoF2ChkSq 2802  := by decide +kernel
private theorem c2802_nof3  : NoF3ChkSq 2802  := by decide +kernel
private theorem c2802_nof4z : NoF4zChkSq 2802 := by decide +kernel
theorem C'_2802 : C' 2802 :=
  ⟨c2802_sqf, c2802_range, c2802_ell, leafNSq_of_sq c2802_nsq, leafHAr_of_sq c2802_har,
   c2802_r, c2802_e', c2802_f1, leafS2_of_sq c2802_s2, leafS3_of_sq c2802_s3,
   c2802_iso, leafR8_of_sq c2802_nof2 c2802_nof3 c2802_nof4z⟩
theorem not_tile'_2802 (D : CongruentDissection 2802) : False :=
  not_tile_of_conditions' 2802 C'_2802 D

end Erdos634.Draft.AllN2

/- AllN2Check113: N = 2778, 2779, 2782, 2786, 2787
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2778_sqf   : LeafSqf 2778   := by decide +kernel
private theorem c2778_range : LeafRange 2778  := by decide +kernel
private theorem c2778_ell   : LeafEll 2778    := by decide +kernel
private theorem c2778_nsq   : NSqChkSq 2778   := by decide +kernel
private theorem c2778_har   : HArithChkSq 2778 := by decide +kernel
private theorem c2778_r     : LeafR 2778      := by decide +kernel
private theorem c2778_e'    : LeafE' 2778     := by decide +kernel
private theorem c2778_f1    : LeafF1 2778     := Or.inl (by decide)
private theorem c2778_s2    : S2ChkSq 2778    := by decide +kernel
private theorem c2778_s3    : S3ChkSq 2778    := by decide +kernel
private theorem c2778_iso   : LeafIso 2778    := by decide +kernel
private theorem c2778_nof2  : NoF2ChkSq 2778  := by decide +kernel
private theorem c2778_nof3  : NoF3ChkSq 2778  := by decide +kernel
private theorem c2778_nof4z : NoF4zChkSq 2778 := by decide +kernel
theorem C'_2778 : C' 2778 :=
  ⟨c2778_sqf, c2778_range, c2778_ell, leafNSq_of_sq c2778_nsq, leafHAr_of_sq c2778_har,
   c2778_r, c2778_e', c2778_f1, leafS2_of_sq c2778_s2, leafS3_of_sq c2778_s3,
   c2778_iso, leafR8_of_sq c2778_nof2 c2778_nof3 c2778_nof4z⟩
theorem not_tile'_2778 (D : CongruentDissection 2778) : False :=
  not_tile_of_conditions' 2778 C'_2778 D

private theorem c2779_sqf   : LeafSqf 2779   := by decide +kernel
private theorem c2779_range : LeafRange 2779  := by decide +kernel
private theorem c2779_ell   : LeafEll 2779    := by decide +kernel
private theorem c2779_nsq   : NSqChkSq 2779   := by decide +kernel
private theorem c2779_har   : HArithChkSq 2779 := by decide +kernel
private theorem c2779_r     : LeafR 2779      := by decide +kernel
private theorem c2779_e'    : LeafE' 2779     := by decide +kernel
private theorem c2779_f1    : LeafF1 2779     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2779_s2    : S2ChkSq 2779    := by decide +kernel
private theorem c2779_s3    : S3ChkSq 2779    := by decide +kernel
private theorem c2779_iso   : LeafIso 2779    := by decide +kernel
private theorem c2779_nof2  : NoF2ChkSq 2779  := by decide +kernel
private theorem c2779_nof3  : NoF3ChkSq 2779  := by decide +kernel
private theorem c2779_nof4z : NoF4zChkSq 2779 := by decide +kernel
theorem C'_2779 : C' 2779 :=
  ⟨c2779_sqf, c2779_range, c2779_ell, leafNSq_of_sq c2779_nsq, leafHAr_of_sq c2779_har,
   c2779_r, c2779_e', c2779_f1, leafS2_of_sq c2779_s2, leafS3_of_sq c2779_s3,
   c2779_iso, leafR8_of_sq c2779_nof2 c2779_nof3 c2779_nof4z⟩
theorem not_tile'_2779 (D : CongruentDissection 2779) : False :=
  not_tile_of_conditions' 2779 C'_2779 D

private theorem c2782_sqf   : LeafSqf 2782   := by decide +kernel
private theorem c2782_range : LeafRange 2782  := by decide +kernel
private theorem c2782_ell   : LeafEll 2782    := by decide +kernel
private theorem c2782_nsq   : NSqChkSq 2782   := by decide +kernel
private theorem c2782_har   : HArithChkSq 2782 := by decide +kernel
private theorem c2782_r     : LeafR 2782      := by decide +kernel
private theorem c2782_e'    : LeafE' 2782     := by decide +kernel
private theorem c2782_f1    : LeafF1 2782     := Or.inl (by decide)
private theorem c2782_s2    : S2ChkSq 2782    := by decide +kernel
private theorem c2782_s3    : S3ChkSq 2782    := by decide +kernel
private theorem c2782_iso   : LeafIso 2782    := by decide +kernel
private theorem c2782_nof2  : NoF2ChkSq 2782  := by decide +kernel
private theorem c2782_nof3  : NoF3ChkSq 2782  := by decide +kernel
private theorem c2782_nof4z : NoF4zChkSq 2782 := by decide +kernel
theorem C'_2782 : C' 2782 :=
  ⟨c2782_sqf, c2782_range, c2782_ell, leafNSq_of_sq c2782_nsq, leafHAr_of_sq c2782_har,
   c2782_r, c2782_e', c2782_f1, leafS2_of_sq c2782_s2, leafS3_of_sq c2782_s3,
   c2782_iso, leafR8_of_sq c2782_nof2 c2782_nof3 c2782_nof4z⟩
theorem not_tile'_2782 (D : CongruentDissection 2782) : False :=
  not_tile_of_conditions' 2782 C'_2782 D

private theorem c2786_sqf   : LeafSqf 2786   := by decide +kernel
private theorem c2786_range : LeafRange 2786  := by decide +kernel
private theorem c2786_ell   : LeafEll 2786    := by decide +kernel
private theorem c2786_nsq   : NSqChkSq 2786   := by decide +kernel
private theorem c2786_har   : HArithChkSq 2786 := by decide +kernel
private theorem c2786_r     : LeafR 2786      := by decide +kernel
private theorem c2786_e'    : LeafE' 2786     := by decide +kernel
private theorem c2786_f1    : LeafF1 2786     := Or.inl (by decide)
private theorem c2786_s2    : S2ChkSq 2786    := by decide +kernel
private theorem c2786_s3    : S3ChkSq 2786    := by decide +kernel
private theorem c2786_iso   : LeafIso 2786    := by decide +kernel
private theorem c2786_nof2  : NoF2ChkSq 2786  := by decide +kernel
private theorem c2786_nof3  : NoF3ChkSq 2786  := by decide +kernel
private theorem c2786_nof4z : NoF4zChkSq 2786 := by decide +kernel
theorem C'_2786 : C' 2786 :=
  ⟨c2786_sqf, c2786_range, c2786_ell, leafNSq_of_sq c2786_nsq, leafHAr_of_sq c2786_har,
   c2786_r, c2786_e', c2786_f1, leafS2_of_sq c2786_s2, leafS3_of_sq c2786_s3,
   c2786_iso, leafR8_of_sq c2786_nof2 c2786_nof3 c2786_nof4z⟩
theorem not_tile'_2786 (D : CongruentDissection 2786) : False :=
  not_tile_of_conditions' 2786 C'_2786 D

private theorem c2787_sqf   : LeafSqf 2787   := by decide +kernel
private theorem c2787_range : LeafRange 2787  := by decide +kernel
private theorem c2787_ell   : LeafEll 2787    := by decide +kernel
private theorem c2787_nsq   : NSqChkSq 2787   := by decide +kernel
private theorem c2787_har   : HArithChkSq 2787 := by decide +kernel
private theorem c2787_r     : LeafR 2787      := by decide +kernel
private theorem c2787_e'    : LeafE' 2787     := by decide +kernel
private theorem c2787_f1    : LeafF1 2787     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2787_s2    : S2ChkSq 2787    := by decide +kernel
private theorem c2787_s3    : S3ChkSq 2787    := by decide +kernel
private theorem c2787_iso   : LeafIso 2787    := by decide +kernel
private theorem c2787_nof2  : NoF2ChkSq 2787  := by decide +kernel
private theorem c2787_nof3  : NoF3ChkSq 2787  := by decide +kernel
private theorem c2787_nof4z : NoF4zChkSq 2787 := by decide +kernel
theorem C'_2787 : C' 2787 :=
  ⟨c2787_sqf, c2787_range, c2787_ell, leafNSq_of_sq c2787_nsq, leafHAr_of_sq c2787_har,
   c2787_r, c2787_e', c2787_f1, leafS2_of_sq c2787_s2, leafS3_of_sq c2787_s3,
   c2787_iso, leafR8_of_sq c2787_nof2 c2787_nof3 c2787_nof4z⟩
theorem not_tile'_2787 (D : CongruentDissection 2787) : False :=
  not_tile_of_conditions' 2787 C'_2787 D

end Erdos634.Draft.AllN2

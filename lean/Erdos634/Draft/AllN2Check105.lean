/- AllN2Check105: N = 2670, 2671, 2674, 2678, 2679
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2670_sqf   : LeafSqf 2670   := by decide +kernel
private theorem c2670_range : LeafRange 2670  := by decide +kernel
private theorem c2670_ell   : LeafEll 2670    := by decide +kernel
private theorem c2670_nsq   : NSqChkSq 2670   := by decide +kernel
private theorem c2670_har   : HArithChkSq 2670 := by decide +kernel
private theorem c2670_r     : LeafR 2670      := by decide +kernel
private theorem c2670_e'    : LeafE' 2670     := by decide +kernel
private theorem c2670_f1    : LeafF1 2670     := Or.inl (by decide)
private theorem c2670_s2    : S2ChkSq 2670    := by decide +kernel
private theorem c2670_s3    : S3ChkSq 2670    := by decide +kernel
private theorem c2670_iso   : LeafIso 2670    := by decide +kernel
private theorem c2670_nof2  : NoF2ChkSq 2670  := by decide +kernel
private theorem c2670_nof3  : NoF3ChkSq 2670  := by decide +kernel
private theorem c2670_nof4z : NoF4zChkSq 2670 := by decide +kernel
theorem C'_2670 : C' 2670 :=
  ⟨c2670_sqf, c2670_range, c2670_ell, leafNSq_of_sq c2670_nsq, leafHAr_of_sq c2670_har,
   c2670_r, c2670_e', c2670_f1, leafS2_of_sq c2670_s2, leafS3_of_sq c2670_s3,
   c2670_iso, leafR8_of_sq c2670_nof2 c2670_nof3 c2670_nof4z⟩
theorem not_tile'_2670 (D : CongruentDissection 2670) : False :=
  not_tile_of_conditions' 2670 C'_2670 D

private theorem c2671_sqf   : LeafSqf 2671   := by decide +kernel
private theorem c2671_range : LeafRange 2671  := by decide +kernel
private theorem c2671_ell   : LeafEll 2671    := by decide +kernel
private theorem c2671_nsq   : NSqChkSq 2671   := by decide +kernel
private theorem c2671_har   : HArithChkSq 2671 := by decide +kernel
private theorem c2671_r     : LeafR 2671      := by decide +kernel
private theorem c2671_e'    : LeafE' 2671     := by decide +kernel
private theorem c2671_f1    : LeafF1 2671     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2671_s2    : S2ChkSq 2671    := by decide +kernel
private theorem c2671_s3    : S3ChkSq 2671    := by decide +kernel
private theorem c2671_iso   : LeafIso 2671    := by decide +kernel
private theorem c2671_nof2  : NoF2ChkSq 2671  := by decide +kernel
private theorem c2671_nof3  : NoF3ChkSq 2671  := by decide +kernel
private theorem c2671_nof4z : NoF4zChkSq 2671 := by decide +kernel
theorem C'_2671 : C' 2671 :=
  ⟨c2671_sqf, c2671_range, c2671_ell, leafNSq_of_sq c2671_nsq, leafHAr_of_sq c2671_har,
   c2671_r, c2671_e', c2671_f1, leafS2_of_sq c2671_s2, leafS3_of_sq c2671_s3,
   c2671_iso, leafR8_of_sq c2671_nof2 c2671_nof3 c2671_nof4z⟩
theorem not_tile'_2671 (D : CongruentDissection 2671) : False :=
  not_tile_of_conditions' 2671 C'_2671 D

private theorem c2674_sqf   : LeafSqf 2674   := by decide +kernel
private theorem c2674_range : LeafRange 2674  := by decide +kernel
private theorem c2674_ell   : LeafEll 2674    := by decide +kernel
private theorem c2674_nsq   : NSqChkSq 2674   := by decide +kernel
private theorem c2674_har   : HArithChkSq 2674 := by decide +kernel
private theorem c2674_r     : LeafR 2674      := by decide +kernel
private theorem c2674_e'    : LeafE' 2674     := by decide +kernel
private theorem c2674_f1    : LeafF1 2674     := Or.inl (by decide)
private theorem c2674_s2    : S2ChkSq 2674    := by decide +kernel
private theorem c2674_s3    : S3ChkSq 2674    := by decide +kernel
private theorem c2674_iso   : LeafIso 2674    := by decide +kernel
private theorem c2674_nof2  : NoF2ChkSq 2674  := by decide +kernel
private theorem c2674_nof3  : NoF3ChkSq 2674  := by decide +kernel
private theorem c2674_nof4z : NoF4zChkSq 2674 := by decide +kernel
theorem C'_2674 : C' 2674 :=
  ⟨c2674_sqf, c2674_range, c2674_ell, leafNSq_of_sq c2674_nsq, leafHAr_of_sq c2674_har,
   c2674_r, c2674_e', c2674_f1, leafS2_of_sq c2674_s2, leafS3_of_sq c2674_s3,
   c2674_iso, leafR8_of_sq c2674_nof2 c2674_nof3 c2674_nof4z⟩
theorem not_tile'_2674 (D : CongruentDissection 2674) : False :=
  not_tile_of_conditions' 2674 C'_2674 D

private theorem c2678_sqf   : LeafSqf 2678   := by decide +kernel
private theorem c2678_range : LeafRange 2678  := by decide +kernel
private theorem c2678_ell   : LeafEll 2678    := by decide +kernel
private theorem c2678_nsq   : NSqChkSq 2678   := by decide +kernel
private theorem c2678_har   : HArithChkSq 2678 := by decide +kernel
private theorem c2678_r     : LeafR 2678      := by decide +kernel
private theorem c2678_e'    : LeafE' 2678     := by decide +kernel
private theorem c2678_f1    : LeafF1 2678     := Or.inl (by decide)
private theorem c2678_s2    : S2ChkSq 2678    := by decide +kernel
private theorem c2678_s3    : S3ChkSq 2678    := by decide +kernel
private theorem c2678_iso   : LeafIso 2678    := by decide +kernel
private theorem c2678_nof2  : NoF2ChkSq 2678  := by decide +kernel
private theorem c2678_nof3  : NoF3ChkSq 2678  := by decide +kernel
private theorem c2678_nof4z : NoF4zChkSq 2678 := by decide +kernel
theorem C'_2678 : C' 2678 :=
  ⟨c2678_sqf, c2678_range, c2678_ell, leafNSq_of_sq c2678_nsq, leafHAr_of_sq c2678_har,
   c2678_r, c2678_e', c2678_f1, leafS2_of_sq c2678_s2, leafS3_of_sq c2678_s3,
   c2678_iso, leafR8_of_sq c2678_nof2 c2678_nof3 c2678_nof4z⟩
theorem not_tile'_2678 (D : CongruentDissection 2678) : False :=
  not_tile_of_conditions' 2678 C'_2678 D

private theorem c2679_sqf   : LeafSqf 2679   := by decide +kernel
private theorem c2679_range : LeafRange 2679  := by decide +kernel
private theorem c2679_ell   : LeafEll 2679    := by decide +kernel
private theorem c2679_nsq   : NSqChkSq 2679   := by decide +kernel
private theorem c2679_har   : HArithChkSq 2679 := by decide +kernel
private theorem c2679_r     : LeafR 2679      := by decide +kernel
private theorem c2679_e'    : LeafE' 2679     := by decide +kernel
private theorem c2679_f1    : LeafF1 2679     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2679_s2    : S2ChkSq 2679    := by decide +kernel
private theorem c2679_s3    : S3ChkSq 2679    := by decide +kernel
private theorem c2679_iso   : LeafIso 2679    := by decide +kernel
private theorem c2679_nof2  : NoF2ChkSq 2679  := by decide +kernel
private theorem c2679_nof3  : NoF3ChkSq 2679  := by decide +kernel
private theorem c2679_nof4z : NoF4zChkSq 2679 := by decide +kernel
theorem C'_2679 : C' 2679 :=
  ⟨c2679_sqf, c2679_range, c2679_ell, leafNSq_of_sq c2679_nsq, leafHAr_of_sq c2679_har,
   c2679_r, c2679_e', c2679_f1, leafS2_of_sq c2679_s2, leafS3_of_sq c2679_s3,
   c2679_iso, leafR8_of_sq c2679_nof2 c2679_nof3 c2679_nof4z⟩
theorem not_tile'_2679 (D : CongruentDissection 2679) : False :=
  not_tile_of_conditions' 2679 C'_2679 D

end Erdos634.Draft.AllN2

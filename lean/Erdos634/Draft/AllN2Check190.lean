/- AllN2Check190: N = 3777, 3779, 3781, 3782, 3786
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3777_sqf   : LeafSqf 3777   := by decide +kernel
private theorem c3777_range : LeafRange 3777  := by decide +kernel
private theorem c3777_ell   : LeafEll 3777    := by decide +kernel
private theorem c3777_nsq   : NSqChkSq 3777   := by decide +kernel
private theorem c3777_har   : HArithChkSq 3777 := by decide +kernel
private theorem c3777_r     : LeafR 3777      := by decide +kernel
private theorem c3777_e'    : LeafE' 3777     := by decide +kernel
private theorem c3777_f1    : LeafF1 3777     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3777_s2    : S2ChkSq 3777    := by decide +kernel
private theorem c3777_s3    : S3ChkSq 3777    := by decide +kernel
private theorem c3777_iso   : LeafIso 3777    := by decide +kernel
private theorem c3777_nof2  : NoF2ChkSq 3777  := by decide +kernel
private theorem c3777_nof3  : NoF3ChkSq 3777  := by decide +kernel
private theorem c3777_nof4z : NoF4zChkSq 3777 := by decide +kernel
theorem C'_3777 : C' 3777 :=
  ⟨c3777_sqf, c3777_range, c3777_ell, leafNSq_of_sq c3777_nsq, leafHAr_of_sq c3777_har,
   c3777_r, c3777_e', c3777_f1, leafS2_of_sq c3777_s2, leafS3_of_sq c3777_s3,
   c3777_iso, leafR8_of_sq c3777_nof2 c3777_nof3 c3777_nof4z⟩
theorem not_tile'_3777 (D : CongruentDissection 3777) : False :=
  not_tile_of_conditions' 3777 C'_3777 D

private theorem c3779_sqf   : LeafSqf 3779   := by decide +kernel
private theorem c3779_range : LeafRange 3779  := by decide +kernel
private theorem c3779_ell   : LeafEll 3779    := by decide +kernel
private theorem c3779_nsq   : NSqChkSq 3779   := by decide +kernel
private theorem c3779_har   : HArithChkSq 3779 := by decide +kernel
private theorem c3779_r     : LeafR 3779      := by decide +kernel
private theorem c3779_e'    : LeafE' 3779     := by decide +kernel
private theorem c3779_f1    : LeafF1 3779     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3779_s2    : S2ChkSq 3779    := by decide +kernel
private theorem c3779_s3    : S3ChkSq 3779    := by decide +kernel
private theorem c3779_iso   : LeafIso 3779    := by decide +kernel
private theorem c3779_nof2  : NoF2ChkSq 3779  := by decide +kernel
private theorem c3779_nof3  : NoF3ChkSq 3779  := by decide +kernel
private theorem c3779_nof4z : NoF4zChkSq 3779 := by decide +kernel
theorem C'_3779 : C' 3779 :=
  ⟨c3779_sqf, c3779_range, c3779_ell, leafNSq_of_sq c3779_nsq, leafHAr_of_sq c3779_har,
   c3779_r, c3779_e', c3779_f1, leafS2_of_sq c3779_s2, leafS3_of_sq c3779_s3,
   c3779_iso, leafR8_of_sq c3779_nof2 c3779_nof3 c3779_nof4z⟩
theorem not_tile'_3779 (D : CongruentDissection 3779) : False :=
  not_tile_of_conditions' 3779 C'_3779 D

private theorem c3781_sqf   : LeafSqf 3781   := by decide +kernel
private theorem c3781_range : LeafRange 3781  := by decide +kernel
private theorem c3781_ell   : LeafEll 3781    := by decide +kernel
private theorem c3781_nsq   : NSqChkSq 3781   := by decide +kernel
private theorem c3781_har   : HArithChkSq 3781 := by decide +kernel
private theorem c3781_r     : LeafR 3781      := by decide +kernel
private theorem c3781_e'    : LeafE' 3781     := by decide +kernel
private theorem c3781_f1    : LeafF1 3781     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3781_s2    : S2ChkSq 3781    := by decide +kernel
private theorem c3781_s3    : S3ChkSq 3781    := by decide +kernel
private theorem c3781_iso   : LeafIso 3781    := by decide +kernel
private theorem c3781_nof2  : NoF2ChkSq 3781  := by decide +kernel
private theorem c3781_nof3  : NoF3ChkSq 3781  := by decide +kernel
private theorem c3781_nof4z : NoF4zChkSq 3781 := by decide +kernel
theorem C'_3781 : C' 3781 :=
  ⟨c3781_sqf, c3781_range, c3781_ell, leafNSq_of_sq c3781_nsq, leafHAr_of_sq c3781_har,
   c3781_r, c3781_e', c3781_f1, leafS2_of_sq c3781_s2, leafS3_of_sq c3781_s3,
   c3781_iso, leafR8_of_sq c3781_nof2 c3781_nof3 c3781_nof4z⟩
theorem not_tile'_3781 (D : CongruentDissection 3781) : False :=
  not_tile_of_conditions' 3781 C'_3781 D

private theorem c3782_sqf   : LeafSqf 3782   := by decide +kernel
private theorem c3782_range : LeafRange 3782  := by decide +kernel
private theorem c3782_ell   : LeafEll 3782    := by decide +kernel
private theorem c3782_nsq   : NSqChkSq 3782   := by decide +kernel
private theorem c3782_har   : HArithChkSq 3782 := by decide +kernel
private theorem c3782_r     : LeafR 3782      := by decide +kernel
private theorem c3782_e'    : LeafE' 3782     := by decide +kernel
private theorem c3782_f1    : LeafF1 3782     := Or.inl (by decide)
private theorem c3782_s2    : S2ChkSq 3782    := by decide +kernel
private theorem c3782_s3    : S3ChkSq 3782    := by decide +kernel
private theorem c3782_iso   : LeafIso 3782    := by decide +kernel
private theorem c3782_nof2  : NoF2ChkSq 3782  := by decide +kernel
private theorem c3782_nof3  : NoF3ChkSq 3782  := by decide +kernel
private theorem c3782_nof4z : NoF4zChkSq 3782 := by decide +kernel
theorem C'_3782 : C' 3782 :=
  ⟨c3782_sqf, c3782_range, c3782_ell, leafNSq_of_sq c3782_nsq, leafHAr_of_sq c3782_har,
   c3782_r, c3782_e', c3782_f1, leafS2_of_sq c3782_s2, leafS3_of_sq c3782_s3,
   c3782_iso, leafR8_of_sq c3782_nof2 c3782_nof3 c3782_nof4z⟩
theorem not_tile'_3782 (D : CongruentDissection 3782) : False :=
  not_tile_of_conditions' 3782 C'_3782 D

private theorem c3786_sqf   : LeafSqf 3786   := by decide +kernel
private theorem c3786_range : LeafRange 3786  := by decide +kernel
private theorem c3786_ell   : LeafEll 3786    := by decide +kernel
private theorem c3786_nsq   : NSqChkSq 3786   := by decide +kernel
private theorem c3786_har   : HArithChkSq 3786 := by decide +kernel
private theorem c3786_r     : LeafR 3786      := by decide +kernel
private theorem c3786_e'    : LeafE' 3786     := by decide +kernel
private theorem c3786_f1    : LeafF1 3786     := Or.inl (by decide)
private theorem c3786_s2    : S2ChkSq 3786    := by decide +kernel
private theorem c3786_s3    : S3ChkSq 3786    := by decide +kernel
private theorem c3786_iso   : LeafIso 3786    := by decide +kernel
private theorem c3786_nof2  : NoF2ChkSq 3786  := by decide +kernel
private theorem c3786_nof3  : NoF3ChkSq 3786  := by decide +kernel
private theorem c3786_nof4z : NoF4zChkSq 3786 := by decide +kernel
theorem C'_3786 : C' 3786 :=
  ⟨c3786_sqf, c3786_range, c3786_ell, leafNSq_of_sq c3786_nsq, leafHAr_of_sq c3786_har,
   c3786_r, c3786_e', c3786_f1, leafS2_of_sq c3786_s2, leafS3_of_sq c3786_s3,
   c3786_iso, leafR8_of_sq c3786_nof2 c3786_nof3 c3786_nof4z⟩
theorem not_tile'_3786 (D : CongruentDissection 3786) : False :=
  not_tile_of_conditions' 3786 C'_3786 D

end Erdos634.Draft.AllN2

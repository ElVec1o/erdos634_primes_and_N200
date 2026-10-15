/- AllN2Check183: N = 3678, 3679, 3682, 3683, 3685
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3678_sqf   : LeafSqf 3678   := by decide +kernel
private theorem c3678_range : LeafRange 3678  := by decide +kernel
private theorem c3678_ell   : LeafEll 3678    := by decide +kernel
private theorem c3678_nsq   : NSqChkSq 3678   := by decide +kernel
private theorem c3678_har   : HArithChkSq 3678 := by decide +kernel
private theorem c3678_r     : LeafR 3678      := by decide +kernel
private theorem c3678_e'    : LeafE' 3678     := by decide +kernel
private theorem c3678_f1    : LeafF1 3678     := Or.inl (by decide)
private theorem c3678_s2    : S2ChkSq 3678    := by decide +kernel
private theorem c3678_s3    : S3ChkSq 3678    := by decide +kernel
private theorem c3678_iso   : LeafIso 3678    := by decide +kernel
private theorem c3678_nof2  : NoF2ChkSq 3678  := by decide +kernel
private theorem c3678_nof3  : NoF3ChkSq 3678  := by decide +kernel
private theorem c3678_nof4z : NoF4zChkSq 3678 := by decide +kernel
theorem C'_3678 : C' 3678 :=
  ⟨c3678_sqf, c3678_range, c3678_ell, leafNSq_of_sq c3678_nsq, leafHAr_of_sq c3678_har,
   c3678_r, c3678_e', c3678_f1, leafS2_of_sq c3678_s2, leafS3_of_sq c3678_s3,
   c3678_iso, leafR8_of_sq c3678_nof2 c3678_nof3 c3678_nof4z⟩
theorem not_tile'_3678 (D : CongruentDissection 3678) : False :=
  not_tile_of_conditions' 3678 C'_3678 D

private theorem c3679_sqf   : LeafSqf 3679   := by decide +kernel
private theorem c3679_range : LeafRange 3679  := by decide +kernel
private theorem c3679_ell   : LeafEll 3679    := by decide +kernel
private theorem c3679_nsq   : NSqChkSq 3679   := by decide +kernel
private theorem c3679_har   : HArithChkSq 3679 := by decide +kernel
private theorem c3679_r     : LeafR 3679      := by decide +kernel
private theorem c3679_e'    : LeafE' 3679     := by decide +kernel
private theorem c3679_f1    : LeafF1 3679     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3679_s2    : S2ChkSq 3679    := by decide +kernel
private theorem c3679_s3    : S3ChkSq 3679    := by decide +kernel
private theorem c3679_iso   : LeafIso 3679    := by decide +kernel
private theorem c3679_nof2  : NoF2ChkSq 3679  := by decide +kernel
private theorem c3679_nof3  : NoF3ChkSq 3679  := by decide +kernel
private theorem c3679_nof4z : NoF4zChkSq 3679 := by decide +kernel
theorem C'_3679 : C' 3679 :=
  ⟨c3679_sqf, c3679_range, c3679_ell, leafNSq_of_sq c3679_nsq, leafHAr_of_sq c3679_har,
   c3679_r, c3679_e', c3679_f1, leafS2_of_sq c3679_s2, leafS3_of_sq c3679_s3,
   c3679_iso, leafR8_of_sq c3679_nof2 c3679_nof3 c3679_nof4z⟩
theorem not_tile'_3679 (D : CongruentDissection 3679) : False :=
  not_tile_of_conditions' 3679 C'_3679 D

private theorem c3682_sqf   : LeafSqf 3682   := by decide +kernel
private theorem c3682_range : LeafRange 3682  := by decide +kernel
private theorem c3682_ell   : LeafEll 3682    := by decide +kernel
private theorem c3682_nsq   : NSqChkSq 3682   := by decide +kernel
private theorem c3682_har   : HArithChkSq 3682 := by decide +kernel
private theorem c3682_r     : LeafR 3682      := by decide +kernel
private theorem c3682_e'    : LeafE' 3682     := by decide +kernel
private theorem c3682_f1    : LeafF1 3682     := Or.inl (by decide)
private theorem c3682_s2    : S2ChkSq 3682    := by decide +kernel
private theorem c3682_s3    : S3ChkSq 3682    := by decide +kernel
private theorem c3682_iso   : LeafIso 3682    := by decide +kernel
private theorem c3682_nof2  : NoF2ChkSq 3682  := by decide +kernel
private theorem c3682_nof3  : NoF3ChkSq 3682  := by decide +kernel
private theorem c3682_nof4z : NoF4zChkSq 3682 := by decide +kernel
theorem C'_3682 : C' 3682 :=
  ⟨c3682_sqf, c3682_range, c3682_ell, leafNSq_of_sq c3682_nsq, leafHAr_of_sq c3682_har,
   c3682_r, c3682_e', c3682_f1, leafS2_of_sq c3682_s2, leafS3_of_sq c3682_s3,
   c3682_iso, leafR8_of_sq c3682_nof2 c3682_nof3 c3682_nof4z⟩
theorem not_tile'_3682 (D : CongruentDissection 3682) : False :=
  not_tile_of_conditions' 3682 C'_3682 D

private theorem c3683_sqf   : LeafSqf 3683   := by decide +kernel
private theorem c3683_range : LeafRange 3683  := by decide +kernel
private theorem c3683_ell   : LeafEll 3683    := by decide +kernel
private theorem c3683_nsq   : NSqChkSq 3683   := by decide +kernel
private theorem c3683_har   : HArithChkSq 3683 := by decide +kernel
private theorem c3683_r     : LeafR 3683      := by decide +kernel
private theorem c3683_e'    : LeafE' 3683     := by decide +kernel
private theorem c3683_f1    : LeafF1 3683     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3683_s2    : S2ChkSq 3683    := by decide +kernel
private theorem c3683_s3    : S3ChkSq 3683    := by decide +kernel
private theorem c3683_iso   : LeafIso 3683    := by decide +kernel
private theorem c3683_nof2  : NoF2ChkSq 3683  := by decide +kernel
private theorem c3683_nof3  : NoF3ChkSq 3683  := by decide +kernel
private theorem c3683_nof4z : NoF4zChkSq 3683 := by decide +kernel
theorem C'_3683 : C' 3683 :=
  ⟨c3683_sqf, c3683_range, c3683_ell, leafNSq_of_sq c3683_nsq, leafHAr_of_sq c3683_har,
   c3683_r, c3683_e', c3683_f1, leafS2_of_sq c3683_s2, leafS3_of_sq c3683_s3,
   c3683_iso, leafR8_of_sq c3683_nof2 c3683_nof3 c3683_nof4z⟩
theorem not_tile'_3683 (D : CongruentDissection 3683) : False :=
  not_tile_of_conditions' 3683 C'_3683 D

private theorem c3685_sqf   : LeafSqf 3685   := by decide +kernel
private theorem c3685_range : LeafRange 3685  := by decide +kernel
private theorem c3685_ell   : LeafEll 3685    := by decide +kernel
private theorem c3685_nsq   : NSqChkSq 3685   := by decide +kernel
private theorem c3685_har   : HArithChkSq 3685 := by decide +kernel
private theorem c3685_r     : LeafR 3685      := by decide +kernel
private theorem c3685_e'    : LeafE' 3685     := by decide +kernel
private theorem c3685_f1    : LeafF1 3685     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3685_s2    : S2ChkSq 3685    := by decide +kernel
private theorem c3685_s3    : S3ChkSq 3685    := by decide +kernel
private theorem c3685_iso   : LeafIso 3685    := by decide +kernel
private theorem c3685_nof2  : NoF2ChkSq 3685  := by decide +kernel
private theorem c3685_nof3  : NoF3ChkSq 3685  := by decide +kernel
private theorem c3685_nof4z : NoF4zChkSq 3685 := by decide +kernel
theorem C'_3685 : C' 3685 :=
  ⟨c3685_sqf, c3685_range, c3685_ell, leafNSq_of_sq c3685_nsq, leafHAr_of_sq c3685_har,
   c3685_r, c3685_e', c3685_f1, leafS2_of_sq c3685_s2, leafS3_of_sq c3685_s3,
   c3685_iso, leafR8_of_sq c3685_nof2 c3685_nof3 c3685_nof4z⟩
theorem not_tile'_3685 (D : CongruentDissection 3685) : False :=
  not_tile_of_conditions' 3685 C'_3685 D

end Erdos634.Draft.AllN2

/- AllN2Check182: N = 3667, 3669, 3670, 3671, 3674
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3667_sqf   : LeafSqf 3667   := by decide +kernel
private theorem c3667_range : LeafRange 3667  := by decide +kernel
private theorem c3667_ell   : LeafEll 3667    := by decide +kernel
private theorem c3667_nsq   : NSqChkSq 3667   := by decide +kernel
private theorem c3667_har   : HArithChkSq 3667 := by decide +kernel
private theorem c3667_r     : LeafR 3667      := by decide +kernel
private theorem c3667_e'    : LeafE' 3667     := by decide +kernel
private theorem c3667_f1    : LeafF1 3667     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3667_s2    : S2ChkSq 3667    := by decide +kernel
private theorem c3667_s3    : S3ChkSq 3667    := by decide +kernel
private theorem c3667_iso   : LeafIso 3667    := by decide +kernel
private theorem c3667_nof2  : NoF2ChkSq 3667  := by decide +kernel
private theorem c3667_nof3  : NoF3ChkSq 3667  := by decide +kernel
private theorem c3667_nof4z : NoF4zChkSq 3667 := by decide +kernel
theorem C'_3667 : C' 3667 :=
  ⟨c3667_sqf, c3667_range, c3667_ell, leafNSq_of_sq c3667_nsq, leafHAr_of_sq c3667_har,
   c3667_r, c3667_e', c3667_f1, leafS2_of_sq c3667_s2, leafS3_of_sq c3667_s3,
   c3667_iso, leafR8_of_sq c3667_nof2 c3667_nof3 c3667_nof4z⟩
theorem not_tile'_3667 (D : CongruentDissection 3667) : False :=
  not_tile_of_conditions' 3667 C'_3667 D

private theorem c3669_sqf   : LeafSqf 3669   := by decide +kernel
private theorem c3669_range : LeafRange 3669  := by decide +kernel
private theorem c3669_ell   : LeafEll 3669    := by decide +kernel
private theorem c3669_nsq   : NSqChkSq 3669   := by decide +kernel
private theorem c3669_har   : HArithChkSq 3669 := by decide +kernel
private theorem c3669_r     : LeafR 3669      := by decide +kernel
private theorem c3669_e'    : LeafE' 3669     := by decide +kernel
private theorem c3669_f1    : LeafF1 3669     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3669_s2    : S2ChkSq 3669    := by decide +kernel
private theorem c3669_s3    : S3ChkSq 3669    := by decide +kernel
private theorem c3669_iso   : LeafIso 3669    := by decide +kernel
private theorem c3669_nof2  : NoF2ChkSq 3669  := by decide +kernel
private theorem c3669_nof3  : NoF3ChkSq 3669  := by decide +kernel
private theorem c3669_nof4z : NoF4zChkSq 3669 := by decide +kernel
theorem C'_3669 : C' 3669 :=
  ⟨c3669_sqf, c3669_range, c3669_ell, leafNSq_of_sq c3669_nsq, leafHAr_of_sq c3669_har,
   c3669_r, c3669_e', c3669_f1, leafS2_of_sq c3669_s2, leafS3_of_sq c3669_s3,
   c3669_iso, leafR8_of_sq c3669_nof2 c3669_nof3 c3669_nof4z⟩
theorem not_tile'_3669 (D : CongruentDissection 3669) : False :=
  not_tile_of_conditions' 3669 C'_3669 D

private theorem c3670_sqf   : LeafSqf 3670   := by decide +kernel
private theorem c3670_range : LeafRange 3670  := by decide +kernel
private theorem c3670_ell   : LeafEll 3670    := by decide +kernel
private theorem c3670_nsq   : NSqChkSq 3670   := by decide +kernel
private theorem c3670_har   : HArithChkSq 3670 := by decide +kernel
private theorem c3670_r     : LeafR 3670      := by decide +kernel
private theorem c3670_e'    : LeafE' 3670     := by decide +kernel
private theorem c3670_f1    : LeafF1 3670     := Or.inl (by decide)
private theorem c3670_s2    : S2ChkSq 3670    := by decide +kernel
private theorem c3670_s3    : S3ChkSq 3670    := by decide +kernel
private theorem c3670_iso   : LeafIso 3670    := by decide +kernel
private theorem c3670_nof2  : NoF2ChkSq 3670  := by decide +kernel
private theorem c3670_nof3  : NoF3ChkSq 3670  := by decide +kernel
private theorem c3670_nof4z : NoF4zChkSq 3670 := by decide +kernel
theorem C'_3670 : C' 3670 :=
  ⟨c3670_sqf, c3670_range, c3670_ell, leafNSq_of_sq c3670_nsq, leafHAr_of_sq c3670_har,
   c3670_r, c3670_e', c3670_f1, leafS2_of_sq c3670_s2, leafS3_of_sq c3670_s3,
   c3670_iso, leafR8_of_sq c3670_nof2 c3670_nof3 c3670_nof4z⟩
theorem not_tile'_3670 (D : CongruentDissection 3670) : False :=
  not_tile_of_conditions' 3670 C'_3670 D

private theorem c3671_sqf   : LeafSqf 3671   := by decide +kernel
private theorem c3671_range : LeafRange 3671  := by decide +kernel
private theorem c3671_ell   : LeafEll 3671    := by decide +kernel
private theorem c3671_nsq   : NSqChkSq 3671   := by decide +kernel
private theorem c3671_har   : HArithChkSq 3671 := by decide +kernel
private theorem c3671_r     : LeafR 3671      := by decide +kernel
private theorem c3671_e'    : LeafE' 3671     := by decide +kernel
private theorem c3671_f1    : LeafF1 3671     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3671_s2    : S2ChkSq 3671    := by decide +kernel
private theorem c3671_s3    : S3ChkSq 3671    := by decide +kernel
private theorem c3671_iso   : LeafIso 3671    := by decide +kernel
private theorem c3671_nof2  : NoF2ChkSq 3671  := by decide +kernel
private theorem c3671_nof3  : NoF3ChkSq 3671  := by decide +kernel
private theorem c3671_nof4z : NoF4zChkSq 3671 := by decide +kernel
theorem C'_3671 : C' 3671 :=
  ⟨c3671_sqf, c3671_range, c3671_ell, leafNSq_of_sq c3671_nsq, leafHAr_of_sq c3671_har,
   c3671_r, c3671_e', c3671_f1, leafS2_of_sq c3671_s2, leafS3_of_sq c3671_s3,
   c3671_iso, leafR8_of_sq c3671_nof2 c3671_nof3 c3671_nof4z⟩
theorem not_tile'_3671 (D : CongruentDissection 3671) : False :=
  not_tile_of_conditions' 3671 C'_3671 D

private theorem c3674_sqf   : LeafSqf 3674   := by decide +kernel
private theorem c3674_range : LeafRange 3674  := by decide +kernel
private theorem c3674_ell   : LeafEll 3674    := by decide +kernel
private theorem c3674_nsq   : NSqChkSq 3674   := by decide +kernel
private theorem c3674_har   : HArithChkSq 3674 := by decide +kernel
private theorem c3674_r     : LeafR 3674      := by decide +kernel
private theorem c3674_e'    : LeafE' 3674     := by decide +kernel
private theorem c3674_f1    : LeafF1 3674     := Or.inl (by decide)
private theorem c3674_s2    : S2ChkSq 3674    := by decide +kernel
private theorem c3674_s3    : S3ChkSq 3674    := by decide +kernel
private theorem c3674_iso   : LeafIso 3674    := by decide +kernel
private theorem c3674_nof2  : NoF2ChkSq 3674  := by decide +kernel
private theorem c3674_nof3  : NoF3ChkSq 3674  := by decide +kernel
private theorem c3674_nof4z : NoF4zChkSq 3674 := by decide +kernel
theorem C'_3674 : C' 3674 :=
  ⟨c3674_sqf, c3674_range, c3674_ell, leafNSq_of_sq c3674_nsq, leafHAr_of_sq c3674_har,
   c3674_r, c3674_e', c3674_f1, leafS2_of_sq c3674_s2, leafS3_of_sq c3674_s3,
   c3674_iso, leafR8_of_sq c3674_nof2 c3674_nof3 c3674_nof4z⟩
theorem not_tile'_3674 (D : CongruentDissection 3674) : False :=
  not_tile_of_conditions' 3674 C'_3674 D

end Erdos634.Draft.AllN2

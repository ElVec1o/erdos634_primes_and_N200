/- AllN2Check44: N = 1771, 1779, 1793, 1795, 1797
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1771_sqf   : LeafSqf 1771   := by decide +kernel
private theorem c1771_range : LeafRange 1771  := by decide +kernel
private theorem c1771_ell   : LeafEll 1771    := by decide +kernel
private theorem c1771_nsq   : NSqChkSq 1771   := by decide +kernel
private theorem c1771_har   : HArithChkSq 1771 := by decide +kernel
private theorem c1771_r     : LeafR 1771      := by decide +kernel
private theorem c1771_e'    : LeafE' 1771     := by decide +kernel
private theorem c1771_f1    : LeafF1 1771     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1771_s2    : S2ChkSq 1771    := by decide +kernel
private theorem c1771_s3    : S3ChkSq 1771    := by decide +kernel
private theorem c1771_iso   : LeafIso 1771    := by decide +kernel
private theorem c1771_nof2  : NoF2ChkSq 1771  := by decide +kernel
private theorem c1771_nof3  : NoF3ChkSq 1771  := by decide +kernel
private theorem c1771_nof4z : NoF4zChkSq 1771 := by decide +kernel
theorem C'_1771 : C' 1771 :=
  ⟨c1771_sqf, c1771_range, c1771_ell, leafNSq_of_sq c1771_nsq, leafHAr_of_sq c1771_har,
   c1771_r, c1771_e', c1771_f1, leafS2_of_sq c1771_s2, leafS3_of_sq c1771_s3,
   c1771_iso, leafR8_of_sq c1771_nof2 c1771_nof3 c1771_nof4z⟩
theorem not_tile'_1771 (D : CongruentDissection 1771) : False :=
  not_tile_of_conditions' 1771 C'_1771 D

private theorem c1779_sqf   : LeafSqf 1779   := by decide +kernel
private theorem c1779_range : LeafRange 1779  := by decide +kernel
private theorem c1779_ell   : LeafEll 1779    := by decide +kernel
private theorem c1779_nsq   : NSqChkSq 1779   := by decide +kernel
private theorem c1779_har   : HArithChkSq 1779 := by decide +kernel
private theorem c1779_r     : LeafR 1779      := by decide +kernel
private theorem c1779_e'    : LeafE' 1779     := by decide +kernel
private theorem c1779_f1    : LeafF1 1779     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1779_s2    : S2ChkSq 1779    := by decide +kernel
private theorem c1779_s3    : S3ChkSq 1779    := by decide +kernel
private theorem c1779_iso   : LeafIso 1779    := by decide +kernel
private theorem c1779_nof2  : NoF2ChkSq 1779  := by decide +kernel
private theorem c1779_nof3  : NoF3ChkSq 1779  := by decide +kernel
private theorem c1779_nof4z : NoF4zChkSq 1779 := by decide +kernel
theorem C'_1779 : C' 1779 :=
  ⟨c1779_sqf, c1779_range, c1779_ell, leafNSq_of_sq c1779_nsq, leafHAr_of_sq c1779_har,
   c1779_r, c1779_e', c1779_f1, leafS2_of_sq c1779_s2, leafS3_of_sq c1779_s3,
   c1779_iso, leafR8_of_sq c1779_nof2 c1779_nof3 c1779_nof4z⟩
theorem not_tile'_1779 (D : CongruentDissection 1779) : False :=
  not_tile_of_conditions' 1779 C'_1779 D

private theorem c1793_sqf   : LeafSqf 1793   := by decide +kernel
private theorem c1793_range : LeafRange 1793  := by decide +kernel
private theorem c1793_ell   : LeafEll 1793    := by decide +kernel
private theorem c1793_nsq   : NSqChkSq 1793   := by decide +kernel
private theorem c1793_har   : HArithChkSq 1793 := by decide +kernel
private theorem c1793_r     : LeafR 1793      := by decide +kernel
private theorem c1793_e'    : LeafE' 1793     := by decide +kernel
private theorem c1793_f1    : LeafF1 1793     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1793_s2    : S2ChkSq 1793    := by decide +kernel
private theorem c1793_s3    : S3ChkSq 1793    := by decide +kernel
private theorem c1793_iso   : LeafIso 1793    := by decide +kernel
private theorem c1793_nof2  : NoF2ChkSq 1793  := by decide +kernel
private theorem c1793_nof3  : NoF3ChkSq 1793  := by decide +kernel
private theorem c1793_nof4z : NoF4zChkSq 1793 := by decide +kernel
theorem C'_1793 : C' 1793 :=
  ⟨c1793_sqf, c1793_range, c1793_ell, leafNSq_of_sq c1793_nsq, leafHAr_of_sq c1793_har,
   c1793_r, c1793_e', c1793_f1, leafS2_of_sq c1793_s2, leafS3_of_sq c1793_s3,
   c1793_iso, leafR8_of_sq c1793_nof2 c1793_nof3 c1793_nof4z⟩
theorem not_tile'_1793 (D : CongruentDissection 1793) : False :=
  not_tile_of_conditions' 1793 C'_1793 D

private theorem c1795_sqf   : LeafSqf 1795   := by decide +kernel
private theorem c1795_range : LeafRange 1795  := by decide +kernel
private theorem c1795_ell   : LeafEll 1795    := by decide +kernel
private theorem c1795_nsq   : NSqChkSq 1795   := by decide +kernel
private theorem c1795_har   : HArithChkSq 1795 := by decide +kernel
private theorem c1795_r     : LeafR 1795      := by decide +kernel
private theorem c1795_e'    : LeafE' 1795     := by decide +kernel
private theorem c1795_f1    : LeafF1 1795     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1795_s2    : S2ChkSq 1795    := by decide +kernel
private theorem c1795_s3    : S3ChkSq 1795    := by decide +kernel
private theorem c1795_iso   : LeafIso 1795    := by decide +kernel
private theorem c1795_nof2  : NoF2ChkSq 1795  := by decide +kernel
private theorem c1795_nof3  : NoF3ChkSq 1795  := by decide +kernel
private theorem c1795_nof4z : NoF4zChkSq 1795 := by decide +kernel
theorem C'_1795 : C' 1795 :=
  ⟨c1795_sqf, c1795_range, c1795_ell, leafNSq_of_sq c1795_nsq, leafHAr_of_sq c1795_har,
   c1795_r, c1795_e', c1795_f1, leafS2_of_sq c1795_s2, leafS3_of_sq c1795_s3,
   c1795_iso, leafR8_of_sq c1795_nof2 c1795_nof3 c1795_nof4z⟩
theorem not_tile'_1795 (D : CongruentDissection 1795) : False :=
  not_tile_of_conditions' 1795 C'_1795 D

private theorem c1797_sqf   : LeafSqf 1797   := by decide +kernel
private theorem c1797_range : LeafRange 1797  := by decide +kernel
private theorem c1797_ell   : LeafEll 1797    := by decide +kernel
private theorem c1797_nsq   : NSqChkSq 1797   := by decide +kernel
private theorem c1797_har   : HArithChkSq 1797 := by decide +kernel
private theorem c1797_r     : LeafR 1797      := by decide +kernel
private theorem c1797_e'    : LeafE' 1797     := by decide +kernel
private theorem c1797_f1    : LeafF1 1797     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1797_s2    : S2ChkSq 1797    := by decide +kernel
private theorem c1797_s3    : S3ChkSq 1797    := by decide +kernel
private theorem c1797_iso   : LeafIso 1797    := by decide +kernel
private theorem c1797_nof2  : NoF2ChkSq 1797  := by decide +kernel
private theorem c1797_nof3  : NoF3ChkSq 1797  := by decide +kernel
private theorem c1797_nof4z : NoF4zChkSq 1797 := by decide +kernel
theorem C'_1797 : C' 1797 :=
  ⟨c1797_sqf, c1797_range, c1797_ell, leafNSq_of_sq c1797_nsq, leafHAr_of_sq c1797_har,
   c1797_r, c1797_e', c1797_f1, leafS2_of_sq c1797_s2, leafS3_of_sq c1797_s3,
   c1797_iso, leafR8_of_sq c1797_nof2 c1797_nof3 c1797_nof4z⟩
theorem not_tile'_1797 (D : CongruentDissection 1797) : False :=
  not_tile_of_conditions' 1797 C'_1797 D

end Erdos634.Draft.AllN2

/- AllN2Check36: N = 1463, 1473, 1477, 1495, 1497
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1463_sqf   : LeafSqf 1463   := by decide +kernel
private theorem c1463_range : LeafRange 1463  := by decide +kernel
private theorem c1463_ell   : LeafEll 1463    := by decide +kernel
private theorem c1463_nsq   : NSqChkSq 1463   := by decide +kernel
private theorem c1463_har   : HArithChkSq 1463 := by decide +kernel
private theorem c1463_r     : LeafR 1463      := by decide +kernel
private theorem c1463_e'    : LeafE' 1463     := by decide +kernel
private theorem c1463_f1    : LeafF1 1463     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1463_s2    : S2ChkSq 1463    := by decide +kernel
private theorem c1463_s3    : S3ChkSq 1463    := by decide +kernel
private theorem c1463_iso   : LeafIso 1463    := by decide +kernel
private theorem c1463_nof2  : NoF2ChkSq 1463  := by decide +kernel
private theorem c1463_nof3  : NoF3ChkSq 1463  := by decide +kernel
private theorem c1463_nof4z : NoF4zChkSq 1463 := by decide +kernel
theorem C'_1463 : C' 1463 :=
  ⟨c1463_sqf, c1463_range, c1463_ell, leafNSq_of_sq c1463_nsq, leafHAr_of_sq c1463_har,
   c1463_r, c1463_e', c1463_f1, leafS2_of_sq c1463_s2, leafS3_of_sq c1463_s3,
   c1463_iso, leafR8_of_sq c1463_nof2 c1463_nof3 c1463_nof4z⟩
theorem not_tile'_1463 (D : CongruentDissection 1463) : False :=
  not_tile_of_conditions' 1463 C'_1463 D

private theorem c1473_sqf   : LeafSqf 1473   := by decide +kernel
private theorem c1473_range : LeafRange 1473  := by decide +kernel
private theorem c1473_ell   : LeafEll 1473    := by decide +kernel
private theorem c1473_nsq   : NSqChkSq 1473   := by decide +kernel
private theorem c1473_har   : HArithChkSq 1473 := by decide +kernel
private theorem c1473_r     : LeafR 1473      := by decide +kernel
private theorem c1473_e'    : LeafE' 1473     := by decide +kernel
private theorem c1473_f1    : LeafF1 1473     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1473_s2    : S2ChkSq 1473    := by decide +kernel
private theorem c1473_s3    : S3ChkSq 1473    := by decide +kernel
private theorem c1473_iso   : LeafIso 1473    := by decide +kernel
private theorem c1473_nof2  : NoF2ChkSq 1473  := by decide +kernel
private theorem c1473_nof3  : NoF3ChkSq 1473  := by decide +kernel
private theorem c1473_nof4z : NoF4zChkSq 1473 := by decide +kernel
theorem C'_1473 : C' 1473 :=
  ⟨c1473_sqf, c1473_range, c1473_ell, leafNSq_of_sq c1473_nsq, leafHAr_of_sq c1473_har,
   c1473_r, c1473_e', c1473_f1, leafS2_of_sq c1473_s2, leafS3_of_sq c1473_s3,
   c1473_iso, leafR8_of_sq c1473_nof2 c1473_nof3 c1473_nof4z⟩
theorem not_tile'_1473 (D : CongruentDissection 1473) : False :=
  not_tile_of_conditions' 1473 C'_1473 D

private theorem c1477_sqf   : LeafSqf 1477   := by decide +kernel
private theorem c1477_range : LeafRange 1477  := by decide +kernel
private theorem c1477_ell   : LeafEll 1477    := by decide +kernel
private theorem c1477_nsq   : NSqChkSq 1477   := by decide +kernel
private theorem c1477_har   : HArithChkSq 1477 := by decide +kernel
private theorem c1477_r     : LeafR 1477      := by decide +kernel
private theorem c1477_e'    : LeafE' 1477     := by decide +kernel
private theorem c1477_f1    : LeafF1 1477     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1477_s2    : S2ChkSq 1477    := by decide +kernel
private theorem c1477_s3    : S3ChkSq 1477    := by decide +kernel
private theorem c1477_iso   : LeafIso 1477    := by decide +kernel
private theorem c1477_nof2  : NoF2ChkSq 1477  := by decide +kernel
private theorem c1477_nof3  : NoF3ChkSq 1477  := by decide +kernel
private theorem c1477_nof4z : NoF4zChkSq 1477 := by decide +kernel
theorem C'_1477 : C' 1477 :=
  ⟨c1477_sqf, c1477_range, c1477_ell, leafNSq_of_sq c1477_nsq, leafHAr_of_sq c1477_har,
   c1477_r, c1477_e', c1477_f1, leafS2_of_sq c1477_s2, leafS3_of_sq c1477_s3,
   c1477_iso, leafR8_of_sq c1477_nof2 c1477_nof3 c1477_nof4z⟩
theorem not_tile'_1477 (D : CongruentDissection 1477) : False :=
  not_tile_of_conditions' 1477 C'_1477 D

private theorem c1495_sqf   : LeafSqf 1495   := by decide +kernel
private theorem c1495_range : LeafRange 1495  := by decide +kernel
private theorem c1495_ell   : LeafEll 1495    := by decide +kernel
private theorem c1495_nsq   : NSqChkSq 1495   := by decide +kernel
private theorem c1495_har   : HArithChkSq 1495 := by decide +kernel
private theorem c1495_r     : LeafR 1495      := by decide +kernel
private theorem c1495_e'    : LeafE' 1495     := by decide +kernel
private theorem c1495_f1    : LeafF1 1495     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1495_s2    : S2ChkSq 1495    := by decide +kernel
private theorem c1495_s3    : S3ChkSq 1495    := by decide +kernel
private theorem c1495_iso   : LeafIso 1495    := by decide +kernel
private theorem c1495_nof2  : NoF2ChkSq 1495  := by decide +kernel
private theorem c1495_nof3  : NoF3ChkSq 1495  := by decide +kernel
private theorem c1495_nof4z : NoF4zChkSq 1495 := by decide +kernel
theorem C'_1495 : C' 1495 :=
  ⟨c1495_sqf, c1495_range, c1495_ell, leafNSq_of_sq c1495_nsq, leafHAr_of_sq c1495_har,
   c1495_r, c1495_e', c1495_f1, leafS2_of_sq c1495_s2, leafS3_of_sq c1495_s3,
   c1495_iso, leafR8_of_sq c1495_nof2 c1495_nof3 c1495_nof4z⟩
theorem not_tile'_1495 (D : CongruentDissection 1495) : False :=
  not_tile_of_conditions' 1495 C'_1495 D

private theorem c1497_sqf   : LeafSqf 1497   := by decide +kernel
private theorem c1497_range : LeafRange 1497  := by decide +kernel
private theorem c1497_ell   : LeafEll 1497    := by decide +kernel
private theorem c1497_nsq   : NSqChkSq 1497   := by decide +kernel
private theorem c1497_har   : HArithChkSq 1497 := by decide +kernel
private theorem c1497_r     : LeafR 1497      := by decide +kernel
private theorem c1497_e'    : LeafE' 1497     := by decide +kernel
private theorem c1497_f1    : LeafF1 1497     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1497_s2    : S2ChkSq 1497    := by decide +kernel
private theorem c1497_s3    : S3ChkSq 1497    := by decide +kernel
private theorem c1497_iso   : LeafIso 1497    := by decide +kernel
private theorem c1497_nof2  : NoF2ChkSq 1497  := by decide +kernel
private theorem c1497_nof3  : NoF3ChkSq 1497  := by decide +kernel
private theorem c1497_nof4z : NoF4zChkSq 1497 := by decide +kernel
theorem C'_1497 : C' 1497 :=
  ⟨c1497_sqf, c1497_range, c1497_ell, leafNSq_of_sq c1497_nsq, leafHAr_of_sq c1497_har,
   c1497_r, c1497_e', c1497_f1, leafS2_of_sq c1497_s2, leafS3_of_sq c1497_s3,
   c1497_iso, leafR8_of_sq c1497_nof2 c1497_nof3 c1497_nof4z⟩
theorem not_tile'_1497 (D : CongruentDissection 1497) : False :=
  not_tile_of_conditions' 1497 C'_1497 D

end Erdos634.Draft.AllN2

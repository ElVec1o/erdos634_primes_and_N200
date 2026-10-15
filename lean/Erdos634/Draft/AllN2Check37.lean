/- AllN2Check37: N = 1505, 1507, 1509, 1527, 1529
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1505_sqf   : LeafSqf 1505   := by decide +kernel
private theorem c1505_range : LeafRange 1505  := by decide +kernel
private theorem c1505_ell   : LeafEll 1505    := by decide +kernel
private theorem c1505_nsq   : NSqChkSq 1505   := by decide +kernel
private theorem c1505_har   : HArithChkSq 1505 := by decide +kernel
private theorem c1505_r     : LeafR 1505      := by decide +kernel
private theorem c1505_e'    : LeafE' 1505     := by decide +kernel
private theorem c1505_f1    : LeafF1 1505     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1505_s2    : S2ChkSq 1505    := by decide +kernel
private theorem c1505_s3    : S3ChkSq 1505    := by decide +kernel
private theorem c1505_iso   : LeafIso 1505    := by decide +kernel
private theorem c1505_nof2  : NoF2ChkSq 1505  := by decide +kernel
private theorem c1505_nof3  : NoF3ChkSq 1505  := by decide +kernel
private theorem c1505_nof4z : NoF4zChkSq 1505 := by decide +kernel
theorem C'_1505 : C' 1505 :=
  ⟨c1505_sqf, c1505_range, c1505_ell, leafNSq_of_sq c1505_nsq, leafHAr_of_sq c1505_har,
   c1505_r, c1505_e', c1505_f1, leafS2_of_sq c1505_s2, leafS3_of_sq c1505_s3,
   c1505_iso, leafR8_of_sq c1505_nof2 c1505_nof3 c1505_nof4z⟩
theorem not_tile'_1505 (D : CongruentDissection 1505) : False :=
  not_tile_of_conditions' 1505 C'_1505 D

private theorem c1507_sqf   : LeafSqf 1507   := by decide +kernel
private theorem c1507_range : LeafRange 1507  := by decide +kernel
private theorem c1507_ell   : LeafEll 1507    := by decide +kernel
private theorem c1507_nsq   : NSqChkSq 1507   := by decide +kernel
private theorem c1507_har   : HArithChkSq 1507 := by decide +kernel
private theorem c1507_r     : LeafR 1507      := by decide +kernel
private theorem c1507_e'    : LeafE' 1507     := by decide +kernel
private theorem c1507_f1    : LeafF1 1507     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1507_s2    : S2ChkSq 1507    := by decide +kernel
private theorem c1507_s3    : S3ChkSq 1507    := by decide +kernel
private theorem c1507_iso   : LeafIso 1507    := by decide +kernel
private theorem c1507_nof2  : NoF2ChkSq 1507  := by decide +kernel
private theorem c1507_nof3  : NoF3ChkSq 1507  := by decide +kernel
private theorem c1507_nof4z : NoF4zChkSq 1507 := by decide +kernel
theorem C'_1507 : C' 1507 :=
  ⟨c1507_sqf, c1507_range, c1507_ell, leafNSq_of_sq c1507_nsq, leafHAr_of_sq c1507_har,
   c1507_r, c1507_e', c1507_f1, leafS2_of_sq c1507_s2, leafS3_of_sq c1507_s3,
   c1507_iso, leafR8_of_sq c1507_nof2 c1507_nof3 c1507_nof4z⟩
theorem not_tile'_1507 (D : CongruentDissection 1507) : False :=
  not_tile_of_conditions' 1507 C'_1507 D

private theorem c1509_sqf   : LeafSqf 1509   := by decide +kernel
private theorem c1509_range : LeafRange 1509  := by decide +kernel
private theorem c1509_ell   : LeafEll 1509    := by decide +kernel
private theorem c1509_nsq   : NSqChkSq 1509   := by decide +kernel
private theorem c1509_har   : HArithChkSq 1509 := by decide +kernel
private theorem c1509_r     : LeafR 1509      := by decide +kernel
private theorem c1509_e'    : LeafE' 1509     := by decide +kernel
private theorem c1509_f1    : LeafF1 1509     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1509_s2    : S2ChkSq 1509    := by decide +kernel
private theorem c1509_s3    : S3ChkSq 1509    := by decide +kernel
private theorem c1509_iso   : LeafIso 1509    := by decide +kernel
private theorem c1509_nof2  : NoF2ChkSq 1509  := by decide +kernel
private theorem c1509_nof3  : NoF3ChkSq 1509  := by decide +kernel
private theorem c1509_nof4z : NoF4zChkSq 1509 := by decide +kernel
theorem C'_1509 : C' 1509 :=
  ⟨c1509_sqf, c1509_range, c1509_ell, leafNSq_of_sq c1509_nsq, leafHAr_of_sq c1509_har,
   c1509_r, c1509_e', c1509_f1, leafS2_of_sq c1509_s2, leafS3_of_sq c1509_s3,
   c1509_iso, leafR8_of_sq c1509_nof2 c1509_nof3 c1509_nof4z⟩
theorem not_tile'_1509 (D : CongruentDissection 1509) : False :=
  not_tile_of_conditions' 1509 C'_1509 D

private theorem c1527_sqf   : LeafSqf 1527   := by decide +kernel
private theorem c1527_range : LeafRange 1527  := by decide +kernel
private theorem c1527_ell   : LeafEll 1527    := by decide +kernel
private theorem c1527_nsq   : NSqChkSq 1527   := by decide +kernel
private theorem c1527_har   : HArithChkSq 1527 := by decide +kernel
private theorem c1527_r     : LeafR 1527      := by decide +kernel
private theorem c1527_e'    : LeafE' 1527     := by decide +kernel
private theorem c1527_f1    : LeafF1 1527     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1527_s2    : S2ChkSq 1527    := by decide +kernel
private theorem c1527_s3    : S3ChkSq 1527    := by decide +kernel
private theorem c1527_iso   : LeafIso 1527    := by decide +kernel
private theorem c1527_nof2  : NoF2ChkSq 1527  := by decide +kernel
private theorem c1527_nof3  : NoF3ChkSq 1527  := by decide +kernel
private theorem c1527_nof4z : NoF4zChkSq 1527 := by decide +kernel
theorem C'_1527 : C' 1527 :=
  ⟨c1527_sqf, c1527_range, c1527_ell, leafNSq_of_sq c1527_nsq, leafHAr_of_sq c1527_har,
   c1527_r, c1527_e', c1527_f1, leafS2_of_sq c1527_s2, leafS3_of_sq c1527_s3,
   c1527_iso, leafR8_of_sq c1527_nof2 c1527_nof3 c1527_nof4z⟩
theorem not_tile'_1527 (D : CongruentDissection 1527) : False :=
  not_tile_of_conditions' 1527 C'_1527 D

private theorem c1529_sqf   : LeafSqf 1529   := by decide +kernel
private theorem c1529_range : LeafRange 1529  := by decide +kernel
private theorem c1529_ell   : LeafEll 1529    := by decide +kernel
private theorem c1529_nsq   : NSqChkSq 1529   := by decide +kernel
private theorem c1529_har   : HArithChkSq 1529 := by decide +kernel
private theorem c1529_r     : LeafR 1529      := by decide +kernel
private theorem c1529_e'    : LeafE' 1529     := by decide +kernel
private theorem c1529_f1    : LeafF1 1529     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1529_s2    : S2ChkSq 1529    := by decide +kernel
private theorem c1529_s3    : S3ChkSq 1529    := by decide +kernel
private theorem c1529_iso   : LeafIso 1529    := by decide +kernel
private theorem c1529_nof2  : NoF2ChkSq 1529  := by decide +kernel
private theorem c1529_nof3  : NoF3ChkSq 1529  := by decide +kernel
private theorem c1529_nof4z : NoF4zChkSq 1529 := by decide +kernel
theorem C'_1529 : C' 1529 :=
  ⟨c1529_sqf, c1529_range, c1529_ell, leafNSq_of_sq c1529_nsq, leafHAr_of_sq c1529_har,
   c1529_r, c1529_e', c1529_f1, leafS2_of_sq c1529_s2, leafS3_of_sq c1529_s3,
   c1529_iso, leafR8_of_sq c1529_nof2 c1529_nof3 c1529_nof4z⟩
theorem not_tile'_1529 (D : CongruentDissection 1529) : False :=
  not_tile_of_conditions' 1529 C'_1529 D

end Erdos634.Draft.AllN2

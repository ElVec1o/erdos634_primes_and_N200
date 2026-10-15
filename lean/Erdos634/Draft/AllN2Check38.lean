/- AllN2Check38: N = 1535, 1547, 1555, 1561, 1563
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1535_sqf   : LeafSqf 1535   := by decide +kernel
private theorem c1535_range : LeafRange 1535  := by decide +kernel
private theorem c1535_ell   : LeafEll 1535    := by decide +kernel
private theorem c1535_nsq   : NSqChkSq 1535   := by decide +kernel
private theorem c1535_har   : HArithChkSq 1535 := by decide +kernel
private theorem c1535_r     : LeafR 1535      := by decide +kernel
private theorem c1535_e'    : LeafE' 1535     := by decide +kernel
private theorem c1535_f1    : LeafF1 1535     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1535_s2    : S2ChkSq 1535    := by decide +kernel
private theorem c1535_s3    : S3ChkSq 1535    := by decide +kernel
private theorem c1535_iso   : LeafIso 1535    := by decide +kernel
private theorem c1535_nof2  : NoF2ChkSq 1535  := by decide +kernel
private theorem c1535_nof3  : NoF3ChkSq 1535  := by decide +kernel
private theorem c1535_nof4z : NoF4zChkSq 1535 := by decide +kernel
theorem C'_1535 : C' 1535 :=
  ⟨c1535_sqf, c1535_range, c1535_ell, leafNSq_of_sq c1535_nsq, leafHAr_of_sq c1535_har,
   c1535_r, c1535_e', c1535_f1, leafS2_of_sq c1535_s2, leafS3_of_sq c1535_s3,
   c1535_iso, leafR8_of_sq c1535_nof2 c1535_nof3 c1535_nof4z⟩
theorem not_tile'_1535 (D : CongruentDissection 1535) : False :=
  not_tile_of_conditions' 1535 C'_1535 D

private theorem c1547_sqf   : LeafSqf 1547   := by decide +kernel
private theorem c1547_range : LeafRange 1547  := by decide +kernel
private theorem c1547_ell   : LeafEll 1547    := by decide +kernel
private theorem c1547_nsq   : NSqChkSq 1547   := by decide +kernel
private theorem c1547_har   : HArithChkSq 1547 := by decide +kernel
private theorem c1547_r     : LeafR 1547      := by decide +kernel
private theorem c1547_e'    : LeafE' 1547     := by decide +kernel
private theorem c1547_f1    : LeafF1 1547     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1547_s2    : S2ChkSq 1547    := by decide +kernel
private theorem c1547_s3    : S3ChkSq 1547    := by decide +kernel
private theorem c1547_iso   : LeafIso 1547    := by decide +kernel
private theorem c1547_nof2  : NoF2ChkSq 1547  := by decide +kernel
private theorem c1547_nof3  : NoF3ChkSq 1547  := by decide +kernel
private theorem c1547_nof4z : NoF4zChkSq 1547 := by decide +kernel
theorem C'_1547 : C' 1547 :=
  ⟨c1547_sqf, c1547_range, c1547_ell, leafNSq_of_sq c1547_nsq, leafHAr_of_sq c1547_har,
   c1547_r, c1547_e', c1547_f1, leafS2_of_sq c1547_s2, leafS3_of_sq c1547_s3,
   c1547_iso, leafR8_of_sq c1547_nof2 c1547_nof3 c1547_nof4z⟩
theorem not_tile'_1547 (D : CongruentDissection 1547) : False :=
  not_tile_of_conditions' 1547 C'_1547 D

private theorem c1555_sqf   : LeafSqf 1555   := by decide +kernel
private theorem c1555_range : LeafRange 1555  := by decide +kernel
private theorem c1555_ell   : LeafEll 1555    := by decide +kernel
private theorem c1555_nsq   : NSqChkSq 1555   := by decide +kernel
private theorem c1555_har   : HArithChkSq 1555 := by decide +kernel
private theorem c1555_r     : LeafR 1555      := by decide +kernel
private theorem c1555_e'    : LeafE' 1555     := by decide +kernel
private theorem c1555_f1    : LeafF1 1555     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1555_s2    : S2ChkSq 1555    := by decide +kernel
private theorem c1555_s3    : S3ChkSq 1555    := by decide +kernel
private theorem c1555_iso   : LeafIso 1555    := by decide +kernel
private theorem c1555_nof2  : NoF2ChkSq 1555  := by decide +kernel
private theorem c1555_nof3  : NoF3ChkSq 1555  := by decide +kernel
private theorem c1555_nof4z : NoF4zChkSq 1555 := by decide +kernel
theorem C'_1555 : C' 1555 :=
  ⟨c1555_sqf, c1555_range, c1555_ell, leafNSq_of_sq c1555_nsq, leafHAr_of_sq c1555_har,
   c1555_r, c1555_e', c1555_f1, leafS2_of_sq c1555_s2, leafS3_of_sq c1555_s3,
   c1555_iso, leafR8_of_sq c1555_nof2 c1555_nof3 c1555_nof4z⟩
theorem not_tile'_1555 (D : CongruentDissection 1555) : False :=
  not_tile_of_conditions' 1555 C'_1555 D

private theorem c1561_sqf   : LeafSqf 1561   := by decide +kernel
private theorem c1561_range : LeafRange 1561  := by decide +kernel
private theorem c1561_ell   : LeafEll 1561    := by decide +kernel
private theorem c1561_nsq   : NSqChkSq 1561   := by decide +kernel
private theorem c1561_har   : HArithChkSq 1561 := by decide +kernel
private theorem c1561_r     : LeafR 1561      := by decide +kernel
private theorem c1561_e'    : LeafE' 1561     := by decide +kernel
private theorem c1561_f1    : LeafF1 1561     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1561_s2    : S2ChkSq 1561    := by decide +kernel
private theorem c1561_s3    : S3ChkSq 1561    := by decide +kernel
private theorem c1561_iso   : LeafIso 1561    := by decide +kernel
private theorem c1561_nof2  : NoF2ChkSq 1561  := by decide +kernel
private theorem c1561_nof3  : NoF3ChkSq 1561  := by decide +kernel
private theorem c1561_nof4z : NoF4zChkSq 1561 := by decide +kernel
theorem C'_1561 : C' 1561 :=
  ⟨c1561_sqf, c1561_range, c1561_ell, leafNSq_of_sq c1561_nsq, leafHAr_of_sq c1561_har,
   c1561_r, c1561_e', c1561_f1, leafS2_of_sq c1561_s2, leafS3_of_sq c1561_s3,
   c1561_iso, leafR8_of_sq c1561_nof2 c1561_nof3 c1561_nof4z⟩
theorem not_tile'_1561 (D : CongruentDissection 1561) : False :=
  not_tile_of_conditions' 1561 C'_1561 D

private theorem c1563_sqf   : LeafSqf 1563   := by decide +kernel
private theorem c1563_range : LeafRange 1563  := by decide +kernel
private theorem c1563_ell   : LeafEll 1563    := by decide +kernel
private theorem c1563_nsq   : NSqChkSq 1563   := by decide +kernel
private theorem c1563_har   : HArithChkSq 1563 := by decide +kernel
private theorem c1563_r     : LeafR 1563      := by decide +kernel
private theorem c1563_e'    : LeafE' 1563     := by decide +kernel
private theorem c1563_f1    : LeafF1 1563     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1563_s2    : S2ChkSq 1563    := by decide +kernel
private theorem c1563_s3    : S3ChkSq 1563    := by decide +kernel
private theorem c1563_iso   : LeafIso 1563    := by decide +kernel
private theorem c1563_nof2  : NoF2ChkSq 1563  := by decide +kernel
private theorem c1563_nof3  : NoF3ChkSq 1563  := by decide +kernel
private theorem c1563_nof4z : NoF4zChkSq 1563 := by decide +kernel
theorem C'_1563 : C' 1563 :=
  ⟨c1563_sqf, c1563_range, c1563_ell, leafNSq_of_sq c1563_nsq, leafHAr_of_sq c1563_har,
   c1563_r, c1563_e', c1563_f1, leafS2_of_sq c1563_s2, leafS3_of_sq c1563_s3,
   c1563_iso, leafR8_of_sq c1563_nof2 c1563_nof3 c1563_nof4z⟩
theorem not_tile'_1563 (D : CongruentDissection 1563) : False :=
  not_tile_of_conditions' 1563 C'_1563 D

end Erdos634.Draft.AllN2

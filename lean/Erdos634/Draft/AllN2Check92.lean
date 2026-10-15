/- AllN2Check92: N = 2510, 2513, 2514, 2515, 2517
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2510_sqf   : LeafSqf 2510   := by decide +kernel
private theorem c2510_range : LeafRange 2510  := by decide +kernel
private theorem c2510_ell   : LeafEll 2510    := by decide +kernel
private theorem c2510_nsq   : NSqChkSq 2510   := by decide +kernel
private theorem c2510_har   : HArithChkSq 2510 := by decide +kernel
private theorem c2510_r     : LeafR 2510      := by decide +kernel
private theorem c2510_e'    : LeafE' 2510     := by decide +kernel
private theorem c2510_f1    : LeafF1 2510     := Or.inl (by decide)
private theorem c2510_s2    : S2ChkSq 2510    := by decide +kernel
private theorem c2510_s3    : S3ChkSq 2510    := by decide +kernel
private theorem c2510_iso   : LeafIso 2510    := by decide +kernel
private theorem c2510_nof2  : NoF2ChkSq 2510  := by decide +kernel
private theorem c2510_nof3  : NoF3ChkSq 2510  := by decide +kernel
private theorem c2510_nof4z : NoF4zChkSq 2510 := by decide +kernel
theorem C'_2510 : C' 2510 :=
  ⟨c2510_sqf, c2510_range, c2510_ell, leafNSq_of_sq c2510_nsq, leafHAr_of_sq c2510_har,
   c2510_r, c2510_e', c2510_f1, leafS2_of_sq c2510_s2, leafS3_of_sq c2510_s3,
   c2510_iso, leafR8_of_sq c2510_nof2 c2510_nof3 c2510_nof4z⟩
theorem not_tile'_2510 (D : CongruentDissection 2510) : False :=
  not_tile_of_conditions' 2510 C'_2510 D

private theorem c2513_sqf   : LeafSqf 2513   := by decide +kernel
private theorem c2513_range : LeafRange 2513  := by decide +kernel
private theorem c2513_ell   : LeafEll 2513    := by decide +kernel
private theorem c2513_nsq   : NSqChkSq 2513   := by decide +kernel
private theorem c2513_har   : HArithChkSq 2513 := by decide +kernel
private theorem c2513_r     : LeafR 2513      := by decide +kernel
private theorem c2513_e'    : LeafE' 2513     := by decide +kernel
private theorem c2513_f1    : LeafF1 2513     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2513_s2    : S2ChkSq 2513    := by decide +kernel
private theorem c2513_s3    : S3ChkSq 2513    := by decide +kernel
private theorem c2513_iso   : LeafIso 2513    := by decide +kernel
private theorem c2513_nof2  : NoF2ChkSq 2513  := by decide +kernel
private theorem c2513_nof3  : NoF3ChkSq 2513  := by decide +kernel
private theorem c2513_nof4z : NoF4zChkSq 2513 := by decide +kernel
theorem C'_2513 : C' 2513 :=
  ⟨c2513_sqf, c2513_range, c2513_ell, leafNSq_of_sq c2513_nsq, leafHAr_of_sq c2513_har,
   c2513_r, c2513_e', c2513_f1, leafS2_of_sq c2513_s2, leafS3_of_sq c2513_s3,
   c2513_iso, leafR8_of_sq c2513_nof2 c2513_nof3 c2513_nof4z⟩
theorem not_tile'_2513 (D : CongruentDissection 2513) : False :=
  not_tile_of_conditions' 2513 C'_2513 D

private theorem c2514_sqf   : LeafSqf 2514   := by decide +kernel
private theorem c2514_range : LeafRange 2514  := by decide +kernel
private theorem c2514_ell   : LeafEll 2514    := by decide +kernel
private theorem c2514_nsq   : NSqChkSq 2514   := by decide +kernel
private theorem c2514_har   : HArithChkSq 2514 := by decide +kernel
private theorem c2514_r     : LeafR 2514      := by decide +kernel
private theorem c2514_e'    : LeafE' 2514     := by decide +kernel
private theorem c2514_f1    : LeafF1 2514     := Or.inl (by decide)
private theorem c2514_s2    : S2ChkSq 2514    := by decide +kernel
private theorem c2514_s3    : S3ChkSq 2514    := by decide +kernel
private theorem c2514_iso   : LeafIso 2514    := by decide +kernel
private theorem c2514_nof2  : NoF2ChkSq 2514  := by decide +kernel
private theorem c2514_nof3  : NoF3ChkSq 2514  := by decide +kernel
private theorem c2514_nof4z : NoF4zChkSq 2514 := by decide +kernel
theorem C'_2514 : C' 2514 :=
  ⟨c2514_sqf, c2514_range, c2514_ell, leafNSq_of_sq c2514_nsq, leafHAr_of_sq c2514_har,
   c2514_r, c2514_e', c2514_f1, leafS2_of_sq c2514_s2, leafS3_of_sq c2514_s3,
   c2514_iso, leafR8_of_sq c2514_nof2 c2514_nof3 c2514_nof4z⟩
theorem not_tile'_2514 (D : CongruentDissection 2514) : False :=
  not_tile_of_conditions' 2514 C'_2514 D

private theorem c2515_sqf   : LeafSqf 2515   := by decide +kernel
private theorem c2515_range : LeafRange 2515  := by decide +kernel
private theorem c2515_ell   : LeafEll 2515    := by decide +kernel
private theorem c2515_nsq   : NSqChkSq 2515   := by decide +kernel
private theorem c2515_har   : HArithChkSq 2515 := by decide +kernel
private theorem c2515_r     : LeafR 2515      := by decide +kernel
private theorem c2515_e'    : LeafE' 2515     := by decide +kernel
private theorem c2515_f1    : LeafF1 2515     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2515_s2    : S2ChkSq 2515    := by decide +kernel
private theorem c2515_s3    : S3ChkSq 2515    := by decide +kernel
private theorem c2515_iso   : LeafIso 2515    := by decide +kernel
private theorem c2515_nof2  : NoF2ChkSq 2515  := by decide +kernel
private theorem c2515_nof3  : NoF3ChkSq 2515  := by decide +kernel
private theorem c2515_nof4z : NoF4zChkSq 2515 := by decide +kernel
theorem C'_2515 : C' 2515 :=
  ⟨c2515_sqf, c2515_range, c2515_ell, leafNSq_of_sq c2515_nsq, leafHAr_of_sq c2515_har,
   c2515_r, c2515_e', c2515_f1, leafS2_of_sq c2515_s2, leafS3_of_sq c2515_s3,
   c2515_iso, leafR8_of_sq c2515_nof2 c2515_nof3 c2515_nof4z⟩
theorem not_tile'_2515 (D : CongruentDissection 2515) : False :=
  not_tile_of_conditions' 2515 C'_2515 D

private theorem c2517_sqf   : LeafSqf 2517   := by decide +kernel
private theorem c2517_range : LeafRange 2517  := by decide +kernel
private theorem c2517_ell   : LeafEll 2517    := by decide +kernel
private theorem c2517_nsq   : NSqChkSq 2517   := by decide +kernel
private theorem c2517_har   : HArithChkSq 2517 := by decide +kernel
private theorem c2517_r     : LeafR 2517      := by decide +kernel
private theorem c2517_e'    : LeafE' 2517     := by decide +kernel
private theorem c2517_f1    : LeafF1 2517     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2517_s2    : S2ChkSq 2517    := by decide +kernel
private theorem c2517_s3    : S3ChkSq 2517    := by decide +kernel
private theorem c2517_iso   : LeafIso 2517    := by decide +kernel
private theorem c2517_nof2  : NoF2ChkSq 2517  := by decide +kernel
private theorem c2517_nof3  : NoF3ChkSq 2517  := by decide +kernel
private theorem c2517_nof4z : NoF4zChkSq 2517 := by decide +kernel
theorem C'_2517 : C' 2517 :=
  ⟨c2517_sqf, c2517_range, c2517_ell, leafNSq_of_sq c2517_nsq, leafHAr_of_sq c2517_har,
   c2517_r, c2517_e', c2517_f1, leafS2_of_sq c2517_s2, leafS3_of_sq c2517_s3,
   c2517_iso, leafR8_of_sq c2517_nof2 c2517_nof3 c2517_nof4z⟩
theorem not_tile'_2517 (D : CongruentDissection 2517) : False :=
  not_tile_of_conditions' 2517 C'_2517 D

end Erdos634.Draft.AllN2

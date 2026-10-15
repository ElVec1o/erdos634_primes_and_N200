/- AllN2Check87: N = 2454, 2455, 2459, 2461, 2462
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2454_sqf   : LeafSqf 2454   := by decide +kernel
private theorem c2454_range : LeafRange 2454  := by decide +kernel
private theorem c2454_ell   : LeafEll 2454    := by decide +kernel
private theorem c2454_nsq   : NSqChkSq 2454   := by decide +kernel
private theorem c2454_har   : HArithChkSq 2454 := by decide +kernel
private theorem c2454_r     : LeafR 2454      := by decide +kernel
private theorem c2454_e'    : LeafE' 2454     := by decide +kernel
private theorem c2454_f1    : LeafF1 2454     := Or.inl (by decide)
private theorem c2454_s2    : S2ChkSq 2454    := by decide +kernel
private theorem c2454_s3    : S3ChkSq 2454    := by decide +kernel
private theorem c2454_iso   : LeafIso 2454    := by decide +kernel
private theorem c2454_nof2  : NoF2ChkSq 2454  := by decide +kernel
private theorem c2454_nof3  : NoF3ChkSq 2454  := by decide +kernel
private theorem c2454_nof4z : NoF4zChkSq 2454 := by decide +kernel
theorem C'_2454 : C' 2454 :=
  ⟨c2454_sqf, c2454_range, c2454_ell, leafNSq_of_sq c2454_nsq, leafHAr_of_sq c2454_har,
   c2454_r, c2454_e', c2454_f1, leafS2_of_sq c2454_s2, leafS3_of_sq c2454_s3,
   c2454_iso, leafR8_of_sq c2454_nof2 c2454_nof3 c2454_nof4z⟩
theorem not_tile'_2454 (D : CongruentDissection 2454) : False :=
  not_tile_of_conditions' 2454 C'_2454 D

private theorem c2455_sqf   : LeafSqf 2455   := by decide +kernel
private theorem c2455_range : LeafRange 2455  := by decide +kernel
private theorem c2455_ell   : LeafEll 2455    := by decide +kernel
private theorem c2455_nsq   : NSqChkSq 2455   := by decide +kernel
private theorem c2455_har   : HArithChkSq 2455 := by decide +kernel
private theorem c2455_r     : LeafR 2455      := by decide +kernel
private theorem c2455_e'    : LeafE' 2455     := by decide +kernel
private theorem c2455_f1    : LeafF1 2455     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2455_s2    : S2ChkSq 2455    := by decide +kernel
private theorem c2455_s3    : S3ChkSq 2455    := by decide +kernel
private theorem c2455_iso   : LeafIso 2455    := by decide +kernel
private theorem c2455_nof2  : NoF2ChkSq 2455  := by decide +kernel
private theorem c2455_nof3  : NoF3ChkSq 2455  := by decide +kernel
private theorem c2455_nof4z : NoF4zChkSq 2455 := by decide +kernel
theorem C'_2455 : C' 2455 :=
  ⟨c2455_sqf, c2455_range, c2455_ell, leafNSq_of_sq c2455_nsq, leafHAr_of_sq c2455_har,
   c2455_r, c2455_e', c2455_f1, leafS2_of_sq c2455_s2, leafS3_of_sq c2455_s3,
   c2455_iso, leafR8_of_sq c2455_nof2 c2455_nof3 c2455_nof4z⟩
theorem not_tile'_2455 (D : CongruentDissection 2455) : False :=
  not_tile_of_conditions' 2455 C'_2455 D

private theorem c2459_sqf   : LeafSqf 2459   := by decide +kernel
private theorem c2459_range : LeafRange 2459  := by decide +kernel
private theorem c2459_ell   : LeafEll 2459    := by decide +kernel
private theorem c2459_nsq   : NSqChkSq 2459   := by decide +kernel
private theorem c2459_har   : HArithChkSq 2459 := by decide +kernel
private theorem c2459_r     : LeafR 2459      := by decide +kernel
private theorem c2459_e'    : LeafE' 2459     := by decide +kernel
private theorem c2459_f1    : LeafF1 2459     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2459_s2    : S2ChkSq 2459    := by decide +kernel
private theorem c2459_s3    : S3ChkSq 2459    := by decide +kernel
private theorem c2459_iso   : LeafIso 2459    := by decide +kernel
private theorem c2459_nof2  : NoF2ChkSq 2459  := by decide +kernel
private theorem c2459_nof3  : NoF3ChkSq 2459  := by decide +kernel
private theorem c2459_nof4z : NoF4zChkSq 2459 := by decide +kernel
theorem C'_2459 : C' 2459 :=
  ⟨c2459_sqf, c2459_range, c2459_ell, leafNSq_of_sq c2459_nsq, leafHAr_of_sq c2459_har,
   c2459_r, c2459_e', c2459_f1, leafS2_of_sq c2459_s2, leafS3_of_sq c2459_s3,
   c2459_iso, leafR8_of_sq c2459_nof2 c2459_nof3 c2459_nof4z⟩
theorem not_tile'_2459 (D : CongruentDissection 2459) : False :=
  not_tile_of_conditions' 2459 C'_2459 D

private theorem c2461_sqf   : LeafSqf 2461   := by decide +kernel
private theorem c2461_range : LeafRange 2461  := by decide +kernel
private theorem c2461_ell   : LeafEll 2461    := by decide +kernel
private theorem c2461_nsq   : NSqChkSq 2461   := by decide +kernel
private theorem c2461_har   : HArithChkSq 2461 := by decide +kernel
private theorem c2461_r     : LeafR 2461      := by decide +kernel
private theorem c2461_e'    : LeafE' 2461     := by decide +kernel
private theorem c2461_f1    : LeafF1 2461     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2461_s2    : S2ChkSq 2461    := by decide +kernel
private theorem c2461_s3    : S3ChkSq 2461    := by decide +kernel
private theorem c2461_iso   : LeafIso 2461    := by decide +kernel
private theorem c2461_nof2  : NoF2ChkSq 2461  := by decide +kernel
private theorem c2461_nof3  : NoF3ChkSq 2461  := by decide +kernel
private theorem c2461_nof4z : NoF4zChkSq 2461 := by decide +kernel
theorem C'_2461 : C' 2461 :=
  ⟨c2461_sqf, c2461_range, c2461_ell, leafNSq_of_sq c2461_nsq, leafHAr_of_sq c2461_har,
   c2461_r, c2461_e', c2461_f1, leafS2_of_sq c2461_s2, leafS3_of_sq c2461_s3,
   c2461_iso, leafR8_of_sq c2461_nof2 c2461_nof3 c2461_nof4z⟩
theorem not_tile'_2461 (D : CongruentDissection 2461) : False :=
  not_tile_of_conditions' 2461 C'_2461 D

private theorem c2462_sqf   : LeafSqf 2462   := by decide +kernel
private theorem c2462_range : LeafRange 2462  := by decide +kernel
private theorem c2462_ell   : LeafEll 2462    := by decide +kernel
private theorem c2462_nsq   : NSqChkSq 2462   := by decide +kernel
private theorem c2462_har   : HArithChkSq 2462 := by decide +kernel
private theorem c2462_r     : LeafR 2462      := by decide +kernel
private theorem c2462_e'    : LeafE' 2462     := by decide +kernel
private theorem c2462_f1    : LeafF1 2462     := Or.inl (by decide)
private theorem c2462_s2    : S2ChkSq 2462    := by decide +kernel
private theorem c2462_s3    : S3ChkSq 2462    := by decide +kernel
private theorem c2462_iso   : LeafIso 2462    := by decide +kernel
private theorem c2462_nof2  : NoF2ChkSq 2462  := by decide +kernel
private theorem c2462_nof3  : NoF3ChkSq 2462  := by decide +kernel
private theorem c2462_nof4z : NoF4zChkSq 2462 := by decide +kernel
theorem C'_2462 : C' 2462 :=
  ⟨c2462_sqf, c2462_range, c2462_ell, leafNSq_of_sq c2462_nsq, leafHAr_of_sq c2462_har,
   c2462_r, c2462_e', c2462_f1, leafS2_of_sq c2462_s2, leafS3_of_sq c2462_s3,
   c2462_iso, leafR8_of_sq c2462_nof2 c2462_nof3 c2462_nof4z⟩
theorem not_tile'_2462 (D : CongruentDissection 2462) : False :=
  not_tile_of_conditions' 2462 C'_2462 D

end Erdos634.Draft.AllN2

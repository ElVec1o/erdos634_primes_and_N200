/- AllN2Check167: N = 3470, 3473, 3478, 3486, 3487
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3470_sqf   : LeafSqf 3470   := by decide +kernel
private theorem c3470_range : LeafRange 3470  := by decide +kernel
private theorem c3470_ell   : LeafEll 3470    := by decide +kernel
private theorem c3470_nsq   : NSqChkSq 3470   := by decide +kernel
private theorem c3470_har   : HArithChkSq 3470 := by decide +kernel
private theorem c3470_r     : LeafR 3470      := by decide +kernel
private theorem c3470_e'    : LeafE' 3470     := by decide +kernel
private theorem c3470_f1    : LeafF1 3470     := Or.inl (by decide)
private theorem c3470_s2    : S2ChkSq 3470    := by decide +kernel
private theorem c3470_s3    : S3ChkSq 3470    := by decide +kernel
private theorem c3470_iso   : LeafIso 3470    := by decide +kernel
private theorem c3470_nof2  : NoF2ChkSq 3470  := by decide +kernel
private theorem c3470_nof3  : NoF3ChkSq 3470  := by decide +kernel
private theorem c3470_nof4z : NoF4zChkSq 3470 := by decide +kernel
theorem C'_3470 : C' 3470 :=
  ⟨c3470_sqf, c3470_range, c3470_ell, leafNSq_of_sq c3470_nsq, leafHAr_of_sq c3470_har,
   c3470_r, c3470_e', c3470_f1, leafS2_of_sq c3470_s2, leafS3_of_sq c3470_s3,
   c3470_iso, leafR8_of_sq c3470_nof2 c3470_nof3 c3470_nof4z⟩
theorem not_tile'_3470 (D : CongruentDissection 3470) : False :=
  not_tile_of_conditions' 3470 C'_3470 D

private theorem c3473_sqf   : LeafSqf 3473   := by decide +kernel
private theorem c3473_range : LeafRange 3473  := by decide +kernel
private theorem c3473_ell   : LeafEll 3473    := by decide +kernel
private theorem c3473_nsq   : NSqChkSq 3473   := by decide +kernel
private theorem c3473_har   : HArithChkSq 3473 := by decide +kernel
private theorem c3473_r     : LeafR 3473      := by decide +kernel
private theorem c3473_e'    : LeafE' 3473     := by decide +kernel
private theorem c3473_f1    : LeafF1 3473     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3473_s2    : S2ChkSq 3473    := by decide +kernel
private theorem c3473_s3    : S3ChkSq 3473    := by decide +kernel
private theorem c3473_iso   : LeafIso 3473    := by decide +kernel
private theorem c3473_nof2  : NoF2ChkSq 3473  := by decide +kernel
private theorem c3473_nof3  : NoF3ChkSq 3473  := by decide +kernel
private theorem c3473_nof4z : NoF4zChkSq 3473 := by decide +kernel
theorem C'_3473 : C' 3473 :=
  ⟨c3473_sqf, c3473_range, c3473_ell, leafNSq_of_sq c3473_nsq, leafHAr_of_sq c3473_har,
   c3473_r, c3473_e', c3473_f1, leafS2_of_sq c3473_s2, leafS3_of_sq c3473_s3,
   c3473_iso, leafR8_of_sq c3473_nof2 c3473_nof3 c3473_nof4z⟩
theorem not_tile'_3473 (D : CongruentDissection 3473) : False :=
  not_tile_of_conditions' 3473 C'_3473 D

private theorem c3478_sqf   : LeafSqf 3478   := by decide +kernel
private theorem c3478_range : LeafRange 3478  := by decide +kernel
private theorem c3478_ell   : LeafEll 3478    := by decide +kernel
private theorem c3478_nsq   : NSqChkSq 3478   := by decide +kernel
private theorem c3478_har   : HArithChkSq 3478 := by decide +kernel
private theorem c3478_r     : LeafR 3478      := by decide +kernel
private theorem c3478_e'    : LeafE' 3478     := by decide +kernel
private theorem c3478_f1    : LeafF1 3478     := Or.inl (by decide)
private theorem c3478_s2    : S2ChkSq 3478    := by decide +kernel
private theorem c3478_s3    : S3ChkSq 3478    := by decide +kernel
private theorem c3478_iso   : LeafIso 3478    := by decide +kernel
private theorem c3478_nof2  : NoF2ChkSq 3478  := by decide +kernel
private theorem c3478_nof3  : NoF3ChkSq 3478  := by decide +kernel
private theorem c3478_nof4z : NoF4zChkSq 3478 := by decide +kernel
theorem C'_3478 : C' 3478 :=
  ⟨c3478_sqf, c3478_range, c3478_ell, leafNSq_of_sq c3478_nsq, leafHAr_of_sq c3478_har,
   c3478_r, c3478_e', c3478_f1, leafS2_of_sq c3478_s2, leafS3_of_sq c3478_s3,
   c3478_iso, leafR8_of_sq c3478_nof2 c3478_nof3 c3478_nof4z⟩
theorem not_tile'_3478 (D : CongruentDissection 3478) : False :=
  not_tile_of_conditions' 3478 C'_3478 D

private theorem c3486_sqf   : LeafSqf 3486   := by decide +kernel
private theorem c3486_range : LeafRange 3486  := by decide +kernel
private theorem c3486_ell   : LeafEll 3486    := by decide +kernel
private theorem c3486_nsq   : NSqChkSq 3486   := by decide +kernel
private theorem c3486_har   : HArithChkSq 3486 := by decide +kernel
private theorem c3486_r     : LeafR 3486      := by decide +kernel
private theorem c3486_e'    : LeafE' 3486     := by decide +kernel
private theorem c3486_f1    : LeafF1 3486     := Or.inl (by decide)
private theorem c3486_s2    : S2ChkSq 3486    := by decide +kernel
private theorem c3486_s3    : S3ChkSq 3486    := by decide +kernel
private theorem c3486_iso   : LeafIso 3486    := by decide +kernel
private theorem c3486_nof2  : NoF2ChkSq 3486  := by decide +kernel
private theorem c3486_nof3  : NoF3ChkSq 3486  := by decide +kernel
private theorem c3486_nof4z : NoF4zChkSq 3486 := by decide +kernel
theorem C'_3486 : C' 3486 :=
  ⟨c3486_sqf, c3486_range, c3486_ell, leafNSq_of_sq c3486_nsq, leafHAr_of_sq c3486_har,
   c3486_r, c3486_e', c3486_f1, leafS2_of_sq c3486_s2, leafS3_of_sq c3486_s3,
   c3486_iso, leafR8_of_sq c3486_nof2 c3486_nof3 c3486_nof4z⟩
theorem not_tile'_3486 (D : CongruentDissection 3486) : False :=
  not_tile_of_conditions' 3486 C'_3486 D

private theorem c3487_sqf   : LeafSqf 3487   := by decide +kernel
private theorem c3487_range : LeafRange 3487  := by decide +kernel
private theorem c3487_ell   : LeafEll 3487    := by decide +kernel
private theorem c3487_nsq   : NSqChkSq 3487   := by decide +kernel
private theorem c3487_har   : HArithChkSq 3487 := by decide +kernel
private theorem c3487_r     : LeafR 3487      := by decide +kernel
private theorem c3487_e'    : LeafE' 3487     := by decide +kernel
private theorem c3487_f1    : LeafF1 3487     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3487_s2    : S2ChkSq 3487    := by decide +kernel
private theorem c3487_s3    : S3ChkSq 3487    := by decide +kernel
private theorem c3487_iso   : LeafIso 3487    := by decide +kernel
private theorem c3487_nof2  : NoF2ChkSq 3487  := by decide +kernel
private theorem c3487_nof3  : NoF3ChkSq 3487  := by decide +kernel
private theorem c3487_nof4z : NoF4zChkSq 3487 := by decide +kernel
theorem C'_3487 : C' 3487 :=
  ⟨c3487_sqf, c3487_range, c3487_ell, leafNSq_of_sq c3487_nsq, leafHAr_of_sq c3487_har,
   c3487_r, c3487_e', c3487_f1, leafS2_of_sq c3487_s2, leafS3_of_sq c3487_s3,
   c3487_iso, leafR8_of_sq c3487_nof2 c3487_nof3 c3487_nof4z⟩
theorem not_tile'_3487 (D : CongruentDissection 3487) : False :=
  not_tile_of_conditions' 3487 C'_3487 D

end Erdos634.Draft.AllN2

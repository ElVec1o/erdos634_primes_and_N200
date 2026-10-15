/- AllN2Check88: N = 2463, 2467, 2469, 2470, 2471
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2463_sqf   : LeafSqf 2463   := by decide +kernel
private theorem c2463_range : LeafRange 2463  := by decide +kernel
private theorem c2463_ell   : LeafEll 2463    := by decide +kernel
private theorem c2463_nsq   : NSqChkSq 2463   := by decide +kernel
private theorem c2463_har   : HArithChkSq 2463 := by decide +kernel
private theorem c2463_r     : LeafR 2463      := by decide +kernel
private theorem c2463_e'    : LeafE' 2463     := by decide +kernel
private theorem c2463_f1    : LeafF1 2463     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2463_s2    : S2ChkSq 2463    := by decide +kernel
private theorem c2463_s3    : S3ChkSq 2463    := by decide +kernel
private theorem c2463_iso   : LeafIso 2463    := by decide +kernel
private theorem c2463_nof2  : NoF2ChkSq 2463  := by decide +kernel
private theorem c2463_nof3  : NoF3ChkSq 2463  := by decide +kernel
private theorem c2463_nof4z : NoF4zChkSq 2463 := by decide +kernel
theorem C'_2463 : C' 2463 :=
  ⟨c2463_sqf, c2463_range, c2463_ell, leafNSq_of_sq c2463_nsq, leafHAr_of_sq c2463_har,
   c2463_r, c2463_e', c2463_f1, leafS2_of_sq c2463_s2, leafS3_of_sq c2463_s3,
   c2463_iso, leafR8_of_sq c2463_nof2 c2463_nof3 c2463_nof4z⟩
theorem not_tile'_2463 (D : CongruentDissection 2463) : False :=
  not_tile_of_conditions' 2463 C'_2463 D

private theorem c2467_sqf   : LeafSqf 2467   := by decide +kernel
private theorem c2467_range : LeafRange 2467  := by decide +kernel
private theorem c2467_ell   : LeafEll 2467    := by decide +kernel
private theorem c2467_nsq   : NSqChkSq 2467   := by decide +kernel
private theorem c2467_har   : HArithChkSq 2467 := by decide +kernel
private theorem c2467_r     : LeafR 2467      := by decide +kernel
private theorem c2467_e'    : LeafE' 2467     := by decide +kernel
private theorem c2467_f1    : LeafF1 2467     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2467_s2    : S2ChkSq 2467    := by decide +kernel
private theorem c2467_s3    : S3ChkSq 2467    := by decide +kernel
private theorem c2467_iso   : LeafIso 2467    := by decide +kernel
private theorem c2467_nof2  : NoF2ChkSq 2467  := by decide +kernel
private theorem c2467_nof3  : NoF3ChkSq 2467  := by decide +kernel
private theorem c2467_nof4z : NoF4zChkSq 2467 := by decide +kernel
theorem C'_2467 : C' 2467 :=
  ⟨c2467_sqf, c2467_range, c2467_ell, leafNSq_of_sq c2467_nsq, leafHAr_of_sq c2467_har,
   c2467_r, c2467_e', c2467_f1, leafS2_of_sq c2467_s2, leafS3_of_sq c2467_s3,
   c2467_iso, leafR8_of_sq c2467_nof2 c2467_nof3 c2467_nof4z⟩
theorem not_tile'_2467 (D : CongruentDissection 2467) : False :=
  not_tile_of_conditions' 2467 C'_2467 D

private theorem c2469_sqf   : LeafSqf 2469   := by decide +kernel
private theorem c2469_range : LeafRange 2469  := by decide +kernel
private theorem c2469_ell   : LeafEll 2469    := by decide +kernel
private theorem c2469_nsq   : NSqChkSq 2469   := by decide +kernel
private theorem c2469_har   : HArithChkSq 2469 := by decide +kernel
private theorem c2469_r     : LeafR 2469      := by decide +kernel
private theorem c2469_e'    : LeafE' 2469     := by decide +kernel
private theorem c2469_f1    : LeafF1 2469     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2469_s2    : S2ChkSq 2469    := by decide +kernel
private theorem c2469_s3    : S3ChkSq 2469    := by decide +kernel
private theorem c2469_iso   : LeafIso 2469    := by decide +kernel
private theorem c2469_nof2  : NoF2ChkSq 2469  := by decide +kernel
private theorem c2469_nof3  : NoF3ChkSq 2469  := by decide +kernel
private theorem c2469_nof4z : NoF4zChkSq 2469 := by decide +kernel
theorem C'_2469 : C' 2469 :=
  ⟨c2469_sqf, c2469_range, c2469_ell, leafNSq_of_sq c2469_nsq, leafHAr_of_sq c2469_har,
   c2469_r, c2469_e', c2469_f1, leafS2_of_sq c2469_s2, leafS3_of_sq c2469_s3,
   c2469_iso, leafR8_of_sq c2469_nof2 c2469_nof3 c2469_nof4z⟩
theorem not_tile'_2469 (D : CongruentDissection 2469) : False :=
  not_tile_of_conditions' 2469 C'_2469 D

private theorem c2470_sqf   : LeafSqf 2470   := by decide +kernel
private theorem c2470_range : LeafRange 2470  := by decide +kernel
private theorem c2470_ell   : LeafEll 2470    := by decide +kernel
private theorem c2470_nsq   : NSqChkSq 2470   := by decide +kernel
private theorem c2470_har   : HArithChkSq 2470 := by decide +kernel
private theorem c2470_r     : LeafR 2470      := by decide +kernel
private theorem c2470_e'    : LeafE' 2470     := by decide +kernel
private theorem c2470_f1    : LeafF1 2470     := Or.inl (by decide)
private theorem c2470_s2    : S2ChkSq 2470    := by decide +kernel
private theorem c2470_s3    : S3ChkSq 2470    := by decide +kernel
private theorem c2470_iso   : LeafIso 2470    := by decide +kernel
private theorem c2470_nof2  : NoF2ChkSq 2470  := by decide +kernel
private theorem c2470_nof3  : NoF3ChkSq 2470  := by decide +kernel
private theorem c2470_nof4z : NoF4zChkSq 2470 := by decide +kernel
theorem C'_2470 : C' 2470 :=
  ⟨c2470_sqf, c2470_range, c2470_ell, leafNSq_of_sq c2470_nsq, leafHAr_of_sq c2470_har,
   c2470_r, c2470_e', c2470_f1, leafS2_of_sq c2470_s2, leafS3_of_sq c2470_s3,
   c2470_iso, leafR8_of_sq c2470_nof2 c2470_nof3 c2470_nof4z⟩
theorem not_tile'_2470 (D : CongruentDissection 2470) : False :=
  not_tile_of_conditions' 2470 C'_2470 D

private theorem c2471_sqf   : LeafSqf 2471   := by decide +kernel
private theorem c2471_range : LeafRange 2471  := by decide +kernel
private theorem c2471_ell   : LeafEll 2471    := by decide +kernel
private theorem c2471_nsq   : NSqChkSq 2471   := by decide +kernel
private theorem c2471_har   : HArithChkSq 2471 := by decide +kernel
private theorem c2471_r     : LeafR 2471      := by decide +kernel
private theorem c2471_e'    : LeafE' 2471     := by decide +kernel
private theorem c2471_f1    : LeafF1 2471     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2471_s2    : S2ChkSq 2471    := by decide +kernel
private theorem c2471_s3    : S3ChkSq 2471    := by decide +kernel
private theorem c2471_iso   : LeafIso 2471    := by decide +kernel
private theorem c2471_nof2  : NoF2ChkSq 2471  := by decide +kernel
private theorem c2471_nof3  : NoF3ChkSq 2471  := by decide +kernel
private theorem c2471_nof4z : NoF4zChkSq 2471 := by decide +kernel
theorem C'_2471 : C' 2471 :=
  ⟨c2471_sqf, c2471_range, c2471_ell, leafNSq_of_sq c2471_nsq, leafHAr_of_sq c2471_har,
   c2471_r, c2471_e', c2471_f1, leafS2_of_sq c2471_s2, leafS3_of_sq c2471_s3,
   c2471_iso, leafR8_of_sq c2471_nof2 c2471_nof3 c2471_nof4z⟩
theorem not_tile'_2471 (D : CongruentDissection 2471) : False :=
  not_tile_of_conditions' 2471 C'_2471 D

end Erdos634.Draft.AllN2

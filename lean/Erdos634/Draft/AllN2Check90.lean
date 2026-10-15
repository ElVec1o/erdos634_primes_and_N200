/- AllN2Check90: N = 2487, 2489, 2490, 2491, 2494
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2487_sqf   : LeafSqf 2487   := by decide +kernel
private theorem c2487_range : LeafRange 2487  := by decide +kernel
private theorem c2487_ell   : LeafEll 2487    := by decide +kernel
private theorem c2487_nsq   : NSqChkSq 2487   := by decide +kernel
private theorem c2487_har   : HArithChkSq 2487 := by decide +kernel
private theorem c2487_r     : LeafR 2487      := by decide +kernel
private theorem c2487_e'    : LeafE' 2487     := by decide +kernel
private theorem c2487_f1    : LeafF1 2487     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2487_s2    : S2ChkSq 2487    := by decide +kernel
private theorem c2487_s3    : S3ChkSq 2487    := by decide +kernel
private theorem c2487_iso   : LeafIso 2487    := by decide +kernel
private theorem c2487_nof2  : NoF2ChkSq 2487  := by decide +kernel
private theorem c2487_nof3  : NoF3ChkSq 2487  := by decide +kernel
private theorem c2487_nof4z : NoF4zChkSq 2487 := by decide +kernel
theorem C'_2487 : C' 2487 :=
  ⟨c2487_sqf, c2487_range, c2487_ell, leafNSq_of_sq c2487_nsq, leafHAr_of_sq c2487_har,
   c2487_r, c2487_e', c2487_f1, leafS2_of_sq c2487_s2, leafS3_of_sq c2487_s3,
   c2487_iso, leafR8_of_sq c2487_nof2 c2487_nof3 c2487_nof4z⟩
theorem not_tile'_2487 (D : CongruentDissection 2487) : False :=
  not_tile_of_conditions' 2487 C'_2487 D

private theorem c2489_sqf   : LeafSqf 2489   := by decide +kernel
private theorem c2489_range : LeafRange 2489  := by decide +kernel
private theorem c2489_ell   : LeafEll 2489    := by decide +kernel
private theorem c2489_nsq   : NSqChkSq 2489   := by decide +kernel
private theorem c2489_har   : HArithChkSq 2489 := by decide +kernel
private theorem c2489_r     : LeafR 2489      := by decide +kernel
private theorem c2489_e'    : LeafE' 2489     := by decide +kernel
private theorem c2489_f1    : LeafF1 2489     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2489_s2    : S2ChkSq 2489    := by decide +kernel
private theorem c2489_s3    : S3ChkSq 2489    := by decide +kernel
private theorem c2489_iso   : LeafIso 2489    := by decide +kernel
private theorem c2489_nof2  : NoF2ChkSq 2489  := by decide +kernel
private theorem c2489_nof3  : NoF3ChkSq 2489  := by decide +kernel
private theorem c2489_nof4z : NoF4zChkSq 2489 := by decide +kernel
theorem C'_2489 : C' 2489 :=
  ⟨c2489_sqf, c2489_range, c2489_ell, leafNSq_of_sq c2489_nsq, leafHAr_of_sq c2489_har,
   c2489_r, c2489_e', c2489_f1, leafS2_of_sq c2489_s2, leafS3_of_sq c2489_s3,
   c2489_iso, leafR8_of_sq c2489_nof2 c2489_nof3 c2489_nof4z⟩
theorem not_tile'_2489 (D : CongruentDissection 2489) : False :=
  not_tile_of_conditions' 2489 C'_2489 D

private theorem c2490_sqf   : LeafSqf 2490   := by decide +kernel
private theorem c2490_range : LeafRange 2490  := by decide +kernel
private theorem c2490_ell   : LeafEll 2490    := by decide +kernel
private theorem c2490_nsq   : NSqChkSq 2490   := by decide +kernel
private theorem c2490_har   : HArithChkSq 2490 := by decide +kernel
private theorem c2490_r     : LeafR 2490      := by decide +kernel
private theorem c2490_e'    : LeafE' 2490     := by decide +kernel
private theorem c2490_f1    : LeafF1 2490     := Or.inl (by decide)
private theorem c2490_s2    : S2ChkSq 2490    := by decide +kernel
private theorem c2490_s3    : S3ChkSq 2490    := by decide +kernel
private theorem c2490_iso   : LeafIso 2490    := by decide +kernel
private theorem c2490_nof2  : NoF2ChkSq 2490  := by decide +kernel
private theorem c2490_nof3  : NoF3ChkSq 2490  := by decide +kernel
private theorem c2490_nof4z : NoF4zChkSq 2490 := by decide +kernel
theorem C'_2490 : C' 2490 :=
  ⟨c2490_sqf, c2490_range, c2490_ell, leafNSq_of_sq c2490_nsq, leafHAr_of_sq c2490_har,
   c2490_r, c2490_e', c2490_f1, leafS2_of_sq c2490_s2, leafS3_of_sq c2490_s3,
   c2490_iso, leafR8_of_sq c2490_nof2 c2490_nof3 c2490_nof4z⟩
theorem not_tile'_2490 (D : CongruentDissection 2490) : False :=
  not_tile_of_conditions' 2490 C'_2490 D

private theorem c2491_sqf   : LeafSqf 2491   := by decide +kernel
private theorem c2491_range : LeafRange 2491  := by decide +kernel
private theorem c2491_ell   : LeafEll 2491    := by decide +kernel
private theorem c2491_nsq   : NSqChkSq 2491   := by decide +kernel
private theorem c2491_har   : HArithChkSq 2491 := by decide +kernel
private theorem c2491_r     : LeafR 2491      := by decide +kernel
private theorem c2491_e'    : LeafE' 2491     := by decide +kernel
private theorem c2491_f1    : LeafF1 2491     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2491_s2    : S2ChkSq 2491    := by decide +kernel
private theorem c2491_s3    : S3ChkSq 2491    := by decide +kernel
private theorem c2491_iso   : LeafIso 2491    := by decide +kernel
private theorem c2491_nof2  : NoF2ChkSq 2491  := by decide +kernel
private theorem c2491_nof3  : NoF3ChkSq 2491  := by decide +kernel
private theorem c2491_nof4z : NoF4zChkSq 2491 := by decide +kernel
theorem C'_2491 : C' 2491 :=
  ⟨c2491_sqf, c2491_range, c2491_ell, leafNSq_of_sq c2491_nsq, leafHAr_of_sq c2491_har,
   c2491_r, c2491_e', c2491_f1, leafS2_of_sq c2491_s2, leafS3_of_sq c2491_s3,
   c2491_iso, leafR8_of_sq c2491_nof2 c2491_nof3 c2491_nof4z⟩
theorem not_tile'_2491 (D : CongruentDissection 2491) : False :=
  not_tile_of_conditions' 2491 C'_2491 D

private theorem c2494_sqf   : LeafSqf 2494   := by decide +kernel
private theorem c2494_range : LeafRange 2494  := by decide +kernel
private theorem c2494_ell   : LeafEll 2494    := by decide +kernel
private theorem c2494_nsq   : NSqChkSq 2494   := by decide +kernel
private theorem c2494_har   : HArithChkSq 2494 := by decide +kernel
private theorem c2494_r     : LeafR 2494      := by decide +kernel
private theorem c2494_e'    : LeafE' 2494     := by decide +kernel
private theorem c2494_f1    : LeafF1 2494     := Or.inl (by decide)
private theorem c2494_s2    : S2ChkSq 2494    := by decide +kernel
private theorem c2494_s3    : S3ChkSq 2494    := by decide +kernel
private theorem c2494_iso   : LeafIso 2494    := by decide +kernel
private theorem c2494_nof2  : NoF2ChkSq 2494  := by decide +kernel
private theorem c2494_nof3  : NoF3ChkSq 2494  := by decide +kernel
private theorem c2494_nof4z : NoF4zChkSq 2494 := by decide +kernel
theorem C'_2494 : C' 2494 :=
  ⟨c2494_sqf, c2494_range, c2494_ell, leafNSq_of_sq c2494_nsq, leafHAr_of_sq c2494_har,
   c2494_r, c2494_e', c2494_f1, leafS2_of_sq c2494_s2, leafS3_of_sq c2494_s3,
   c2494_iso, leafR8_of_sq c2494_nof2 c2494_nof3 c2494_nof4z⟩
theorem not_tile'_2494 (D : CongruentDissection 2494) : False :=
  not_tile_of_conditions' 2494 C'_2494 D

end Erdos634.Draft.AllN2

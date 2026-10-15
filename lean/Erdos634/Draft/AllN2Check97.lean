/- AllN2Check97: N = 2571, 2573, 2577, 2579, 2582
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2571_sqf   : LeafSqf 2571   := by decide +kernel
private theorem c2571_range : LeafRange 2571  := by decide +kernel
private theorem c2571_ell   : LeafEll 2571    := by decide +kernel
private theorem c2571_nsq   : NSqChkSq 2571   := by decide +kernel
private theorem c2571_har   : HArithChkSq 2571 := by decide +kernel
private theorem c2571_r     : LeafR 2571      := by decide +kernel
private theorem c2571_e'    : LeafE' 2571     := by decide +kernel
private theorem c2571_f1    : LeafF1 2571     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2571_s2    : S2ChkSq 2571    := by decide +kernel
private theorem c2571_s3    : S3ChkSq 2571    := by decide +kernel
private theorem c2571_iso   : LeafIso 2571    := by decide +kernel
private theorem c2571_nof2  : NoF2ChkSq 2571  := by decide +kernel
private theorem c2571_nof3  : NoF3ChkSq 2571  := by decide +kernel
private theorem c2571_nof4z : NoF4zChkSq 2571 := by decide +kernel
theorem C'_2571 : C' 2571 :=
  ⟨c2571_sqf, c2571_range, c2571_ell, leafNSq_of_sq c2571_nsq, leafHAr_of_sq c2571_har,
   c2571_r, c2571_e', c2571_f1, leafS2_of_sq c2571_s2, leafS3_of_sq c2571_s3,
   c2571_iso, leafR8_of_sq c2571_nof2 c2571_nof3 c2571_nof4z⟩
theorem not_tile'_2571 (D : CongruentDissection 2571) : False :=
  not_tile_of_conditions' 2571 C'_2571 D

private theorem c2573_sqf   : LeafSqf 2573   := by decide +kernel
private theorem c2573_range : LeafRange 2573  := by decide +kernel
private theorem c2573_ell   : LeafEll 2573    := by decide +kernel
private theorem c2573_nsq   : NSqChkSq 2573   := by decide +kernel
private theorem c2573_har   : HArithChkSq 2573 := by decide +kernel
private theorem c2573_r     : LeafR 2573      := by decide +kernel
private theorem c2573_e'    : LeafE' 2573     := by decide +kernel
private theorem c2573_f1    : LeafF1 2573     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2573_s2    : S2ChkSq 2573    := by decide +kernel
private theorem c2573_s3    : S3ChkSq 2573    := by decide +kernel
private theorem c2573_iso   : LeafIso 2573    := by decide +kernel
private theorem c2573_nof2  : NoF2ChkSq 2573  := by decide +kernel
private theorem c2573_nof3  : NoF3ChkSq 2573  := by decide +kernel
private theorem c2573_nof4z : NoF4zChkSq 2573 := by decide +kernel
theorem C'_2573 : C' 2573 :=
  ⟨c2573_sqf, c2573_range, c2573_ell, leafNSq_of_sq c2573_nsq, leafHAr_of_sq c2573_har,
   c2573_r, c2573_e', c2573_f1, leafS2_of_sq c2573_s2, leafS3_of_sq c2573_s3,
   c2573_iso, leafR8_of_sq c2573_nof2 c2573_nof3 c2573_nof4z⟩
theorem not_tile'_2573 (D : CongruentDissection 2573) : False :=
  not_tile_of_conditions' 2573 C'_2573 D

private theorem c2577_sqf   : LeafSqf 2577   := by decide +kernel
private theorem c2577_range : LeafRange 2577  := by decide +kernel
private theorem c2577_ell   : LeafEll 2577    := by decide +kernel
private theorem c2577_nsq   : NSqChkSq 2577   := by decide +kernel
private theorem c2577_har   : HArithChkSq 2577 := by decide +kernel
private theorem c2577_r     : LeafR 2577      := by decide +kernel
private theorem c2577_e'    : LeafE' 2577     := by decide +kernel
private theorem c2577_f1    : LeafF1 2577     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2577_s2    : S2ChkSq 2577    := by decide +kernel
private theorem c2577_s3    : S3ChkSq 2577    := by decide +kernel
private theorem c2577_iso   : LeafIso 2577    := by decide +kernel
private theorem c2577_nof2  : NoF2ChkSq 2577  := by decide +kernel
private theorem c2577_nof3  : NoF3ChkSq 2577  := by decide +kernel
private theorem c2577_nof4z : NoF4zChkSq 2577 := by decide +kernel
theorem C'_2577 : C' 2577 :=
  ⟨c2577_sqf, c2577_range, c2577_ell, leafNSq_of_sq c2577_nsq, leafHAr_of_sq c2577_har,
   c2577_r, c2577_e', c2577_f1, leafS2_of_sq c2577_s2, leafS3_of_sq c2577_s3,
   c2577_iso, leafR8_of_sq c2577_nof2 c2577_nof3 c2577_nof4z⟩
theorem not_tile'_2577 (D : CongruentDissection 2577) : False :=
  not_tile_of_conditions' 2577 C'_2577 D

private theorem c2579_sqf   : LeafSqf 2579   := by decide +kernel
private theorem c2579_range : LeafRange 2579  := by decide +kernel
private theorem c2579_ell   : LeafEll 2579    := by decide +kernel
private theorem c2579_nsq   : NSqChkSq 2579   := by decide +kernel
private theorem c2579_har   : HArithChkSq 2579 := by decide +kernel
private theorem c2579_r     : LeafR 2579      := by decide +kernel
private theorem c2579_e'    : LeafE' 2579     := by decide +kernel
private theorem c2579_f1    : LeafF1 2579     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2579_s2    : S2ChkSq 2579    := by decide +kernel
private theorem c2579_s3    : S3ChkSq 2579    := by decide +kernel
private theorem c2579_iso   : LeafIso 2579    := by decide +kernel
private theorem c2579_nof2  : NoF2ChkSq 2579  := by decide +kernel
private theorem c2579_nof3  : NoF3ChkSq 2579  := by decide +kernel
private theorem c2579_nof4z : NoF4zChkSq 2579 := by decide +kernel
theorem C'_2579 : C' 2579 :=
  ⟨c2579_sqf, c2579_range, c2579_ell, leafNSq_of_sq c2579_nsq, leafHAr_of_sq c2579_har,
   c2579_r, c2579_e', c2579_f1, leafS2_of_sq c2579_s2, leafS3_of_sq c2579_s3,
   c2579_iso, leafR8_of_sq c2579_nof2 c2579_nof3 c2579_nof4z⟩
theorem not_tile'_2579 (D : CongruentDissection 2579) : False :=
  not_tile_of_conditions' 2579 C'_2579 D

private theorem c2582_sqf   : LeafSqf 2582   := by decide +kernel
private theorem c2582_range : LeafRange 2582  := by decide +kernel
private theorem c2582_ell   : LeafEll 2582    := by decide +kernel
private theorem c2582_nsq   : NSqChkSq 2582   := by decide +kernel
private theorem c2582_har   : HArithChkSq 2582 := by decide +kernel
private theorem c2582_r     : LeafR 2582      := by decide +kernel
private theorem c2582_e'    : LeafE' 2582     := by decide +kernel
private theorem c2582_f1    : LeafF1 2582     := Or.inl (by decide)
private theorem c2582_s2    : S2ChkSq 2582    := by decide +kernel
private theorem c2582_s3    : S3ChkSq 2582    := by decide +kernel
private theorem c2582_iso   : LeafIso 2582    := by decide +kernel
private theorem c2582_nof2  : NoF2ChkSq 2582  := by decide +kernel
private theorem c2582_nof3  : NoF3ChkSq 2582  := by decide +kernel
private theorem c2582_nof4z : NoF4zChkSq 2582 := by decide +kernel
theorem C'_2582 : C' 2582 :=
  ⟨c2582_sqf, c2582_range, c2582_ell, leafNSq_of_sq c2582_nsq, leafHAr_of_sq c2582_har,
   c2582_r, c2582_e', c2582_f1, leafS2_of_sq c2582_s2, leafS3_of_sq c2582_s3,
   c2582_iso, leafR8_of_sq c2582_nof2 c2582_nof3 c2582_nof4z⟩
theorem not_tile'_2582 (D : CongruentDissection 2582) : False :=
  not_tile_of_conditions' 2582 C'_2582 D

end Erdos634.Draft.AllN2

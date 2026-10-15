/- AllN2Check91: N = 2495, 2497, 2503, 2506, 2507
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2495_sqf   : LeafSqf 2495   := by decide +kernel
private theorem c2495_range : LeafRange 2495  := by decide +kernel
private theorem c2495_ell   : LeafEll 2495    := by decide +kernel
private theorem c2495_nsq   : NSqChkSq 2495   := by decide +kernel
private theorem c2495_har   : HArithChkSq 2495 := by decide +kernel
private theorem c2495_r     : LeafR 2495      := by decide +kernel
private theorem c2495_e'    : LeafE' 2495     := by decide +kernel
private theorem c2495_f1    : LeafF1 2495     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2495_s2    : S2ChkSq 2495    := by decide +kernel
private theorem c2495_s3    : S3ChkSq 2495    := by decide +kernel
private theorem c2495_iso   : LeafIso 2495    := by decide +kernel
private theorem c2495_nof2  : NoF2ChkSq 2495  := by decide +kernel
private theorem c2495_nof3  : NoF3ChkSq 2495  := by decide +kernel
private theorem c2495_nof4z : NoF4zChkSq 2495 := by decide +kernel
theorem C'_2495 : C' 2495 :=
  ⟨c2495_sqf, c2495_range, c2495_ell, leafNSq_of_sq c2495_nsq, leafHAr_of_sq c2495_har,
   c2495_r, c2495_e', c2495_f1, leafS2_of_sq c2495_s2, leafS3_of_sq c2495_s3,
   c2495_iso, leafR8_of_sq c2495_nof2 c2495_nof3 c2495_nof4z⟩
theorem not_tile'_2495 (D : CongruentDissection 2495) : False :=
  not_tile_of_conditions' 2495 C'_2495 D

private theorem c2497_sqf   : LeafSqf 2497   := by decide +kernel
private theorem c2497_range : LeafRange 2497  := by decide +kernel
private theorem c2497_ell   : LeafEll 2497    := by decide +kernel
private theorem c2497_nsq   : NSqChkSq 2497   := by decide +kernel
private theorem c2497_har   : HArithChkSq 2497 := by decide +kernel
private theorem c2497_r     : LeafR 2497      := by decide +kernel
private theorem c2497_e'    : LeafE' 2497     := by decide +kernel
private theorem c2497_f1    : LeafF1 2497     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2497_s2    : S2ChkSq 2497    := by decide +kernel
private theorem c2497_s3    : S3ChkSq 2497    := by decide +kernel
private theorem c2497_iso   : LeafIso 2497    := by decide +kernel
private theorem c2497_nof2  : NoF2ChkSq 2497  := by decide +kernel
private theorem c2497_nof3  : NoF3ChkSq 2497  := by decide +kernel
private theorem c2497_nof4z : NoF4zChkSq 2497 := by decide +kernel
theorem C'_2497 : C' 2497 :=
  ⟨c2497_sqf, c2497_range, c2497_ell, leafNSq_of_sq c2497_nsq, leafHAr_of_sq c2497_har,
   c2497_r, c2497_e', c2497_f1, leafS2_of_sq c2497_s2, leafS3_of_sq c2497_s3,
   c2497_iso, leafR8_of_sq c2497_nof2 c2497_nof3 c2497_nof4z⟩
theorem not_tile'_2497 (D : CongruentDissection 2497) : False :=
  not_tile_of_conditions' 2497 C'_2497 D

private theorem c2503_sqf   : LeafSqf 2503   := by decide +kernel
private theorem c2503_range : LeafRange 2503  := by decide +kernel
private theorem c2503_ell   : LeafEll 2503    := by decide +kernel
private theorem c2503_nsq   : NSqChkSq 2503   := by decide +kernel
private theorem c2503_har   : HArithChkSq 2503 := by decide +kernel
private theorem c2503_r     : LeafR 2503      := by decide +kernel
private theorem c2503_e'    : LeafE' 2503     := by decide +kernel
private theorem c2503_f1    : LeafF1 2503     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2503_s2    : S2ChkSq 2503    := by decide +kernel
private theorem c2503_s3    : S3ChkSq 2503    := by decide +kernel
private theorem c2503_iso   : LeafIso 2503    := by decide +kernel
private theorem c2503_nof2  : NoF2ChkSq 2503  := by decide +kernel
private theorem c2503_nof3  : NoF3ChkSq 2503  := by decide +kernel
private theorem c2503_nof4z : NoF4zChkSq 2503 := by decide +kernel
theorem C'_2503 : C' 2503 :=
  ⟨c2503_sqf, c2503_range, c2503_ell, leafNSq_of_sq c2503_nsq, leafHAr_of_sq c2503_har,
   c2503_r, c2503_e', c2503_f1, leafS2_of_sq c2503_s2, leafS3_of_sq c2503_s3,
   c2503_iso, leafR8_of_sq c2503_nof2 c2503_nof3 c2503_nof4z⟩
theorem not_tile'_2503 (D : CongruentDissection 2503) : False :=
  not_tile_of_conditions' 2503 C'_2503 D

private theorem c2506_sqf   : LeafSqf 2506   := by decide +kernel
private theorem c2506_range : LeafRange 2506  := by decide +kernel
private theorem c2506_ell   : LeafEll 2506    := by decide +kernel
private theorem c2506_nsq   : NSqChkSq 2506   := by decide +kernel
private theorem c2506_har   : HArithChkSq 2506 := by decide +kernel
private theorem c2506_r     : LeafR 2506      := by decide +kernel
private theorem c2506_e'    : LeafE' 2506     := by decide +kernel
private theorem c2506_f1    : LeafF1 2506     := Or.inl (by decide)
private theorem c2506_s2    : S2ChkSq 2506    := by decide +kernel
private theorem c2506_s3    : S3ChkSq 2506    := by decide +kernel
private theorem c2506_iso   : LeafIso 2506    := by decide +kernel
private theorem c2506_nof2  : NoF2ChkSq 2506  := by decide +kernel
private theorem c2506_nof3  : NoF3ChkSq 2506  := by decide +kernel
private theorem c2506_nof4z : NoF4zChkSq 2506 := by decide +kernel
theorem C'_2506 : C' 2506 :=
  ⟨c2506_sqf, c2506_range, c2506_ell, leafNSq_of_sq c2506_nsq, leafHAr_of_sq c2506_har,
   c2506_r, c2506_e', c2506_f1, leafS2_of_sq c2506_s2, leafS3_of_sq c2506_s3,
   c2506_iso, leafR8_of_sq c2506_nof2 c2506_nof3 c2506_nof4z⟩
theorem not_tile'_2506 (D : CongruentDissection 2506) : False :=
  not_tile_of_conditions' 2506 C'_2506 D

private theorem c2507_sqf   : LeafSqf 2507   := by decide +kernel
private theorem c2507_range : LeafRange 2507  := by decide +kernel
private theorem c2507_ell   : LeafEll 2507    := by decide +kernel
private theorem c2507_nsq   : NSqChkSq 2507   := by decide +kernel
private theorem c2507_har   : HArithChkSq 2507 := by decide +kernel
private theorem c2507_r     : LeafR 2507      := by decide +kernel
private theorem c2507_e'    : LeafE' 2507     := by decide +kernel
private theorem c2507_f1    : LeafF1 2507     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2507_s2    : S2ChkSq 2507    := by decide +kernel
private theorem c2507_s3    : S3ChkSq 2507    := by decide +kernel
private theorem c2507_iso   : LeafIso 2507    := by decide +kernel
private theorem c2507_nof2  : NoF2ChkSq 2507  := by decide +kernel
private theorem c2507_nof3  : NoF3ChkSq 2507  := by decide +kernel
private theorem c2507_nof4z : NoF4zChkSq 2507 := by decide +kernel
theorem C'_2507 : C' 2507 :=
  ⟨c2507_sqf, c2507_range, c2507_ell, leafNSq_of_sq c2507_nsq, leafHAr_of_sq c2507_har,
   c2507_r, c2507_e', c2507_f1, leafS2_of_sq c2507_s2, leafS3_of_sq c2507_s3,
   c2507_iso, leafR8_of_sq c2507_nof2 c2507_nof3 c2507_nof4z⟩
theorem not_tile'_2507 (D : CongruentDissection 2507) : False :=
  not_tile_of_conditions' 2507 C'_2507 D

end Erdos634.Draft.AllN2

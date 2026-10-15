/- AllN2Check94: N = 2534, 2537, 2539, 2542, 2543
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2534_sqf   : LeafSqf 2534   := by decide +kernel
private theorem c2534_range : LeafRange 2534  := by decide +kernel
private theorem c2534_ell   : LeafEll 2534    := by decide +kernel
private theorem c2534_nsq   : NSqChkSq 2534   := by decide +kernel
private theorem c2534_har   : HArithChkSq 2534 := by decide +kernel
private theorem c2534_r     : LeafR 2534      := by decide +kernel
private theorem c2534_e'    : LeafE' 2534     := by decide +kernel
private theorem c2534_f1    : LeafF1 2534     := Or.inl (by decide)
private theorem c2534_s2    : S2ChkSq 2534    := by decide +kernel
private theorem c2534_s3    : S3ChkSq 2534    := by decide +kernel
private theorem c2534_iso   : LeafIso 2534    := by decide +kernel
private theorem c2534_nof2  : NoF2ChkSq 2534  := by decide +kernel
private theorem c2534_nof3  : NoF3ChkSq 2534  := by decide +kernel
private theorem c2534_nof4z : NoF4zChkSq 2534 := by decide +kernel
theorem C'_2534 : C' 2534 :=
  ⟨c2534_sqf, c2534_range, c2534_ell, leafNSq_of_sq c2534_nsq, leafHAr_of_sq c2534_har,
   c2534_r, c2534_e', c2534_f1, leafS2_of_sq c2534_s2, leafS3_of_sq c2534_s3,
   c2534_iso, leafR8_of_sq c2534_nof2 c2534_nof3 c2534_nof4z⟩
theorem not_tile'_2534 (D : CongruentDissection 2534) : False :=
  not_tile_of_conditions' 2534 C'_2534 D

private theorem c2537_sqf   : LeafSqf 2537   := by decide +kernel
private theorem c2537_range : LeafRange 2537  := by decide +kernel
private theorem c2537_ell   : LeafEll 2537    := by decide +kernel
private theorem c2537_nsq   : NSqChkSq 2537   := by decide +kernel
private theorem c2537_har   : HArithChkSq 2537 := by decide +kernel
private theorem c2537_r     : LeafR 2537      := by decide +kernel
private theorem c2537_e'    : LeafE' 2537     := by decide +kernel
private theorem c2537_f1    : LeafF1 2537     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2537_s2    : S2ChkSq 2537    := by decide +kernel
private theorem c2537_s3    : S3ChkSq 2537    := by decide +kernel
private theorem c2537_iso   : LeafIso 2537    := by decide +kernel
private theorem c2537_nof2  : NoF2ChkSq 2537  := by decide +kernel
private theorem c2537_nof3  : NoF3ChkSq 2537  := by decide +kernel
private theorem c2537_nof4z : NoF4zChkSq 2537 := by decide +kernel
theorem C'_2537 : C' 2537 :=
  ⟨c2537_sqf, c2537_range, c2537_ell, leafNSq_of_sq c2537_nsq, leafHAr_of_sq c2537_har,
   c2537_r, c2537_e', c2537_f1, leafS2_of_sq c2537_s2, leafS3_of_sq c2537_s3,
   c2537_iso, leafR8_of_sq c2537_nof2 c2537_nof3 c2537_nof4z⟩
theorem not_tile'_2537 (D : CongruentDissection 2537) : False :=
  not_tile_of_conditions' 2537 C'_2537 D

private theorem c2539_sqf   : LeafSqf 2539   := by decide +kernel
private theorem c2539_range : LeafRange 2539  := by decide +kernel
private theorem c2539_ell   : LeafEll 2539    := by decide +kernel
private theorem c2539_nsq   : NSqChkSq 2539   := by decide +kernel
private theorem c2539_har   : HArithChkSq 2539 := by decide +kernel
private theorem c2539_r     : LeafR 2539      := by decide +kernel
private theorem c2539_e'    : LeafE' 2539     := by decide +kernel
private theorem c2539_f1    : LeafF1 2539     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2539_s2    : S2ChkSq 2539    := by decide +kernel
private theorem c2539_s3    : S3ChkSq 2539    := by decide +kernel
private theorem c2539_iso   : LeafIso 2539    := by decide +kernel
private theorem c2539_nof2  : NoF2ChkSq 2539  := by decide +kernel
private theorem c2539_nof3  : NoF3ChkSq 2539  := by decide +kernel
private theorem c2539_nof4z : NoF4zChkSq 2539 := by decide +kernel
theorem C'_2539 : C' 2539 :=
  ⟨c2539_sqf, c2539_range, c2539_ell, leafNSq_of_sq c2539_nsq, leafHAr_of_sq c2539_har,
   c2539_r, c2539_e', c2539_f1, leafS2_of_sq c2539_s2, leafS3_of_sq c2539_s3,
   c2539_iso, leafR8_of_sq c2539_nof2 c2539_nof3 c2539_nof4z⟩
theorem not_tile'_2539 (D : CongruentDissection 2539) : False :=
  not_tile_of_conditions' 2539 C'_2539 D

private theorem c2542_sqf   : LeafSqf 2542   := by decide +kernel
private theorem c2542_range : LeafRange 2542  := by decide +kernel
private theorem c2542_ell   : LeafEll 2542    := by decide +kernel
private theorem c2542_nsq   : NSqChkSq 2542   := by decide +kernel
private theorem c2542_har   : HArithChkSq 2542 := by decide +kernel
private theorem c2542_r     : LeafR 2542      := by decide +kernel
private theorem c2542_e'    : LeafE' 2542     := by decide +kernel
private theorem c2542_f1    : LeafF1 2542     := Or.inl (by decide)
private theorem c2542_s2    : S2ChkSq 2542    := by decide +kernel
private theorem c2542_s3    : S3ChkSq 2542    := by decide +kernel
private theorem c2542_iso   : LeafIso 2542    := by decide +kernel
private theorem c2542_nof2  : NoF2ChkSq 2542  := by decide +kernel
private theorem c2542_nof3  : NoF3ChkSq 2542  := by decide +kernel
private theorem c2542_nof4z : NoF4zChkSq 2542 := by decide +kernel
theorem C'_2542 : C' 2542 :=
  ⟨c2542_sqf, c2542_range, c2542_ell, leafNSq_of_sq c2542_nsq, leafHAr_of_sq c2542_har,
   c2542_r, c2542_e', c2542_f1, leafS2_of_sq c2542_s2, leafS3_of_sq c2542_s3,
   c2542_iso, leafR8_of_sq c2542_nof2 c2542_nof3 c2542_nof4z⟩
theorem not_tile'_2542 (D : CongruentDissection 2542) : False :=
  not_tile_of_conditions' 2542 C'_2542 D

private theorem c2543_sqf   : LeafSqf 2543   := by decide +kernel
private theorem c2543_range : LeafRange 2543  := by decide +kernel
private theorem c2543_ell   : LeafEll 2543    := by decide +kernel
private theorem c2543_nsq   : NSqChkSq 2543   := by decide +kernel
private theorem c2543_har   : HArithChkSq 2543 := by decide +kernel
private theorem c2543_r     : LeafR 2543      := by decide +kernel
private theorem c2543_e'    : LeafE' 2543     := by decide +kernel
private theorem c2543_f1    : LeafF1 2543     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2543_s2    : S2ChkSq 2543    := by decide +kernel
private theorem c2543_s3    : S3ChkSq 2543    := by decide +kernel
private theorem c2543_iso   : LeafIso 2543    := by decide +kernel
private theorem c2543_nof2  : NoF2ChkSq 2543  := by decide +kernel
private theorem c2543_nof3  : NoF3ChkSq 2543  := by decide +kernel
private theorem c2543_nof4z : NoF4zChkSq 2543 := by decide +kernel
theorem C'_2543 : C' 2543 :=
  ⟨c2543_sqf, c2543_range, c2543_ell, leafNSq_of_sq c2543_nsq, leafHAr_of_sq c2543_har,
   c2543_r, c2543_e', c2543_f1, leafS2_of_sq c2543_s2, leafS3_of_sq c2543_s3,
   c2543_iso, leafR8_of_sq c2543_nof2 c2543_nof3 c2543_nof4z⟩
theorem not_tile'_2543 (D : CongruentDissection 2543) : False :=
  not_tile_of_conditions' 2543 C'_2543 D

end Erdos634.Draft.AllN2

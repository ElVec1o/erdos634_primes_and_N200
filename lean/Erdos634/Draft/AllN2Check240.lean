/- AllN2Check240: N = 4422, 4423, 4427, 4429, 4430
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4422_sqf   : LeafSqf 4422   := by decide +kernel
private theorem c4422_range : LeafRange 4422  := by decide +kernel
private theorem c4422_ell   : LeafEll 4422    := by decide +kernel
private theorem c4422_nsq   : NSqChkSq 4422   := by decide +kernel
private theorem c4422_har   : HArithChkSq 4422 := by decide +kernel
private theorem c4422_r     : LeafR 4422      := by decide +kernel
private theorem c4422_e'    : LeafE' 4422     := by decide +kernel
private theorem c4422_f1    : LeafF1 4422     := Or.inl (by decide)
private theorem c4422_s2    : S2ChkSq 4422    := by decide +kernel
private theorem c4422_s3    : S3ChkSq 4422    := by decide +kernel
private theorem c4422_iso   : LeafIso 4422    := by decide +kernel
private theorem c4422_nof2  : NoF2ChkSq 4422  := by decide +kernel
private theorem c4422_nof3  : NoF3ChkSq 4422  := by decide +kernel
private theorem c4422_nof4z : NoF4zChkSq 4422 := by decide +kernel
theorem C'_4422 : C' 4422 :=
  ⟨c4422_sqf, c4422_range, c4422_ell, leafNSq_of_sq c4422_nsq, leafHAr_of_sq c4422_har,
   c4422_r, c4422_e', c4422_f1, leafS2_of_sq c4422_s2, leafS3_of_sq c4422_s3,
   c4422_iso, leafR8_of_sq c4422_nof2 c4422_nof3 c4422_nof4z⟩
theorem not_tile'_4422 (D : CongruentDissection 4422) : False :=
  not_tile_of_conditions' 4422 C'_4422 D

private theorem c4423_sqf   : LeafSqf 4423   := by decide +kernel
private theorem c4423_range : LeafRange 4423  := by decide +kernel
private theorem c4423_ell   : LeafEll 4423    := by decide +kernel
private theorem c4423_nsq   : NSqChkSq 4423   := by decide +kernel
private theorem c4423_har   : HArithChkSq 4423 := by decide +kernel
private theorem c4423_r     : LeafR 4423      := by decide +kernel
private theorem c4423_e'    : LeafE' 4423     := by decide +kernel
private theorem c4423_f1    : LeafF1 4423     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4423_s2    : S2ChkSq 4423    := by decide +kernel
private theorem c4423_s3    : S3ChkSq 4423    := by decide +kernel
private theorem c4423_iso   : LeafIso 4423    := by decide +kernel
private theorem c4423_nof2  : NoF2ChkSq 4423  := by decide +kernel
private theorem c4423_nof3  : NoF3ChkSq 4423  := by decide +kernel
private theorem c4423_nof4z : NoF4zChkSq 4423 := by decide +kernel
theorem C'_4423 : C' 4423 :=
  ⟨c4423_sqf, c4423_range, c4423_ell, leafNSq_of_sq c4423_nsq, leafHAr_of_sq c4423_har,
   c4423_r, c4423_e', c4423_f1, leafS2_of_sq c4423_s2, leafS3_of_sq c4423_s3,
   c4423_iso, leafR8_of_sq c4423_nof2 c4423_nof3 c4423_nof4z⟩
theorem not_tile'_4423 (D : CongruentDissection 4423) : False :=
  not_tile_of_conditions' 4423 C'_4423 D

private theorem c4427_sqf   : LeafSqf 4427   := by decide +kernel
private theorem c4427_range : LeafRange 4427  := by decide +kernel
private theorem c4427_ell   : LeafEll 4427    := by decide +kernel
private theorem c4427_nsq   : NSqChkSq 4427   := by decide +kernel
private theorem c4427_har   : HArithChkSq 4427 := by decide +kernel
private theorem c4427_r     : LeafR 4427      := by decide +kernel
private theorem c4427_e'    : LeafE' 4427     := by decide +kernel
private theorem c4427_f1    : LeafF1 4427     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4427_s2    : S2ChkSq 4427    := by decide +kernel
private theorem c4427_s3    : S3ChkSq 4427    := by decide +kernel
private theorem c4427_iso   : LeafIso 4427    := by decide +kernel
private theorem c4427_nof2  : NoF2ChkSq 4427  := by decide +kernel
private theorem c4427_nof3  : NoF3ChkSq 4427  := by decide +kernel
private theorem c4427_nof4z : NoF4zChkSq 4427 := by decide +kernel
theorem C'_4427 : C' 4427 :=
  ⟨c4427_sqf, c4427_range, c4427_ell, leafNSq_of_sq c4427_nsq, leafHAr_of_sq c4427_har,
   c4427_r, c4427_e', c4427_f1, leafS2_of_sq c4427_s2, leafS3_of_sq c4427_s3,
   c4427_iso, leafR8_of_sq c4427_nof2 c4427_nof3 c4427_nof4z⟩
theorem not_tile'_4427 (D : CongruentDissection 4427) : False :=
  not_tile_of_conditions' 4427 C'_4427 D

private theorem c4429_sqf   : LeafSqf 4429   := by decide +kernel
private theorem c4429_range : LeafRange 4429  := by decide +kernel
private theorem c4429_ell   : LeafEll 4429    := by decide +kernel
private theorem c4429_nsq   : NSqChkSq 4429   := by decide +kernel
private theorem c4429_har   : HArithChkSq 4429 := by decide +kernel
private theorem c4429_r     : LeafR 4429      := by decide +kernel
private theorem c4429_e'    : LeafE' 4429     := by decide +kernel
private theorem c4429_f1    : LeafF1 4429     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4429_s2    : S2ChkSq 4429    := by decide +kernel
private theorem c4429_s3    : S3ChkSq 4429    := by decide +kernel
private theorem c4429_iso   : LeafIso 4429    := by decide +kernel
private theorem c4429_nof2  : NoF2ChkSq 4429  := by decide +kernel
private theorem c4429_nof3  : NoF3ChkSq 4429  := by decide +kernel
private theorem c4429_nof4z : NoF4zChkSq 4429 := by decide +kernel
theorem C'_4429 : C' 4429 :=
  ⟨c4429_sqf, c4429_range, c4429_ell, leafNSq_of_sq c4429_nsq, leafHAr_of_sq c4429_har,
   c4429_r, c4429_e', c4429_f1, leafS2_of_sq c4429_s2, leafS3_of_sq c4429_s3,
   c4429_iso, leafR8_of_sq c4429_nof2 c4429_nof3 c4429_nof4z⟩
theorem not_tile'_4429 (D : CongruentDissection 4429) : False :=
  not_tile_of_conditions' 4429 C'_4429 D

private theorem c4430_sqf   : LeafSqf 4430   := by decide +kernel
private theorem c4430_range : LeafRange 4430  := by decide +kernel
private theorem c4430_ell   : LeafEll 4430    := by decide +kernel
private theorem c4430_nsq   : NSqChkSq 4430   := by decide +kernel
private theorem c4430_har   : HArithChkSq 4430 := by decide +kernel
private theorem c4430_r     : LeafR 4430      := by decide +kernel
private theorem c4430_e'    : LeafE' 4430     := by decide +kernel
private theorem c4430_f1    : LeafF1 4430     := Or.inl (by decide)
private theorem c4430_s2    : S2ChkSq 4430    := by decide +kernel
private theorem c4430_s3    : S3ChkSq 4430    := by decide +kernel
private theorem c4430_iso   : LeafIso 4430    := by decide +kernel
private theorem c4430_nof2  : NoF2ChkSq 4430  := by decide +kernel
private theorem c4430_nof3  : NoF3ChkSq 4430  := by decide +kernel
private theorem c4430_nof4z : NoF4zChkSq 4430 := by decide +kernel
theorem C'_4430 : C' 4430 :=
  ⟨c4430_sqf, c4430_range, c4430_ell, leafNSq_of_sq c4430_nsq, leafHAr_of_sq c4430_har,
   c4430_r, c4430_e', c4430_f1, leafS2_of_sq c4430_s2, leafS3_of_sq c4430_s3,
   c4430_iso, leafR8_of_sq c4430_nof2 c4430_nof3 c4430_nof4z⟩
theorem not_tile'_4430 (D : CongruentDissection 4430) : False :=
  not_tile_of_conditions' 4430 C'_4430 D

end Erdos634.Draft.AllN2

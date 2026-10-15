/- AllN2Check163: N = 3414, 3415, 3419, 3421, 3422
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3414_sqf   : LeafSqf 3414   := by decide +kernel
private theorem c3414_range : LeafRange 3414  := by decide +kernel
private theorem c3414_ell   : LeafEll 3414    := by decide +kernel
private theorem c3414_nsq   : NSqChkSq 3414   := by decide +kernel
private theorem c3414_har   : HArithChkSq 3414 := by decide +kernel
private theorem c3414_r     : LeafR 3414      := by decide +kernel
private theorem c3414_e'    : LeafE' 3414     := by decide +kernel
private theorem c3414_f1    : LeafF1 3414     := Or.inl (by decide)
private theorem c3414_s2    : S2ChkSq 3414    := by decide +kernel
private theorem c3414_s3    : S3ChkSq 3414    := by decide +kernel
private theorem c3414_iso   : LeafIso 3414    := by decide +kernel
private theorem c3414_nof2  : NoF2ChkSq 3414  := by decide +kernel
private theorem c3414_nof3  : NoF3ChkSq 3414  := by decide +kernel
private theorem c3414_nof4z : NoF4zChkSq 3414 := by decide +kernel
theorem C'_3414 : C' 3414 :=
  ⟨c3414_sqf, c3414_range, c3414_ell, leafNSq_of_sq c3414_nsq, leafHAr_of_sq c3414_har,
   c3414_r, c3414_e', c3414_f1, leafS2_of_sq c3414_s2, leafS3_of_sq c3414_s3,
   c3414_iso, leafR8_of_sq c3414_nof2 c3414_nof3 c3414_nof4z⟩
theorem not_tile'_3414 (D : CongruentDissection 3414) : False :=
  not_tile_of_conditions' 3414 C'_3414 D

private theorem c3415_sqf   : LeafSqf 3415   := by decide +kernel
private theorem c3415_range : LeafRange 3415  := by decide +kernel
private theorem c3415_ell   : LeafEll 3415    := by decide +kernel
private theorem c3415_nsq   : NSqChkSq 3415   := by decide +kernel
private theorem c3415_har   : HArithChkSq 3415 := by decide +kernel
private theorem c3415_r     : LeafR 3415      := by decide +kernel
private theorem c3415_e'    : LeafE' 3415     := by decide +kernel
private theorem c3415_f1    : LeafF1 3415     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3415_s2    : S2ChkSq 3415    := by decide +kernel
private theorem c3415_s3    : S3ChkSq 3415    := by decide +kernel
private theorem c3415_iso   : LeafIso 3415    := by decide +kernel
private theorem c3415_nof2  : NoF2ChkSq 3415  := by decide +kernel
private theorem c3415_nof3  : NoF3ChkSq 3415  := by decide +kernel
private theorem c3415_nof4z : NoF4zChkSq 3415 := by decide +kernel
theorem C'_3415 : C' 3415 :=
  ⟨c3415_sqf, c3415_range, c3415_ell, leafNSq_of_sq c3415_nsq, leafHAr_of_sq c3415_har,
   c3415_r, c3415_e', c3415_f1, leafS2_of_sq c3415_s2, leafS3_of_sq c3415_s3,
   c3415_iso, leafR8_of_sq c3415_nof2 c3415_nof3 c3415_nof4z⟩
theorem not_tile'_3415 (D : CongruentDissection 3415) : False :=
  not_tile_of_conditions' 3415 C'_3415 D

private theorem c3419_sqf   : LeafSqf 3419   := by decide +kernel
private theorem c3419_range : LeafRange 3419  := by decide +kernel
private theorem c3419_ell   : LeafEll 3419    := by decide +kernel
private theorem c3419_nsq   : NSqChkSq 3419   := by decide +kernel
private theorem c3419_har   : HArithChkSq 3419 := by decide +kernel
private theorem c3419_r     : LeafR 3419      := by decide +kernel
private theorem c3419_e'    : LeafE' 3419     := by decide +kernel
private theorem c3419_f1    : LeafF1 3419     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3419_s2    : S2ChkSq 3419    := by decide +kernel
private theorem c3419_s3    : S3ChkSq 3419    := by decide +kernel
private theorem c3419_iso   : LeafIso 3419    := by decide +kernel
private theorem c3419_nof2  : NoF2ChkSq 3419  := by decide +kernel
private theorem c3419_nof3  : NoF3ChkSq 3419  := by decide +kernel
private theorem c3419_nof4z : NoF4zChkSq 3419 := by decide +kernel
theorem C'_3419 : C' 3419 :=
  ⟨c3419_sqf, c3419_range, c3419_ell, leafNSq_of_sq c3419_nsq, leafHAr_of_sq c3419_har,
   c3419_r, c3419_e', c3419_f1, leafS2_of_sq c3419_s2, leafS3_of_sq c3419_s3,
   c3419_iso, leafR8_of_sq c3419_nof2 c3419_nof3 c3419_nof4z⟩
theorem not_tile'_3419 (D : CongruentDissection 3419) : False :=
  not_tile_of_conditions' 3419 C'_3419 D

private theorem c3421_sqf   : LeafSqf 3421   := by decide +kernel
private theorem c3421_range : LeafRange 3421  := by decide +kernel
private theorem c3421_ell   : LeafEll 3421    := by decide +kernel
private theorem c3421_nsq   : NSqChkSq 3421   := by decide +kernel
private theorem c3421_har   : HArithChkSq 3421 := by decide +kernel
private theorem c3421_r     : LeafR 3421      := by decide +kernel
private theorem c3421_e'    : LeafE' 3421     := by decide +kernel
private theorem c3421_f1    : LeafF1 3421     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3421_s2    : S2ChkSq 3421    := by decide +kernel
private theorem c3421_s3    : S3ChkSq 3421    := by decide +kernel
private theorem c3421_iso   : LeafIso 3421    := by decide +kernel
private theorem c3421_nof2  : NoF2ChkSq 3421  := by decide +kernel
private theorem c3421_nof3  : NoF3ChkSq 3421  := by decide +kernel
private theorem c3421_nof4z : NoF4zChkSq 3421 := by decide +kernel
theorem C'_3421 : C' 3421 :=
  ⟨c3421_sqf, c3421_range, c3421_ell, leafNSq_of_sq c3421_nsq, leafHAr_of_sq c3421_har,
   c3421_r, c3421_e', c3421_f1, leafS2_of_sq c3421_s2, leafS3_of_sq c3421_s3,
   c3421_iso, leafR8_of_sq c3421_nof2 c3421_nof3 c3421_nof4z⟩
theorem not_tile'_3421 (D : CongruentDissection 3421) : False :=
  not_tile_of_conditions' 3421 C'_3421 D

private theorem c3422_sqf   : LeafSqf 3422   := by decide +kernel
private theorem c3422_range : LeafRange 3422  := by decide +kernel
private theorem c3422_ell   : LeafEll 3422    := by decide +kernel
private theorem c3422_nsq   : NSqChkSq 3422   := by decide +kernel
private theorem c3422_har   : HArithChkSq 3422 := by decide +kernel
private theorem c3422_r     : LeafR 3422      := by decide +kernel
private theorem c3422_e'    : LeafE' 3422     := by decide +kernel
private theorem c3422_f1    : LeafF1 3422     := Or.inl (by decide)
private theorem c3422_s2    : S2ChkSq 3422    := by decide +kernel
private theorem c3422_s3    : S3ChkSq 3422    := by decide +kernel
private theorem c3422_iso   : LeafIso 3422    := by decide +kernel
private theorem c3422_nof2  : NoF2ChkSq 3422  := by decide +kernel
private theorem c3422_nof3  : NoF3ChkSq 3422  := by decide +kernel
private theorem c3422_nof4z : NoF4zChkSq 3422 := by decide +kernel
theorem C'_3422 : C' 3422 :=
  ⟨c3422_sqf, c3422_range, c3422_ell, leafNSq_of_sq c3422_nsq, leafHAr_of_sq c3422_har,
   c3422_r, c3422_e', c3422_f1, leafS2_of_sq c3422_s2, leafS3_of_sq c3422_s3,
   c3422_iso, leafR8_of_sq c3422_nof2 c3422_nof3 c3422_nof4z⟩
theorem not_tile'_3422 (D : CongruentDissection 3422) : False :=
  not_tile_of_conditions' 3422 C'_3422 D

end Erdos634.Draft.AllN2

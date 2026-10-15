/- AllN2Check233: N = 4333, 4334, 4339, 4341, 4342
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4333_sqf   : LeafSqf 4333   := by decide +kernel
private theorem c4333_range : LeafRange 4333  := by decide +kernel
private theorem c4333_ell   : LeafEll 4333    := by decide +kernel
private theorem c4333_nsq   : NSqChkSq 4333   := by decide +kernel
private theorem c4333_har   : HArithChkSq 4333 := by decide +kernel
private theorem c4333_r     : LeafR 4333      := by decide +kernel
private theorem c4333_e'    : LeafE' 4333     := by decide +kernel
private theorem c4333_f1    : LeafF1 4333     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4333_s2    : S2ChkSq 4333    := by decide +kernel
private theorem c4333_s3    : S3ChkSq 4333    := by decide +kernel
private theorem c4333_iso   : LeafIso 4333    := by decide +kernel
private theorem c4333_nof2  : NoF2ChkSq 4333  := by decide +kernel
private theorem c4333_nof3  : NoF3ChkSq 4333  := by decide +kernel
private theorem c4333_nof4z : NoF4zChkSq 4333 := by decide +kernel
theorem C'_4333 : C' 4333 :=
  ⟨c4333_sqf, c4333_range, c4333_ell, leafNSq_of_sq c4333_nsq, leafHAr_of_sq c4333_har,
   c4333_r, c4333_e', c4333_f1, leafS2_of_sq c4333_s2, leafS3_of_sq c4333_s3,
   c4333_iso, leafR8_of_sq c4333_nof2 c4333_nof3 c4333_nof4z⟩
theorem not_tile'_4333 (D : CongruentDissection 4333) : False :=
  not_tile_of_conditions' 4333 C'_4333 D

private theorem c4334_sqf   : LeafSqf 4334   := by decide +kernel
private theorem c4334_range : LeafRange 4334  := by decide +kernel
private theorem c4334_ell   : LeafEll 4334    := by decide +kernel
private theorem c4334_nsq   : NSqChkSq 4334   := by decide +kernel
private theorem c4334_har   : HArithChkSq 4334 := by decide +kernel
private theorem c4334_r     : LeafR 4334      := by decide +kernel
private theorem c4334_e'    : LeafE' 4334     := by decide +kernel
private theorem c4334_f1    : LeafF1 4334     := Or.inl (by decide)
private theorem c4334_s2    : S2ChkSq 4334    := by decide +kernel
private theorem c4334_s3    : S3ChkSq 4334    := by decide +kernel
private theorem c4334_iso   : LeafIso 4334    := by decide +kernel
private theorem c4334_nof2  : NoF2ChkSq 4334  := by decide +kernel
private theorem c4334_nof3  : NoF3ChkSq 4334  := by decide +kernel
private theorem c4334_nof4z : NoF4zChkSq 4334 := by decide +kernel
theorem C'_4334 : C' 4334 :=
  ⟨c4334_sqf, c4334_range, c4334_ell, leafNSq_of_sq c4334_nsq, leafHAr_of_sq c4334_har,
   c4334_r, c4334_e', c4334_f1, leafS2_of_sq c4334_s2, leafS3_of_sq c4334_s3,
   c4334_iso, leafR8_of_sq c4334_nof2 c4334_nof3 c4334_nof4z⟩
theorem not_tile'_4334 (D : CongruentDissection 4334) : False :=
  not_tile_of_conditions' 4334 C'_4334 D

private theorem c4339_sqf   : LeafSqf 4339   := by decide +kernel
private theorem c4339_range : LeafRange 4339  := by decide +kernel
private theorem c4339_ell   : LeafEll 4339    := by decide +kernel
private theorem c4339_nsq   : NSqChkSq 4339   := by decide +kernel
private theorem c4339_har   : HArithChkSq 4339 := by decide +kernel
private theorem c4339_r     : LeafR 4339      := by decide +kernel
private theorem c4339_e'    : LeafE' 4339     := by decide +kernel
private theorem c4339_f1    : LeafF1 4339     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4339_s2    : S2ChkSq 4339    := by decide +kernel
private theorem c4339_s3    : S3ChkSq 4339    := by decide +kernel
private theorem c4339_iso   : LeafIso 4339    := by decide +kernel
private theorem c4339_nof2  : NoF2ChkSq 4339  := by decide +kernel
private theorem c4339_nof3  : NoF3ChkSq 4339  := by decide +kernel
private theorem c4339_nof4z : NoF4zChkSq 4339 := by decide +kernel
theorem C'_4339 : C' 4339 :=
  ⟨c4339_sqf, c4339_range, c4339_ell, leafNSq_of_sq c4339_nsq, leafHAr_of_sq c4339_har,
   c4339_r, c4339_e', c4339_f1, leafS2_of_sq c4339_s2, leafS3_of_sq c4339_s3,
   c4339_iso, leafR8_of_sq c4339_nof2 c4339_nof3 c4339_nof4z⟩
theorem not_tile'_4339 (D : CongruentDissection 4339) : False :=
  not_tile_of_conditions' 4339 C'_4339 D

private theorem c4341_sqf   : LeafSqf 4341   := by decide +kernel
private theorem c4341_range : LeafRange 4341  := by decide +kernel
private theorem c4341_ell   : LeafEll 4341    := by decide +kernel
private theorem c4341_nsq   : NSqChkSq 4341   := by decide +kernel
private theorem c4341_har   : HArithChkSq 4341 := by decide +kernel
private theorem c4341_r     : LeafR 4341      := by decide +kernel
private theorem c4341_e'    : LeafE' 4341     := by decide +kernel
private theorem c4341_f1    : LeafF1 4341     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4341_s2    : S2ChkSq 4341    := by decide +kernel
private theorem c4341_s3    : S3ChkSq 4341    := by decide +kernel
private theorem c4341_iso   : LeafIso 4341    := by decide +kernel
private theorem c4341_nof2  : NoF2ChkSq 4341  := by decide +kernel
private theorem c4341_nof3  : NoF3ChkSq 4341  := by decide +kernel
private theorem c4341_nof4z : NoF4zChkSq 4341 := by decide +kernel
theorem C'_4341 : C' 4341 :=
  ⟨c4341_sqf, c4341_range, c4341_ell, leafNSq_of_sq c4341_nsq, leafHAr_of_sq c4341_har,
   c4341_r, c4341_e', c4341_f1, leafS2_of_sq c4341_s2, leafS3_of_sq c4341_s3,
   c4341_iso, leafR8_of_sq c4341_nof2 c4341_nof3 c4341_nof4z⟩
theorem not_tile'_4341 (D : CongruentDissection 4341) : False :=
  not_tile_of_conditions' 4341 C'_4341 D

private theorem c4342_sqf   : LeafSqf 4342   := by decide +kernel
private theorem c4342_range : LeafRange 4342  := by decide +kernel
private theorem c4342_ell   : LeafEll 4342    := by decide +kernel
private theorem c4342_nsq   : NSqChkSq 4342   := by decide +kernel
private theorem c4342_har   : HArithChkSq 4342 := by decide +kernel
private theorem c4342_r     : LeafR 4342      := by decide +kernel
private theorem c4342_e'    : LeafE' 4342     := by decide +kernel
private theorem c4342_f1    : LeafF1 4342     := Or.inl (by decide)
private theorem c4342_s2    : S2ChkSq 4342    := by decide +kernel
private theorem c4342_s3    : S3ChkSq 4342    := by decide +kernel
private theorem c4342_iso   : LeafIso 4342    := by decide +kernel
private theorem c4342_nof2  : NoF2ChkSq 4342  := by decide +kernel
private theorem c4342_nof3  : NoF3ChkSq 4342  := by decide +kernel
private theorem c4342_nof4z : NoF4zChkSq 4342 := by decide +kernel
theorem C'_4342 : C' 4342 :=
  ⟨c4342_sqf, c4342_range, c4342_ell, leafNSq_of_sq c4342_nsq, leafHAr_of_sq c4342_har,
   c4342_r, c4342_e', c4342_f1, leafS2_of_sq c4342_s2, leafS3_of_sq c4342_s3,
   c4342_iso, leafR8_of_sq c4342_nof2 c4342_nof3 c4342_nof4z⟩
theorem not_tile'_4342 (D : CongruentDissection 4342) : False :=
  not_tile_of_conditions' 4342 C'_4342 D

end Erdos634.Draft.AllN2

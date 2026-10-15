/- AllN2Check172: N = 3542, 3543, 3547, 3551, 3553
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3542_sqf   : LeafSqf 3542   := by decide +kernel
private theorem c3542_range : LeafRange 3542  := by decide +kernel
private theorem c3542_ell   : LeafEll 3542    := by decide +kernel
private theorem c3542_nsq   : NSqChkSq 3542   := by decide +kernel
private theorem c3542_har   : HArithChkSq 3542 := by decide +kernel
private theorem c3542_r     : LeafR 3542      := by decide +kernel
private theorem c3542_e'    : LeafE' 3542     := by decide +kernel
private theorem c3542_f1    : LeafF1 3542     := Or.inl (by decide)
private theorem c3542_s2    : S2ChkSq 3542    := by decide +kernel
private theorem c3542_s3    : S3ChkSq 3542    := by decide +kernel
private theorem c3542_iso   : LeafIso 3542    := by decide +kernel
private theorem c3542_nof2  : NoF2ChkSq 3542  := by decide +kernel
private theorem c3542_nof3  : NoF3ChkSq 3542  := by decide +kernel
private theorem c3542_nof4z : NoF4zChkSq 3542 := by decide +kernel
theorem C'_3542 : C' 3542 :=
  ⟨c3542_sqf, c3542_range, c3542_ell, leafNSq_of_sq c3542_nsq, leafHAr_of_sq c3542_har,
   c3542_r, c3542_e', c3542_f1, leafS2_of_sq c3542_s2, leafS3_of_sq c3542_s3,
   c3542_iso, leafR8_of_sq c3542_nof2 c3542_nof3 c3542_nof4z⟩
theorem not_tile'_3542 (D : CongruentDissection 3542) : False :=
  not_tile_of_conditions' 3542 C'_3542 D

private theorem c3543_sqf   : LeafSqf 3543   := by decide +kernel
private theorem c3543_range : LeafRange 3543  := by decide +kernel
private theorem c3543_ell   : LeafEll 3543    := by decide +kernel
private theorem c3543_nsq   : NSqChkSq 3543   := by decide +kernel
private theorem c3543_har   : HArithChkSq 3543 := by decide +kernel
private theorem c3543_r     : LeafR 3543      := by decide +kernel
private theorem c3543_e'    : LeafE' 3543     := by decide +kernel
private theorem c3543_f1    : LeafF1 3543     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3543_s2    : S2ChkSq 3543    := by decide +kernel
private theorem c3543_s3    : S3ChkSq 3543    := by decide +kernel
private theorem c3543_iso   : LeafIso 3543    := by decide +kernel
private theorem c3543_nof2  : NoF2ChkSq 3543  := by decide +kernel
private theorem c3543_nof3  : NoF3ChkSq 3543  := by decide +kernel
private theorem c3543_nof4z : NoF4zChkSq 3543 := by decide +kernel
theorem C'_3543 : C' 3543 :=
  ⟨c3543_sqf, c3543_range, c3543_ell, leafNSq_of_sq c3543_nsq, leafHAr_of_sq c3543_har,
   c3543_r, c3543_e', c3543_f1, leafS2_of_sq c3543_s2, leafS3_of_sq c3543_s3,
   c3543_iso, leafR8_of_sq c3543_nof2 c3543_nof3 c3543_nof4z⟩
theorem not_tile'_3543 (D : CongruentDissection 3543) : False :=
  not_tile_of_conditions' 3543 C'_3543 D

private theorem c3547_sqf   : LeafSqf 3547   := by decide +kernel
private theorem c3547_range : LeafRange 3547  := by decide +kernel
private theorem c3547_ell   : LeafEll 3547    := by decide +kernel
private theorem c3547_nsq   : NSqChkSq 3547   := by decide +kernel
private theorem c3547_har   : HArithChkSq 3547 := by decide +kernel
private theorem c3547_r     : LeafR 3547      := by decide +kernel
private theorem c3547_e'    : LeafE' 3547     := by decide +kernel
private theorem c3547_f1    : LeafF1 3547     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3547_s2    : S2ChkSq 3547    := by decide +kernel
private theorem c3547_s3    : S3ChkSq 3547    := by decide +kernel
private theorem c3547_iso   : LeafIso 3547    := by decide +kernel
private theorem c3547_nof2  : NoF2ChkSq 3547  := by decide +kernel
private theorem c3547_nof3  : NoF3ChkSq 3547  := by decide +kernel
private theorem c3547_nof4z : NoF4zChkSq 3547 := by decide +kernel
theorem C'_3547 : C' 3547 :=
  ⟨c3547_sqf, c3547_range, c3547_ell, leafNSq_of_sq c3547_nsq, leafHAr_of_sq c3547_har,
   c3547_r, c3547_e', c3547_f1, leafS2_of_sq c3547_s2, leafS3_of_sq c3547_s3,
   c3547_iso, leafR8_of_sq c3547_nof2 c3547_nof3 c3547_nof4z⟩
theorem not_tile'_3547 (D : CongruentDissection 3547) : False :=
  not_tile_of_conditions' 3547 C'_3547 D

private theorem c3551_sqf   : LeafSqf 3551   := by decide +kernel
private theorem c3551_range : LeafRange 3551  := by decide +kernel
private theorem c3551_ell   : LeafEll 3551    := by decide +kernel
private theorem c3551_nsq   : NSqChkSq 3551   := by decide +kernel
private theorem c3551_har   : HArithChkSq 3551 := by decide +kernel
private theorem c3551_r     : LeafR 3551      := by decide +kernel
private theorem c3551_e'    : LeafE' 3551     := by decide +kernel
private theorem c3551_f1    : LeafF1 3551     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3551_s2    : S2ChkSq 3551    := by decide +kernel
private theorem c3551_s3    : S3ChkSq 3551    := by decide +kernel
private theorem c3551_iso   : LeafIso 3551    := by decide +kernel
private theorem c3551_nof2  : NoF2ChkSq 3551  := by decide +kernel
private theorem c3551_nof3  : NoF3ChkSq 3551  := by decide +kernel
private theorem c3551_nof4z : NoF4zChkSq 3551 := by decide +kernel
theorem C'_3551 : C' 3551 :=
  ⟨c3551_sqf, c3551_range, c3551_ell, leafNSq_of_sq c3551_nsq, leafHAr_of_sq c3551_har,
   c3551_r, c3551_e', c3551_f1, leafS2_of_sq c3551_s2, leafS3_of_sq c3551_s3,
   c3551_iso, leafR8_of_sq c3551_nof2 c3551_nof3 c3551_nof4z⟩
theorem not_tile'_3551 (D : CongruentDissection 3551) : False :=
  not_tile_of_conditions' 3551 C'_3551 D

private theorem c3553_sqf   : LeafSqf 3553   := by decide +kernel
private theorem c3553_range : LeafRange 3553  := by decide +kernel
private theorem c3553_ell   : LeafEll 3553    := by decide +kernel
private theorem c3553_nsq   : NSqChkSq 3553   := by decide +kernel
private theorem c3553_har   : HArithChkSq 3553 := by decide +kernel
private theorem c3553_r     : LeafR 3553      := by decide +kernel
private theorem c3553_e'    : LeafE' 3553     := by decide +kernel
private theorem c3553_f1    : LeafF1 3553     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3553_s2    : S2ChkSq 3553    := by decide +kernel
private theorem c3553_s3    : S3ChkSq 3553    := by decide +kernel
private theorem c3553_iso   : LeafIso 3553    := by decide +kernel
private theorem c3553_nof2  : NoF2ChkSq 3553  := by decide +kernel
private theorem c3553_nof3  : NoF3ChkSq 3553  := by decide +kernel
private theorem c3553_nof4z : NoF4zChkSq 3553 := by decide +kernel
theorem C'_3553 : C' 3553 :=
  ⟨c3553_sqf, c3553_range, c3553_ell, leafNSq_of_sq c3553_nsq, leafHAr_of_sq c3553_har,
   c3553_r, c3553_e', c3553_f1, leafS2_of_sq c3553_s2, leafS3_of_sq c3553_s3,
   c3553_iso, leafR8_of_sq c3553_nof2 c3553_nof3 c3553_nof4z⟩
theorem not_tile'_3553 (D : CongruentDissection 3553) : False :=
  not_tile_of_conditions' 3553 C'_3553 D

end Erdos634.Draft.AllN2

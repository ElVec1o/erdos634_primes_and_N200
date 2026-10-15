/- AllN2Check171: N = 3523, 3526, 3527, 3535, 3539
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3523_sqf   : LeafSqf 3523   := by decide +kernel
private theorem c3523_range : LeafRange 3523  := by decide +kernel
private theorem c3523_ell   : LeafEll 3523    := by decide +kernel
private theorem c3523_nsq   : NSqChkSq 3523   := by decide +kernel
private theorem c3523_har   : HArithChkSq 3523 := by decide +kernel
private theorem c3523_r     : LeafR 3523      := by decide +kernel
private theorem c3523_e'    : LeafE' 3523     := by decide +kernel
private theorem c3523_f1    : LeafF1 3523     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3523_s2    : S2ChkSq 3523    := by decide +kernel
private theorem c3523_s3    : S3ChkSq 3523    := by decide +kernel
private theorem c3523_iso   : LeafIso 3523    := by decide +kernel
private theorem c3523_nof2  : NoF2ChkSq 3523  := by decide +kernel
private theorem c3523_nof3  : NoF3ChkSq 3523  := by decide +kernel
private theorem c3523_nof4z : NoF4zChkSq 3523 := by decide +kernel
theorem C'_3523 : C' 3523 :=
  ⟨c3523_sqf, c3523_range, c3523_ell, leafNSq_of_sq c3523_nsq, leafHAr_of_sq c3523_har,
   c3523_r, c3523_e', c3523_f1, leafS2_of_sq c3523_s2, leafS3_of_sq c3523_s3,
   c3523_iso, leafR8_of_sq c3523_nof2 c3523_nof3 c3523_nof4z⟩
theorem not_tile'_3523 (D : CongruentDissection 3523) : False :=
  not_tile_of_conditions' 3523 C'_3523 D

private theorem c3526_sqf   : LeafSqf 3526   := by decide +kernel
private theorem c3526_range : LeafRange 3526  := by decide +kernel
private theorem c3526_ell   : LeafEll 3526    := by decide +kernel
private theorem c3526_nsq   : NSqChkSq 3526   := by decide +kernel
private theorem c3526_har   : HArithChkSq 3526 := by decide +kernel
private theorem c3526_r     : LeafR 3526      := by decide +kernel
private theorem c3526_e'    : LeafE' 3526     := by decide +kernel
private theorem c3526_f1    : LeafF1 3526     := Or.inl (by decide)
private theorem c3526_s2    : S2ChkSq 3526    := by decide +kernel
private theorem c3526_s3    : S3ChkSq 3526    := by decide +kernel
private theorem c3526_iso   : LeafIso 3526    := by decide +kernel
private theorem c3526_nof2  : NoF2ChkSq 3526  := by decide +kernel
private theorem c3526_nof3  : NoF3ChkSq 3526  := by decide +kernel
private theorem c3526_nof4z : NoF4zChkSq 3526 := by decide +kernel
theorem C'_3526 : C' 3526 :=
  ⟨c3526_sqf, c3526_range, c3526_ell, leafNSq_of_sq c3526_nsq, leafHAr_of_sq c3526_har,
   c3526_r, c3526_e', c3526_f1, leafS2_of_sq c3526_s2, leafS3_of_sq c3526_s3,
   c3526_iso, leafR8_of_sq c3526_nof2 c3526_nof3 c3526_nof4z⟩
theorem not_tile'_3526 (D : CongruentDissection 3526) : False :=
  not_tile_of_conditions' 3526 C'_3526 D

private theorem c3527_sqf   : LeafSqf 3527   := by decide +kernel
private theorem c3527_range : LeafRange 3527  := by decide +kernel
private theorem c3527_ell   : LeafEll 3527    := by decide +kernel
private theorem c3527_nsq   : NSqChkSq 3527   := by decide +kernel
private theorem c3527_har   : HArithChkSq 3527 := by decide +kernel
private theorem c3527_r     : LeafR 3527      := by decide +kernel
private theorem c3527_e'    : LeafE' 3527     := by decide +kernel
private theorem c3527_f1    : LeafF1 3527     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3527_s2    : S2ChkSq 3527    := by decide +kernel
private theorem c3527_s3    : S3ChkSq 3527    := by decide +kernel
private theorem c3527_iso   : LeafIso 3527    := by decide +kernel
private theorem c3527_nof2  : NoF2ChkSq 3527  := by decide +kernel
private theorem c3527_nof3  : NoF3ChkSq 3527  := by decide +kernel
private theorem c3527_nof4z : NoF4zChkSq 3527 := by decide +kernel
theorem C'_3527 : C' 3527 :=
  ⟨c3527_sqf, c3527_range, c3527_ell, leafNSq_of_sq c3527_nsq, leafHAr_of_sq c3527_har,
   c3527_r, c3527_e', c3527_f1, leafS2_of_sq c3527_s2, leafS3_of_sq c3527_s3,
   c3527_iso, leafR8_of_sq c3527_nof2 c3527_nof3 c3527_nof4z⟩
theorem not_tile'_3527 (D : CongruentDissection 3527) : False :=
  not_tile_of_conditions' 3527 C'_3527 D

private theorem c3535_sqf   : LeafSqf 3535   := by decide +kernel
private theorem c3535_range : LeafRange 3535  := by decide +kernel
private theorem c3535_ell   : LeafEll 3535    := by decide +kernel
private theorem c3535_nsq   : NSqChkSq 3535   := by decide +kernel
private theorem c3535_har   : HArithChkSq 3535 := by decide +kernel
private theorem c3535_r     : LeafR 3535      := by decide +kernel
private theorem c3535_e'    : LeafE' 3535     := by decide +kernel
private theorem c3535_f1    : LeafF1 3535     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3535_s2    : S2ChkSq 3535    := by decide +kernel
private theorem c3535_s3    : S3ChkSq 3535    := by decide +kernel
private theorem c3535_iso   : LeafIso 3535    := by decide +kernel
private theorem c3535_nof2  : NoF2ChkSq 3535  := by decide +kernel
private theorem c3535_nof3  : NoF3ChkSq 3535  := by decide +kernel
private theorem c3535_nof4z : NoF4zChkSq 3535 := by decide +kernel
theorem C'_3535 : C' 3535 :=
  ⟨c3535_sqf, c3535_range, c3535_ell, leafNSq_of_sq c3535_nsq, leafHAr_of_sq c3535_har,
   c3535_r, c3535_e', c3535_f1, leafS2_of_sq c3535_s2, leafS3_of_sq c3535_s3,
   c3535_iso, leafR8_of_sq c3535_nof2 c3535_nof3 c3535_nof4z⟩
theorem not_tile'_3535 (D : CongruentDissection 3535) : False :=
  not_tile_of_conditions' 3535 C'_3535 D

private theorem c3539_sqf   : LeafSqf 3539   := by decide +kernel
private theorem c3539_range : LeafRange 3539  := by decide +kernel
private theorem c3539_ell   : LeafEll 3539    := by decide +kernel
private theorem c3539_nsq   : NSqChkSq 3539   := by decide +kernel
private theorem c3539_har   : HArithChkSq 3539 := by decide +kernel
private theorem c3539_r     : LeafR 3539      := by decide +kernel
private theorem c3539_e'    : LeafE' 3539     := by decide +kernel
private theorem c3539_f1    : LeafF1 3539     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3539_s2    : S2ChkSq 3539    := by decide +kernel
private theorem c3539_s3    : S3ChkSq 3539    := by decide +kernel
private theorem c3539_iso   : LeafIso 3539    := by decide +kernel
private theorem c3539_nof2  : NoF2ChkSq 3539  := by decide +kernel
private theorem c3539_nof3  : NoF3ChkSq 3539  := by decide +kernel
private theorem c3539_nof4z : NoF4zChkSq 3539 := by decide +kernel
theorem C'_3539 : C' 3539 :=
  ⟨c3539_sqf, c3539_range, c3539_ell, leafNSq_of_sq c3539_nsq, leafHAr_of_sq c3539_har,
   c3539_r, c3539_e', c3539_f1, leafS2_of_sq c3539_s2, leafS3_of_sq c3539_s3,
   c3539_iso, leafR8_of_sq c3539_nof2 c3539_nof3 c3539_nof4z⟩
theorem not_tile'_3539 (D : CongruentDissection 3539) : False :=
  not_tile_of_conditions' 3539 C'_3539 D

end Erdos634.Draft.AllN2

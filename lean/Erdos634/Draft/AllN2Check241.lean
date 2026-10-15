/- AllN2Check241: N = 4433, 4434, 4435, 4438, 4439
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4433_sqf   : LeafSqf 4433   := by decide +kernel
private theorem c4433_range : LeafRange 4433  := by decide +kernel
private theorem c4433_ell   : LeafEll 4433    := by decide +kernel
private theorem c4433_nsq   : NSqChkSq 4433   := by decide +kernel
private theorem c4433_har   : HArithChkSq 4433 := by decide +kernel
private theorem c4433_r     : LeafR 4433      := by decide +kernel
private theorem c4433_e'    : LeafE' 4433     := by decide +kernel
private theorem c4433_f1    : LeafF1 4433     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4433_s2    : S2ChkSq 4433    := by decide +kernel
private theorem c4433_s3    : S3ChkSq 4433    := by decide +kernel
private theorem c4433_iso   : LeafIso 4433    := by decide +kernel
private theorem c4433_nof2  : NoF2ChkSq 4433  := by decide +kernel
private theorem c4433_nof3  : NoF3ChkSq 4433  := by decide +kernel
private theorem c4433_nof4z : NoF4zChkSq 4433 := by decide +kernel
theorem C'_4433 : C' 4433 :=
  ⟨c4433_sqf, c4433_range, c4433_ell, leafNSq_of_sq c4433_nsq, leafHAr_of_sq c4433_har,
   c4433_r, c4433_e', c4433_f1, leafS2_of_sq c4433_s2, leafS3_of_sq c4433_s3,
   c4433_iso, leafR8_of_sq c4433_nof2 c4433_nof3 c4433_nof4z⟩
theorem not_tile'_4433 (D : CongruentDissection 4433) : False :=
  not_tile_of_conditions' 4433 C'_4433 D

private theorem c4434_sqf   : LeafSqf 4434   := by decide +kernel
private theorem c4434_range : LeafRange 4434  := by decide +kernel
private theorem c4434_ell   : LeafEll 4434    := by decide +kernel
private theorem c4434_nsq   : NSqChkSq 4434   := by decide +kernel
private theorem c4434_har   : HArithChkSq 4434 := by decide +kernel
private theorem c4434_r     : LeafR 4434      := by decide +kernel
private theorem c4434_e'    : LeafE' 4434     := by decide +kernel
private theorem c4434_f1    : LeafF1 4434     := Or.inl (by decide)
private theorem c4434_s2    : S2ChkSq 4434    := by decide +kernel
private theorem c4434_s3    : S3ChkSq 4434    := by decide +kernel
private theorem c4434_iso   : LeafIso 4434    := by decide +kernel
private theorem c4434_nof2  : NoF2ChkSq 4434  := by decide +kernel
private theorem c4434_nof3  : NoF3ChkSq 4434  := by decide +kernel
private theorem c4434_nof4z : NoF4zChkSq 4434 := by decide +kernel
theorem C'_4434 : C' 4434 :=
  ⟨c4434_sqf, c4434_range, c4434_ell, leafNSq_of_sq c4434_nsq, leafHAr_of_sq c4434_har,
   c4434_r, c4434_e', c4434_f1, leafS2_of_sq c4434_s2, leafS3_of_sq c4434_s3,
   c4434_iso, leafR8_of_sq c4434_nof2 c4434_nof3 c4434_nof4z⟩
theorem not_tile'_4434 (D : CongruentDissection 4434) : False :=
  not_tile_of_conditions' 4434 C'_4434 D

private theorem c4435_sqf   : LeafSqf 4435   := by decide +kernel
private theorem c4435_range : LeafRange 4435  := by decide +kernel
private theorem c4435_ell   : LeafEll 4435    := by decide +kernel
private theorem c4435_nsq   : NSqChkSq 4435   := by decide +kernel
private theorem c4435_har   : HArithChkSq 4435 := by decide +kernel
private theorem c4435_r     : LeafR 4435      := by decide +kernel
private theorem c4435_e'    : LeafE' 4435     := by decide +kernel
private theorem c4435_f1    : LeafF1 4435     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4435_s2    : S2ChkSq 4435    := by decide +kernel
private theorem c4435_s3    : S3ChkSq 4435    := by decide +kernel
private theorem c4435_iso   : LeafIso 4435    := by decide +kernel
private theorem c4435_nof2  : NoF2ChkSq 4435  := by decide +kernel
private theorem c4435_nof3  : NoF3ChkSq 4435  := by decide +kernel
private theorem c4435_nof4z : NoF4zChkSq 4435 := by decide +kernel
theorem C'_4435 : C' 4435 :=
  ⟨c4435_sqf, c4435_range, c4435_ell, leafNSq_of_sq c4435_nsq, leafHAr_of_sq c4435_har,
   c4435_r, c4435_e', c4435_f1, leafS2_of_sq c4435_s2, leafS3_of_sq c4435_s3,
   c4435_iso, leafR8_of_sq c4435_nof2 c4435_nof3 c4435_nof4z⟩
theorem not_tile'_4435 (D : CongruentDissection 4435) : False :=
  not_tile_of_conditions' 4435 C'_4435 D

private theorem c4438_sqf   : LeafSqf 4438   := by decide +kernel
private theorem c4438_range : LeafRange 4438  := by decide +kernel
private theorem c4438_ell   : LeafEll 4438    := by decide +kernel
private theorem c4438_nsq   : NSqChkSq 4438   := by decide +kernel
private theorem c4438_har   : HArithChkSq 4438 := by decide +kernel
private theorem c4438_r     : LeafR 4438      := by decide +kernel
private theorem c4438_e'    : LeafE' 4438     := by decide +kernel
private theorem c4438_f1    : LeafF1 4438     := Or.inl (by decide)
private theorem c4438_s2    : S2ChkSq 4438    := by decide +kernel
private theorem c4438_s3    : S3ChkSq 4438    := by decide +kernel
private theorem c4438_iso   : LeafIso 4438    := by decide +kernel
private theorem c4438_nof2  : NoF2ChkSq 4438  := by decide +kernel
private theorem c4438_nof3  : NoF3ChkSq 4438  := by decide +kernel
private theorem c4438_nof4z : NoF4zChkSq 4438 := by decide +kernel
theorem C'_4438 : C' 4438 :=
  ⟨c4438_sqf, c4438_range, c4438_ell, leafNSq_of_sq c4438_nsq, leafHAr_of_sq c4438_har,
   c4438_r, c4438_e', c4438_f1, leafS2_of_sq c4438_s2, leafS3_of_sq c4438_s3,
   c4438_iso, leafR8_of_sq c4438_nof2 c4438_nof3 c4438_nof4z⟩
theorem not_tile'_4438 (D : CongruentDissection 4438) : False :=
  not_tile_of_conditions' 4438 C'_4438 D

private theorem c4439_sqf   : LeafSqf 4439   := by decide +kernel
private theorem c4439_range : LeafRange 4439  := by decide +kernel
private theorem c4439_ell   : LeafEll 4439    := by decide +kernel
private theorem c4439_nsq   : NSqChkSq 4439   := by decide +kernel
private theorem c4439_har   : HArithChkSq 4439 := by decide +kernel
private theorem c4439_r     : LeafR 4439      := by decide +kernel
private theorem c4439_e'    : LeafE' 4439     := by decide +kernel
private theorem c4439_f1    : LeafF1 4439     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4439_s2    : S2ChkSq 4439    := by decide +kernel
private theorem c4439_s3    : S3ChkSq 4439    := by decide +kernel
private theorem c4439_iso   : LeafIso 4439    := by decide +kernel
private theorem c4439_nof2  : NoF2ChkSq 4439  := by decide +kernel
private theorem c4439_nof3  : NoF3ChkSq 4439  := by decide +kernel
private theorem c4439_nof4z : NoF4zChkSq 4439 := by decide +kernel
theorem C'_4439 : C' 4439 :=
  ⟨c4439_sqf, c4439_range, c4439_ell, leafNSq_of_sq c4439_nsq, leafHAr_of_sq c4439_har,
   c4439_r, c4439_e', c4439_f1, leafS2_of_sq c4439_s2, leafS3_of_sq c4439_s3,
   c4439_iso, leafR8_of_sq c4439_nof2 c4439_nof3 c4439_nof4z⟩
theorem not_tile'_4439 (D : CongruentDissection 4439) : False :=
  not_tile_of_conditions' 4439 C'_4439 D

end Erdos634.Draft.AllN2

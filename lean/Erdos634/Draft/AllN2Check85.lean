/- AllN2Check85: N = 2431, 2433, 2435, 2438, 2443
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2431_sqf   : LeafSqf 2431   := by decide +kernel
private theorem c2431_range : LeafRange 2431  := by decide +kernel
private theorem c2431_ell   : LeafEll 2431    := by decide +kernel
private theorem c2431_nsq   : NSqChkSq 2431   := by decide +kernel
private theorem c2431_har   : HArithChkSq 2431 := by decide +kernel
private theorem c2431_r     : LeafR 2431      := by decide +kernel
private theorem c2431_e'    : LeafE' 2431     := by decide +kernel
private theorem c2431_f1    : LeafF1 2431     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2431_s2    : S2ChkSq 2431    := by decide +kernel
private theorem c2431_s3    : S3ChkSq 2431    := by decide +kernel
private theorem c2431_iso   : LeafIso 2431    := by decide +kernel
private theorem c2431_nof2  : NoF2ChkSq 2431  := by decide +kernel
private theorem c2431_nof3  : NoF3ChkSq 2431  := by decide +kernel
private theorem c2431_nof4z : NoF4zChkSq 2431 := by decide +kernel
theorem C'_2431 : C' 2431 :=
  ⟨c2431_sqf, c2431_range, c2431_ell, leafNSq_of_sq c2431_nsq, leafHAr_of_sq c2431_har,
   c2431_r, c2431_e', c2431_f1, leafS2_of_sq c2431_s2, leafS3_of_sq c2431_s3,
   c2431_iso, leafR8_of_sq c2431_nof2 c2431_nof3 c2431_nof4z⟩
theorem not_tile'_2431 (D : CongruentDissection 2431) : False :=
  not_tile_of_conditions' 2431 C'_2431 D

private theorem c2433_sqf   : LeafSqf 2433   := by decide +kernel
private theorem c2433_range : LeafRange 2433  := by decide +kernel
private theorem c2433_ell   : LeafEll 2433    := by decide +kernel
private theorem c2433_nsq   : NSqChkSq 2433   := by decide +kernel
private theorem c2433_har   : HArithChkSq 2433 := by decide +kernel
private theorem c2433_r     : LeafR 2433      := by decide +kernel
private theorem c2433_e'    : LeafE' 2433     := by decide +kernel
private theorem c2433_f1    : LeafF1 2433     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2433_s2    : S2ChkSq 2433    := by decide +kernel
private theorem c2433_s3    : S3ChkSq 2433    := by decide +kernel
private theorem c2433_iso   : LeafIso 2433    := by decide +kernel
private theorem c2433_nof2  : NoF2ChkSq 2433  := by decide +kernel
private theorem c2433_nof3  : NoF3ChkSq 2433  := by decide +kernel
private theorem c2433_nof4z : NoF4zChkSq 2433 := by decide +kernel
theorem C'_2433 : C' 2433 :=
  ⟨c2433_sqf, c2433_range, c2433_ell, leafNSq_of_sq c2433_nsq, leafHAr_of_sq c2433_har,
   c2433_r, c2433_e', c2433_f1, leafS2_of_sq c2433_s2, leafS3_of_sq c2433_s3,
   c2433_iso, leafR8_of_sq c2433_nof2 c2433_nof3 c2433_nof4z⟩
theorem not_tile'_2433 (D : CongruentDissection 2433) : False :=
  not_tile_of_conditions' 2433 C'_2433 D

private theorem c2435_sqf   : LeafSqf 2435   := by decide +kernel
private theorem c2435_range : LeafRange 2435  := by decide +kernel
private theorem c2435_ell   : LeafEll 2435    := by decide +kernel
private theorem c2435_nsq   : NSqChkSq 2435   := by decide +kernel
private theorem c2435_har   : HArithChkSq 2435 := by decide +kernel
private theorem c2435_r     : LeafR 2435      := by decide +kernel
private theorem c2435_e'    : LeafE' 2435     := by decide +kernel
private theorem c2435_f1    : LeafF1 2435     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2435_s2    : S2ChkSq 2435    := by decide +kernel
private theorem c2435_s3    : S3ChkSq 2435    := by decide +kernel
private theorem c2435_iso   : LeafIso 2435    := by decide +kernel
private theorem c2435_nof2  : NoF2ChkSq 2435  := by decide +kernel
private theorem c2435_nof3  : NoF3ChkSq 2435  := by decide +kernel
private theorem c2435_nof4z : NoF4zChkSq 2435 := by decide +kernel
theorem C'_2435 : C' 2435 :=
  ⟨c2435_sqf, c2435_range, c2435_ell, leafNSq_of_sq c2435_nsq, leafHAr_of_sq c2435_har,
   c2435_r, c2435_e', c2435_f1, leafS2_of_sq c2435_s2, leafS3_of_sq c2435_s3,
   c2435_iso, leafR8_of_sq c2435_nof2 c2435_nof3 c2435_nof4z⟩
theorem not_tile'_2435 (D : CongruentDissection 2435) : False :=
  not_tile_of_conditions' 2435 C'_2435 D

private theorem c2438_sqf   : LeafSqf 2438   := by decide +kernel
private theorem c2438_range : LeafRange 2438  := by decide +kernel
private theorem c2438_ell   : LeafEll 2438    := by decide +kernel
private theorem c2438_nsq   : NSqChkSq 2438   := by decide +kernel
private theorem c2438_har   : HArithChkSq 2438 := by decide +kernel
private theorem c2438_r     : LeafR 2438      := by decide +kernel
private theorem c2438_e'    : LeafE' 2438     := by decide +kernel
private theorem c2438_f1    : LeafF1 2438     := Or.inl (by decide)
private theorem c2438_s2    : S2ChkSq 2438    := by decide +kernel
private theorem c2438_s3    : S3ChkSq 2438    := by decide +kernel
private theorem c2438_iso   : LeafIso 2438    := by decide +kernel
private theorem c2438_nof2  : NoF2ChkSq 2438  := by decide +kernel
private theorem c2438_nof3  : NoF3ChkSq 2438  := by decide +kernel
private theorem c2438_nof4z : NoF4zChkSq 2438 := by decide +kernel
theorem C'_2438 : C' 2438 :=
  ⟨c2438_sqf, c2438_range, c2438_ell, leafNSq_of_sq c2438_nsq, leafHAr_of_sq c2438_har,
   c2438_r, c2438_e', c2438_f1, leafS2_of_sq c2438_s2, leafS3_of_sq c2438_s3,
   c2438_iso, leafR8_of_sq c2438_nof2 c2438_nof3 c2438_nof4z⟩
theorem not_tile'_2438 (D : CongruentDissection 2438) : False :=
  not_tile_of_conditions' 2438 C'_2438 D

private theorem c2443_sqf   : LeafSqf 2443   := by decide +kernel
private theorem c2443_range : LeafRange 2443  := by decide +kernel
private theorem c2443_ell   : LeafEll 2443    := by decide +kernel
private theorem c2443_nsq   : NSqChkSq 2443   := by decide +kernel
private theorem c2443_har   : HArithChkSq 2443 := by decide +kernel
private theorem c2443_r     : LeafR 2443      := by decide +kernel
private theorem c2443_e'    : LeafE' 2443     := by decide +kernel
private theorem c2443_f1    : LeafF1 2443     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2443_s2    : S2ChkSq 2443    := by decide +kernel
private theorem c2443_s3    : S3ChkSq 2443    := by decide +kernel
private theorem c2443_iso   : LeafIso 2443    := by decide +kernel
private theorem c2443_nof2  : NoF2ChkSq 2443  := by decide +kernel
private theorem c2443_nof3  : NoF3ChkSq 2443  := by decide +kernel
private theorem c2443_nof4z : NoF4zChkSq 2443 := by decide +kernel
theorem C'_2443 : C' 2443 :=
  ⟨c2443_sqf, c2443_range, c2443_ell, leafNSq_of_sq c2443_nsq, leafHAr_of_sq c2443_har,
   c2443_r, c2443_e', c2443_f1, leafS2_of_sq c2443_s2, leafS3_of_sq c2443_s3,
   c2443_iso, leafR8_of_sq c2443_nof2 c2443_nof3 c2443_nof4z⟩
theorem not_tile'_2443 (D : CongruentDissection 2443) : False :=
  not_tile_of_conditions' 2443 C'_2443 D

end Erdos634.Draft.AllN2

/- AllN2Check16: N = 469, 471, 489, 497, 501, 511, 515, 519, 535, 537
   Squarefree exclusions via C' with sqrt-bounded checks (Wave-2 OOM fix). -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c469_sqf   : LeafSqf 469   := by decide +kernel
private theorem c469_range : LeafRange 469  := by decide +kernel
private theorem c469_ell   : LeafEll 469    := by decide +kernel
private theorem c469_nsq   : NSqChkSq 469   := by decide +kernel
private theorem c469_har   : HArithChkSq 469 := by decide +kernel
private theorem c469_r     : LeafR 469      := by decide +kernel
private theorem c469_e'    : LeafE' 469     := by decide +kernel
private theorem c469_f1    : LeafF1 469     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c469_s2    : S2ChkSq 469    := by decide +kernel
private theorem c469_s3    : S3ChkSq 469    := by decide +kernel
private theorem c469_iso   : LeafIso 469    := by decide +kernel
private theorem c469_nof2  : NoF2ChkSq 469  := by decide +kernel
private theorem c469_nof3  : NoF3ChkSq 469  := by decide +kernel
private theorem c469_nof4z : NoF4zChkSq 469 := by decide +kernel
theorem C'_469 : C' 469 :=
  ⟨c469_sqf, c469_range, c469_ell, leafNSq_of_sq c469_nsq, leafHAr_of_sq c469_har,
   c469_r, c469_e', c469_f1, leafS2_of_sq c469_s2, leafS3_of_sq c469_s3,
   c469_iso, leafR8_of_sq c469_nof2 c469_nof3 c469_nof4z⟩
theorem not_tile'_469 (D : CongruentDissection 469) : False :=
  not_tile_of_conditions' 469 C'_469 D

private theorem c471_sqf   : LeafSqf 471   := by decide +kernel
private theorem c471_range : LeafRange 471  := by decide +kernel
private theorem c471_ell   : LeafEll 471    := by decide +kernel
private theorem c471_nsq   : NSqChkSq 471   := by decide +kernel
private theorem c471_har   : HArithChkSq 471 := by decide +kernel
private theorem c471_r     : LeafR 471      := by decide +kernel
private theorem c471_e'    : LeafE' 471     := by decide +kernel
private theorem c471_f1    : LeafF1 471     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c471_s2    : S2ChkSq 471    := by decide +kernel
private theorem c471_s3    : S3ChkSq 471    := by decide +kernel
private theorem c471_iso   : LeafIso 471    := by decide +kernel
private theorem c471_nof2  : NoF2ChkSq 471  := by decide +kernel
private theorem c471_nof3  : NoF3ChkSq 471  := by decide +kernel
private theorem c471_nof4z : NoF4zChkSq 471 := by decide +kernel
theorem C'_471 : C' 471 :=
  ⟨c471_sqf, c471_range, c471_ell, leafNSq_of_sq c471_nsq, leafHAr_of_sq c471_har,
   c471_r, c471_e', c471_f1, leafS2_of_sq c471_s2, leafS3_of_sq c471_s3,
   c471_iso, leafR8_of_sq c471_nof2 c471_nof3 c471_nof4z⟩
theorem not_tile'_471 (D : CongruentDissection 471) : False :=
  not_tile_of_conditions' 471 C'_471 D

private theorem c489_sqf   : LeafSqf 489   := by decide +kernel
private theorem c489_range : LeafRange 489  := by decide +kernel
private theorem c489_ell   : LeafEll 489    := by decide +kernel
private theorem c489_nsq   : NSqChkSq 489   := by decide +kernel
private theorem c489_har   : HArithChkSq 489 := by decide +kernel
private theorem c489_r     : LeafR 489      := by decide +kernel
private theorem c489_e'    : LeafE' 489     := by decide +kernel
private theorem c489_f1    : LeafF1 489     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c489_s2    : S2ChkSq 489    := by decide +kernel
private theorem c489_s3    : S3ChkSq 489    := by decide +kernel
private theorem c489_iso   : LeafIso 489    := by decide +kernel
private theorem c489_nof2  : NoF2ChkSq 489  := by decide +kernel
private theorem c489_nof3  : NoF3ChkSq 489  := by decide +kernel
private theorem c489_nof4z : NoF4zChkSq 489 := by decide +kernel
theorem C'_489 : C' 489 :=
  ⟨c489_sqf, c489_range, c489_ell, leafNSq_of_sq c489_nsq, leafHAr_of_sq c489_har,
   c489_r, c489_e', c489_f1, leafS2_of_sq c489_s2, leafS3_of_sq c489_s3,
   c489_iso, leafR8_of_sq c489_nof2 c489_nof3 c489_nof4z⟩
theorem not_tile'_489 (D : CongruentDissection 489) : False :=
  not_tile_of_conditions' 489 C'_489 D

private theorem c497_sqf   : LeafSqf 497   := by decide +kernel
private theorem c497_range : LeafRange 497  := by decide +kernel
private theorem c497_ell   : LeafEll 497    := by decide +kernel
private theorem c497_nsq   : NSqChkSq 497   := by decide +kernel
private theorem c497_har   : HArithChkSq 497 := by decide +kernel
private theorem c497_r     : LeafR 497      := by decide +kernel
private theorem c497_e'    : LeafE' 497     := by decide +kernel
private theorem c497_f1    : LeafF1 497     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c497_s2    : S2ChkSq 497    := by decide +kernel
private theorem c497_s3    : S3ChkSq 497    := by decide +kernel
private theorem c497_iso   : LeafIso 497    := by decide +kernel
private theorem c497_nof2  : NoF2ChkSq 497  := by decide +kernel
private theorem c497_nof3  : NoF3ChkSq 497  := by decide +kernel
private theorem c497_nof4z : NoF4zChkSq 497 := by decide +kernel
theorem C'_497 : C' 497 :=
  ⟨c497_sqf, c497_range, c497_ell, leafNSq_of_sq c497_nsq, leafHAr_of_sq c497_har,
   c497_r, c497_e', c497_f1, leafS2_of_sq c497_s2, leafS3_of_sq c497_s3,
   c497_iso, leafR8_of_sq c497_nof2 c497_nof3 c497_nof4z⟩
theorem not_tile'_497 (D : CongruentDissection 497) : False :=
  not_tile_of_conditions' 497 C'_497 D

private theorem c501_sqf   : LeafSqf 501   := by decide +kernel
private theorem c501_range : LeafRange 501  := by decide +kernel
private theorem c501_ell   : LeafEll 501    := by decide +kernel
private theorem c501_nsq   : NSqChkSq 501   := by decide +kernel
private theorem c501_har   : HArithChkSq 501 := by decide +kernel
private theorem c501_r     : LeafR 501      := by decide +kernel
private theorem c501_e'    : LeafE' 501     := by decide +kernel
private theorem c501_f1    : LeafF1 501     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c501_s2    : S2ChkSq 501    := by decide +kernel
private theorem c501_s3    : S3ChkSq 501    := by decide +kernel
private theorem c501_iso   : LeafIso 501    := by decide +kernel
private theorem c501_nof2  : NoF2ChkSq 501  := by decide +kernel
private theorem c501_nof3  : NoF3ChkSq 501  := by decide +kernel
private theorem c501_nof4z : NoF4zChkSq 501 := by decide +kernel
theorem C'_501 : C' 501 :=
  ⟨c501_sqf, c501_range, c501_ell, leafNSq_of_sq c501_nsq, leafHAr_of_sq c501_har,
   c501_r, c501_e', c501_f1, leafS2_of_sq c501_s2, leafS3_of_sq c501_s3,
   c501_iso, leafR8_of_sq c501_nof2 c501_nof3 c501_nof4z⟩
theorem not_tile'_501 (D : CongruentDissection 501) : False :=
  not_tile_of_conditions' 501 C'_501 D

private theorem c511_sqf   : LeafSqf 511   := by decide +kernel
private theorem c511_range : LeafRange 511  := by decide +kernel
private theorem c511_ell   : LeafEll 511    := by decide +kernel
private theorem c511_nsq   : NSqChkSq 511   := by decide +kernel
private theorem c511_har   : HArithChkSq 511 := by decide +kernel
private theorem c511_r     : LeafR 511      := by decide +kernel
private theorem c511_e'    : LeafE' 511     := by decide +kernel
private theorem c511_f1    : LeafF1 511     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c511_s2    : S2ChkSq 511    := by decide +kernel
private theorem c511_s3    : S3ChkSq 511    := by decide +kernel
private theorem c511_iso   : LeafIso 511    := by decide +kernel
private theorem c511_nof2  : NoF2ChkSq 511  := by decide +kernel
private theorem c511_nof3  : NoF3ChkSq 511  := by decide +kernel
private theorem c511_nof4z : NoF4zChkSq 511 := by decide +kernel
theorem C'_511 : C' 511 :=
  ⟨c511_sqf, c511_range, c511_ell, leafNSq_of_sq c511_nsq, leafHAr_of_sq c511_har,
   c511_r, c511_e', c511_f1, leafS2_of_sq c511_s2, leafS3_of_sq c511_s3,
   c511_iso, leafR8_of_sq c511_nof2 c511_nof3 c511_nof4z⟩
theorem not_tile'_511 (D : CongruentDissection 511) : False :=
  not_tile_of_conditions' 511 C'_511 D

private theorem c515_sqf   : LeafSqf 515   := by decide +kernel
private theorem c515_range : LeafRange 515  := by decide +kernel
private theorem c515_ell   : LeafEll 515    := by decide +kernel
private theorem c515_nsq   : NSqChkSq 515   := by decide +kernel
private theorem c515_har   : HArithChkSq 515 := by decide +kernel
private theorem c515_r     : LeafR 515      := by decide +kernel
private theorem c515_e'    : LeafE' 515     := by decide +kernel
private theorem c515_f1    : LeafF1 515     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c515_s2    : S2ChkSq 515    := by decide +kernel
private theorem c515_s3    : S3ChkSq 515    := by decide +kernel
private theorem c515_iso   : LeafIso 515    := by decide +kernel
private theorem c515_nof2  : NoF2ChkSq 515  := by decide +kernel
private theorem c515_nof3  : NoF3ChkSq 515  := by decide +kernel
private theorem c515_nof4z : NoF4zChkSq 515 := by decide +kernel
theorem C'_515 : C' 515 :=
  ⟨c515_sqf, c515_range, c515_ell, leafNSq_of_sq c515_nsq, leafHAr_of_sq c515_har,
   c515_r, c515_e', c515_f1, leafS2_of_sq c515_s2, leafS3_of_sq c515_s3,
   c515_iso, leafR8_of_sq c515_nof2 c515_nof3 c515_nof4z⟩
theorem not_tile'_515 (D : CongruentDissection 515) : False :=
  not_tile_of_conditions' 515 C'_515 D

private theorem c519_sqf   : LeafSqf 519   := by decide +kernel
private theorem c519_range : LeafRange 519  := by decide +kernel
private theorem c519_ell   : LeafEll 519    := by decide +kernel
private theorem c519_nsq   : NSqChkSq 519   := by decide +kernel
private theorem c519_har   : HArithChkSq 519 := by decide +kernel
private theorem c519_r     : LeafR 519      := by decide +kernel
private theorem c519_e'    : LeafE' 519     := by decide +kernel
private theorem c519_f1    : LeafF1 519     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c519_s2    : S2ChkSq 519    := by decide +kernel
private theorem c519_s3    : S3ChkSq 519    := by decide +kernel
private theorem c519_iso   : LeafIso 519    := by decide +kernel
private theorem c519_nof2  : NoF2ChkSq 519  := by decide +kernel
private theorem c519_nof3  : NoF3ChkSq 519  := by decide +kernel
private theorem c519_nof4z : NoF4zChkSq 519 := by decide +kernel
theorem C'_519 : C' 519 :=
  ⟨c519_sqf, c519_range, c519_ell, leafNSq_of_sq c519_nsq, leafHAr_of_sq c519_har,
   c519_r, c519_e', c519_f1, leafS2_of_sq c519_s2, leafS3_of_sq c519_s3,
   c519_iso, leafR8_of_sq c519_nof2 c519_nof3 c519_nof4z⟩
theorem not_tile'_519 (D : CongruentDissection 519) : False :=
  not_tile_of_conditions' 519 C'_519 D

private theorem c535_sqf   : LeafSqf 535   := by decide +kernel
private theorem c535_range : LeafRange 535  := by decide +kernel
private theorem c535_ell   : LeafEll 535    := by decide +kernel
private theorem c535_nsq   : NSqChkSq 535   := by decide +kernel
private theorem c535_har   : HArithChkSq 535 := by decide +kernel
private theorem c535_r     : LeafR 535      := by decide +kernel
private theorem c535_e'    : LeafE' 535     := by decide +kernel
private theorem c535_f1    : LeafF1 535     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c535_s2    : S2ChkSq 535    := by decide +kernel
private theorem c535_s3    : S3ChkSq 535    := by decide +kernel
private theorem c535_iso   : LeafIso 535    := by decide +kernel
private theorem c535_nof2  : NoF2ChkSq 535  := by decide +kernel
private theorem c535_nof3  : NoF3ChkSq 535  := by decide +kernel
private theorem c535_nof4z : NoF4zChkSq 535 := by decide +kernel
theorem C'_535 : C' 535 :=
  ⟨c535_sqf, c535_range, c535_ell, leafNSq_of_sq c535_nsq, leafHAr_of_sq c535_har,
   c535_r, c535_e', c535_f1, leafS2_of_sq c535_s2, leafS3_of_sq c535_s3,
   c535_iso, leafR8_of_sq c535_nof2 c535_nof3 c535_nof4z⟩
theorem not_tile'_535 (D : CongruentDissection 535) : False :=
  not_tile_of_conditions' 535 C'_535 D

private theorem c537_sqf   : LeafSqf 537   := by decide +kernel
private theorem c537_range : LeafRange 537  := by decide +kernel
private theorem c537_ell   : LeafEll 537    := by decide +kernel
private theorem c537_nsq   : NSqChkSq 537   := by decide +kernel
private theorem c537_har   : HArithChkSq 537 := by decide +kernel
private theorem c537_r     : LeafR 537      := by decide +kernel
private theorem c537_e'    : LeafE' 537     := by decide +kernel
private theorem c537_f1    : LeafF1 537     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c537_s2    : S2ChkSq 537    := by decide +kernel
private theorem c537_s3    : S3ChkSq 537    := by decide +kernel
private theorem c537_iso   : LeafIso 537    := by decide +kernel
private theorem c537_nof2  : NoF2ChkSq 537  := by decide +kernel
private theorem c537_nof3  : NoF3ChkSq 537  := by decide +kernel
private theorem c537_nof4z : NoF4zChkSq 537 := by decide +kernel
theorem C'_537 : C' 537 :=
  ⟨c537_sqf, c537_range, c537_ell, leafNSq_of_sq c537_nsq, leafHAr_of_sq c537_har,
   c537_r, c537_e', c537_f1, leafS2_of_sq c537_s2, leafS3_of_sq c537_s3,
   c537_iso, leafR8_of_sq c537_nof2 c537_nof3 c537_nof4z⟩
theorem not_tile'_537 (D : CongruentDissection 537) : False :=
  not_tile_of_conditions' 537 C'_537 D

end Erdos634.Draft.AllN2

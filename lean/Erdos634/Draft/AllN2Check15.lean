/- AllN2Check15: N = 357, 381, 393, 395, 399, 411, 415, 417, 447, 453
   Squarefree exclusions via C' with sqrt-bounded checks (Wave-2 OOM fix). -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c357_sqf   : LeafSqf 357   := by decide +kernel
private theorem c357_range : LeafRange 357  := by decide +kernel
private theorem c357_ell   : LeafEll 357    := by decide +kernel
private theorem c357_nsq   : NSqChkSq 357   := by decide +kernel
private theorem c357_har   : HArithChkSq 357 := by decide +kernel
private theorem c357_r     : LeafR 357      := by decide +kernel
private theorem c357_e'    : LeafE' 357     := by decide +kernel
private theorem c357_f1    : LeafF1 357     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c357_s2    : S2ChkSq 357    := by decide +kernel
private theorem c357_s3    : S3ChkSq 357    := by decide +kernel
private theorem c357_iso   : LeafIso 357    := by decide +kernel
private theorem c357_nof2  : NoF2ChkSq 357  := by decide +kernel
private theorem c357_nof3  : NoF3ChkSq 357  := by decide +kernel
private theorem c357_nof4z : NoF4zChkSq 357 := by decide +kernel
theorem C'_357 : C' 357 :=
  ⟨c357_sqf, c357_range, c357_ell, leafNSq_of_sq c357_nsq, leafHAr_of_sq c357_har,
   c357_r, c357_e', c357_f1, leafS2_of_sq c357_s2, leafS3_of_sq c357_s3,
   c357_iso, leafR8_of_sq c357_nof2 c357_nof3 c357_nof4z⟩
theorem not_tile'_357 (D : CongruentDissection 357) : False :=
  not_tile_of_conditions' 357 C'_357 D

private theorem c381_sqf   : LeafSqf 381   := by decide +kernel
private theorem c381_range : LeafRange 381  := by decide +kernel
private theorem c381_ell   : LeafEll 381    := by decide +kernel
private theorem c381_nsq   : NSqChkSq 381   := by decide +kernel
private theorem c381_har   : HArithChkSq 381 := by decide +kernel
private theorem c381_r     : LeafR 381      := by decide +kernel
private theorem c381_e'    : LeafE' 381     := by decide +kernel
private theorem c381_f1    : LeafF1 381     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c381_s2    : S2ChkSq 381    := by decide +kernel
private theorem c381_s3    : S3ChkSq 381    := by decide +kernel
private theorem c381_iso   : LeafIso 381    := by decide +kernel
private theorem c381_nof2  : NoF2ChkSq 381  := by decide +kernel
private theorem c381_nof3  : NoF3ChkSq 381  := by decide +kernel
private theorem c381_nof4z : NoF4zChkSq 381 := by decide +kernel
theorem C'_381 : C' 381 :=
  ⟨c381_sqf, c381_range, c381_ell, leafNSq_of_sq c381_nsq, leafHAr_of_sq c381_har,
   c381_r, c381_e', c381_f1, leafS2_of_sq c381_s2, leafS3_of_sq c381_s3,
   c381_iso, leafR8_of_sq c381_nof2 c381_nof3 c381_nof4z⟩
theorem not_tile'_381 (D : CongruentDissection 381) : False :=
  not_tile_of_conditions' 381 C'_381 D

private theorem c393_sqf   : LeafSqf 393   := by decide +kernel
private theorem c393_range : LeafRange 393  := by decide +kernel
private theorem c393_ell   : LeafEll 393    := by decide +kernel
private theorem c393_nsq   : NSqChkSq 393   := by decide +kernel
private theorem c393_har   : HArithChkSq 393 := by decide +kernel
private theorem c393_r     : LeafR 393      := by decide +kernel
private theorem c393_e'    : LeafE' 393     := by decide +kernel
private theorem c393_f1    : LeafF1 393     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c393_s2    : S2ChkSq 393    := by decide +kernel
private theorem c393_s3    : S3ChkSq 393    := by decide +kernel
private theorem c393_iso   : LeafIso 393    := by decide +kernel
private theorem c393_nof2  : NoF2ChkSq 393  := by decide +kernel
private theorem c393_nof3  : NoF3ChkSq 393  := by decide +kernel
private theorem c393_nof4z : NoF4zChkSq 393 := by decide +kernel
theorem C'_393 : C' 393 :=
  ⟨c393_sqf, c393_range, c393_ell, leafNSq_of_sq c393_nsq, leafHAr_of_sq c393_har,
   c393_r, c393_e', c393_f1, leafS2_of_sq c393_s2, leafS3_of_sq c393_s3,
   c393_iso, leafR8_of_sq c393_nof2 c393_nof3 c393_nof4z⟩
theorem not_tile'_393 (D : CongruentDissection 393) : False :=
  not_tile_of_conditions' 393 C'_393 D

private theorem c395_sqf   : LeafSqf 395   := by decide +kernel
private theorem c395_range : LeafRange 395  := by decide +kernel
private theorem c395_ell   : LeafEll 395    := by decide +kernel
private theorem c395_nsq   : NSqChkSq 395   := by decide +kernel
private theorem c395_har   : HArithChkSq 395 := by decide +kernel
private theorem c395_r     : LeafR 395      := by decide +kernel
private theorem c395_e'    : LeafE' 395     := by decide +kernel
private theorem c395_f1    : LeafF1 395     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c395_s2    : S2ChkSq 395    := by decide +kernel
private theorem c395_s3    : S3ChkSq 395    := by decide +kernel
private theorem c395_iso   : LeafIso 395    := by decide +kernel
private theorem c395_nof2  : NoF2ChkSq 395  := by decide +kernel
private theorem c395_nof3  : NoF3ChkSq 395  := by decide +kernel
private theorem c395_nof4z : NoF4zChkSq 395 := by decide +kernel
theorem C'_395 : C' 395 :=
  ⟨c395_sqf, c395_range, c395_ell, leafNSq_of_sq c395_nsq, leafHAr_of_sq c395_har,
   c395_r, c395_e', c395_f1, leafS2_of_sq c395_s2, leafS3_of_sq c395_s3,
   c395_iso, leafR8_of_sq c395_nof2 c395_nof3 c395_nof4z⟩
theorem not_tile'_395 (D : CongruentDissection 395) : False :=
  not_tile_of_conditions' 395 C'_395 D

private theorem c399_sqf   : LeafSqf 399   := by decide +kernel
private theorem c399_range : LeafRange 399  := by decide +kernel
private theorem c399_ell   : LeafEll 399    := by decide +kernel
private theorem c399_nsq   : NSqChkSq 399   := by decide +kernel
private theorem c399_har   : HArithChkSq 399 := by decide +kernel
private theorem c399_r     : LeafR 399      := by decide +kernel
private theorem c399_e'    : LeafE' 399     := by decide +kernel
private theorem c399_f1    : LeafF1 399     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c399_s2    : S2ChkSq 399    := by decide +kernel
private theorem c399_s3    : S3ChkSq 399    := by decide +kernel
private theorem c399_iso   : LeafIso 399    := by decide +kernel
private theorem c399_nof2  : NoF2ChkSq 399  := by decide +kernel
private theorem c399_nof3  : NoF3ChkSq 399  := by decide +kernel
private theorem c399_nof4z : NoF4zChkSq 399 := by decide +kernel
theorem C'_399 : C' 399 :=
  ⟨c399_sqf, c399_range, c399_ell, leafNSq_of_sq c399_nsq, leafHAr_of_sq c399_har,
   c399_r, c399_e', c399_f1, leafS2_of_sq c399_s2, leafS3_of_sq c399_s3,
   c399_iso, leafR8_of_sq c399_nof2 c399_nof3 c399_nof4z⟩
theorem not_tile'_399 (D : CongruentDissection 399) : False :=
  not_tile_of_conditions' 399 C'_399 D

private theorem c411_sqf   : LeafSqf 411   := by decide +kernel
private theorem c411_range : LeafRange 411  := by decide +kernel
private theorem c411_ell   : LeafEll 411    := by decide +kernel
private theorem c411_nsq   : NSqChkSq 411   := by decide +kernel
private theorem c411_har   : HArithChkSq 411 := by decide +kernel
private theorem c411_r     : LeafR 411      := by decide +kernel
private theorem c411_e'    : LeafE' 411     := by decide +kernel
private theorem c411_f1    : LeafF1 411     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c411_s2    : S2ChkSq 411    := by decide +kernel
private theorem c411_s3    : S3ChkSq 411    := by decide +kernel
private theorem c411_iso   : LeafIso 411    := by decide +kernel
private theorem c411_nof2  : NoF2ChkSq 411  := by decide +kernel
private theorem c411_nof3  : NoF3ChkSq 411  := by decide +kernel
private theorem c411_nof4z : NoF4zChkSq 411 := by decide +kernel
theorem C'_411 : C' 411 :=
  ⟨c411_sqf, c411_range, c411_ell, leafNSq_of_sq c411_nsq, leafHAr_of_sq c411_har,
   c411_r, c411_e', c411_f1, leafS2_of_sq c411_s2, leafS3_of_sq c411_s3,
   c411_iso, leafR8_of_sq c411_nof2 c411_nof3 c411_nof4z⟩
theorem not_tile'_411 (D : CongruentDissection 411) : False :=
  not_tile_of_conditions' 411 C'_411 D

private theorem c415_sqf   : LeafSqf 415   := by decide +kernel
private theorem c415_range : LeafRange 415  := by decide +kernel
private theorem c415_ell   : LeafEll 415    := by decide +kernel
private theorem c415_nsq   : NSqChkSq 415   := by decide +kernel
private theorem c415_har   : HArithChkSq 415 := by decide +kernel
private theorem c415_r     : LeafR 415      := by decide +kernel
private theorem c415_e'    : LeafE' 415     := by decide +kernel
private theorem c415_f1    : LeafF1 415     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c415_s2    : S2ChkSq 415    := by decide +kernel
private theorem c415_s3    : S3ChkSq 415    := by decide +kernel
private theorem c415_iso   : LeafIso 415    := by decide +kernel
private theorem c415_nof2  : NoF2ChkSq 415  := by decide +kernel
private theorem c415_nof3  : NoF3ChkSq 415  := by decide +kernel
private theorem c415_nof4z : NoF4zChkSq 415 := by decide +kernel
theorem C'_415 : C' 415 :=
  ⟨c415_sqf, c415_range, c415_ell, leafNSq_of_sq c415_nsq, leafHAr_of_sq c415_har,
   c415_r, c415_e', c415_f1, leafS2_of_sq c415_s2, leafS3_of_sq c415_s3,
   c415_iso, leafR8_of_sq c415_nof2 c415_nof3 c415_nof4z⟩
theorem not_tile'_415 (D : CongruentDissection 415) : False :=
  not_tile_of_conditions' 415 C'_415 D

private theorem c417_sqf   : LeafSqf 417   := by decide +kernel
private theorem c417_range : LeafRange 417  := by decide +kernel
private theorem c417_ell   : LeafEll 417    := by decide +kernel
private theorem c417_nsq   : NSqChkSq 417   := by decide +kernel
private theorem c417_har   : HArithChkSq 417 := by decide +kernel
private theorem c417_r     : LeafR 417      := by decide +kernel
private theorem c417_e'    : LeafE' 417     := by decide +kernel
private theorem c417_f1    : LeafF1 417     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c417_s2    : S2ChkSq 417    := by decide +kernel
private theorem c417_s3    : S3ChkSq 417    := by decide +kernel
private theorem c417_iso   : LeafIso 417    := by decide +kernel
private theorem c417_nof2  : NoF2ChkSq 417  := by decide +kernel
private theorem c417_nof3  : NoF3ChkSq 417  := by decide +kernel
private theorem c417_nof4z : NoF4zChkSq 417 := by decide +kernel
theorem C'_417 : C' 417 :=
  ⟨c417_sqf, c417_range, c417_ell, leafNSq_of_sq c417_nsq, leafHAr_of_sq c417_har,
   c417_r, c417_e', c417_f1, leafS2_of_sq c417_s2, leafS3_of_sq c417_s3,
   c417_iso, leafR8_of_sq c417_nof2 c417_nof3 c417_nof4z⟩
theorem not_tile'_417 (D : CongruentDissection 417) : False :=
  not_tile_of_conditions' 417 C'_417 D

private theorem c447_sqf   : LeafSqf 447   := by decide +kernel
private theorem c447_range : LeafRange 447  := by decide +kernel
private theorem c447_ell   : LeafEll 447    := by decide +kernel
private theorem c447_nsq   : NSqChkSq 447   := by decide +kernel
private theorem c447_har   : HArithChkSq 447 := by decide +kernel
private theorem c447_r     : LeafR 447      := by decide +kernel
private theorem c447_e'    : LeafE' 447     := by decide +kernel
private theorem c447_f1    : LeafF1 447     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c447_s2    : S2ChkSq 447    := by decide +kernel
private theorem c447_s3    : S3ChkSq 447    := by decide +kernel
private theorem c447_iso   : LeafIso 447    := by decide +kernel
private theorem c447_nof2  : NoF2ChkSq 447  := by decide +kernel
private theorem c447_nof3  : NoF3ChkSq 447  := by decide +kernel
private theorem c447_nof4z : NoF4zChkSq 447 := by decide +kernel
theorem C'_447 : C' 447 :=
  ⟨c447_sqf, c447_range, c447_ell, leafNSq_of_sq c447_nsq, leafHAr_of_sq c447_har,
   c447_r, c447_e', c447_f1, leafS2_of_sq c447_s2, leafS3_of_sq c447_s3,
   c447_iso, leafR8_of_sq c447_nof2 c447_nof3 c447_nof4z⟩
theorem not_tile'_447 (D : CongruentDissection 447) : False :=
  not_tile_of_conditions' 447 C'_447 D

private theorem c453_sqf   : LeafSqf 453   := by decide +kernel
private theorem c453_range : LeafRange 453  := by decide +kernel
private theorem c453_ell   : LeafEll 453    := by decide +kernel
private theorem c453_nsq   : NSqChkSq 453   := by decide +kernel
private theorem c453_har   : HArithChkSq 453 := by decide +kernel
private theorem c453_r     : LeafR 453      := by decide +kernel
private theorem c453_e'    : LeafE' 453     := by decide +kernel
private theorem c453_f1    : LeafF1 453     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c453_s2    : S2ChkSq 453    := by decide +kernel
private theorem c453_s3    : S3ChkSq 453    := by decide +kernel
private theorem c453_iso   : LeafIso 453    := by decide +kernel
private theorem c453_nof2  : NoF2ChkSq 453  := by decide +kernel
private theorem c453_nof3  : NoF3ChkSq 453  := by decide +kernel
private theorem c453_nof4z : NoF4zChkSq 453 := by decide +kernel
theorem C'_453 : C' 453 :=
  ⟨c453_sqf, c453_range, c453_ell, leafNSq_of_sq c453_nsq, leafHAr_of_sq c453_har,
   c453_r, c453_e', c453_f1, leafS2_of_sq c453_s2, leafS3_of_sq c453_s3,
   c453_iso, leafR8_of_sq c453_nof2 c453_nof3 c453_nof4z⟩
theorem not_tile'_453 (D : CongruentDissection 453) : False :=
  not_tile_of_conditions' 453 C'_453 D

end Erdos634.Draft.AllN2

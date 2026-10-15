/- AllN2Check152: N = 3278, 3279, 3282, 3286, 3287
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3278_sqf   : LeafSqf 3278   := by decide +kernel
private theorem c3278_range : LeafRange 3278  := by decide +kernel
private theorem c3278_ell   : LeafEll 3278    := by decide +kernel
private theorem c3278_nsq   : NSqChkSq 3278   := by decide +kernel
private theorem c3278_har   : HArithChkSq 3278 := by decide +kernel
private theorem c3278_r     : LeafR 3278      := by decide +kernel
private theorem c3278_e'    : LeafE' 3278     := by decide +kernel
private theorem c3278_f1    : LeafF1 3278     := Or.inl (by decide)
private theorem c3278_s2    : S2ChkSq 3278    := by decide +kernel
private theorem c3278_s3    : S3ChkSq 3278    := by decide +kernel
private theorem c3278_iso   : LeafIso 3278    := by decide +kernel
private theorem c3278_nof2  : NoF2ChkSq 3278  := by decide +kernel
private theorem c3278_nof3  : NoF3ChkSq 3278  := by decide +kernel
private theorem c3278_nof4z : NoF4zChkSq 3278 := by decide +kernel
theorem C'_3278 : C' 3278 :=
  ⟨c3278_sqf, c3278_range, c3278_ell, leafNSq_of_sq c3278_nsq, leafHAr_of_sq c3278_har,
   c3278_r, c3278_e', c3278_f1, leafS2_of_sq c3278_s2, leafS3_of_sq c3278_s3,
   c3278_iso, leafR8_of_sq c3278_nof2 c3278_nof3 c3278_nof4z⟩
theorem not_tile'_3278 (D : CongruentDissection 3278) : False :=
  not_tile_of_conditions' 3278 C'_3278 D

private theorem c3279_sqf   : LeafSqf 3279   := by decide +kernel
private theorem c3279_range : LeafRange 3279  := by decide +kernel
private theorem c3279_ell   : LeafEll 3279    := by decide +kernel
private theorem c3279_nsq   : NSqChkSq 3279   := by decide +kernel
private theorem c3279_har   : HArithChkSq 3279 := by decide +kernel
private theorem c3279_r     : LeafR 3279      := by decide +kernel
private theorem c3279_e'    : LeafE' 3279     := by decide +kernel
private theorem c3279_f1    : LeafF1 3279     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3279_s2    : S2ChkSq 3279    := by decide +kernel
private theorem c3279_s3    : S3ChkSq 3279    := by decide +kernel
private theorem c3279_iso   : LeafIso 3279    := by decide +kernel
private theorem c3279_nof2  : NoF2ChkSq 3279  := by decide +kernel
private theorem c3279_nof3  : NoF3ChkSq 3279  := by decide +kernel
private theorem c3279_nof4z : NoF4zChkSq 3279 := by decide +kernel
theorem C'_3279 : C' 3279 :=
  ⟨c3279_sqf, c3279_range, c3279_ell, leafNSq_of_sq c3279_nsq, leafHAr_of_sq c3279_har,
   c3279_r, c3279_e', c3279_f1, leafS2_of_sq c3279_s2, leafS3_of_sq c3279_s3,
   c3279_iso, leafR8_of_sq c3279_nof2 c3279_nof3 c3279_nof4z⟩
theorem not_tile'_3279 (D : CongruentDissection 3279) : False :=
  not_tile_of_conditions' 3279 C'_3279 D

private theorem c3282_sqf   : LeafSqf 3282   := by decide +kernel
private theorem c3282_range : LeafRange 3282  := by decide +kernel
private theorem c3282_ell   : LeafEll 3282    := by decide +kernel
private theorem c3282_nsq   : NSqChkSq 3282   := by decide +kernel
private theorem c3282_har   : HArithChkSq 3282 := by decide +kernel
private theorem c3282_r     : LeafR 3282      := by decide +kernel
private theorem c3282_e'    : LeafE' 3282     := by decide +kernel
private theorem c3282_f1    : LeafF1 3282     := Or.inl (by decide)
private theorem c3282_s2    : S2ChkSq 3282    := by decide +kernel
private theorem c3282_s3    : S3ChkSq 3282    := by decide +kernel
private theorem c3282_iso   : LeafIso 3282    := by decide +kernel
private theorem c3282_nof2  : NoF2ChkSq 3282  := by decide +kernel
private theorem c3282_nof3  : NoF3ChkSq 3282  := by decide +kernel
private theorem c3282_nof4z : NoF4zChkSq 3282 := by decide +kernel
theorem C'_3282 : C' 3282 :=
  ⟨c3282_sqf, c3282_range, c3282_ell, leafNSq_of_sq c3282_nsq, leafHAr_of_sq c3282_har,
   c3282_r, c3282_e', c3282_f1, leafS2_of_sq c3282_s2, leafS3_of_sq c3282_s3,
   c3282_iso, leafR8_of_sq c3282_nof2 c3282_nof3 c3282_nof4z⟩
theorem not_tile'_3282 (D : CongruentDissection 3282) : False :=
  not_tile_of_conditions' 3282 C'_3282 D

private theorem c3286_sqf   : LeafSqf 3286   := by decide +kernel
private theorem c3286_range : LeafRange 3286  := by decide +kernel
private theorem c3286_ell   : LeafEll 3286    := by decide +kernel
private theorem c3286_nsq   : NSqChkSq 3286   := by decide +kernel
private theorem c3286_har   : HArithChkSq 3286 := by decide +kernel
private theorem c3286_r     : LeafR 3286      := by decide +kernel
private theorem c3286_e'    : LeafE' 3286     := by decide +kernel
private theorem c3286_f1    : LeafF1 3286     := Or.inl (by decide)
private theorem c3286_s2    : S2ChkSq 3286    := by decide +kernel
private theorem c3286_s3    : S3ChkSq 3286    := by decide +kernel
private theorem c3286_iso   : LeafIso 3286    := by decide +kernel
private theorem c3286_nof2  : NoF2ChkSq 3286  := by decide +kernel
private theorem c3286_nof3  : NoF3ChkSq 3286  := by decide +kernel
private theorem c3286_nof4z : NoF4zChkSq 3286 := by decide +kernel
theorem C'_3286 : C' 3286 :=
  ⟨c3286_sqf, c3286_range, c3286_ell, leafNSq_of_sq c3286_nsq, leafHAr_of_sq c3286_har,
   c3286_r, c3286_e', c3286_f1, leafS2_of_sq c3286_s2, leafS3_of_sq c3286_s3,
   c3286_iso, leafR8_of_sq c3286_nof2 c3286_nof3 c3286_nof4z⟩
theorem not_tile'_3286 (D : CongruentDissection 3286) : False :=
  not_tile_of_conditions' 3286 C'_3286 D

private theorem c3287_sqf   : LeafSqf 3287   := by decide +kernel
private theorem c3287_range : LeafRange 3287  := by decide +kernel
private theorem c3287_ell   : LeafEll 3287    := by decide +kernel
private theorem c3287_nsq   : NSqChkSq 3287   := by decide +kernel
private theorem c3287_har   : HArithChkSq 3287 := by decide +kernel
private theorem c3287_r     : LeafR 3287      := by decide +kernel
private theorem c3287_e'    : LeafE' 3287     := by decide +kernel
private theorem c3287_f1    : LeafF1 3287     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3287_s2    : S2ChkSq 3287    := by decide +kernel
private theorem c3287_s3    : S3ChkSq 3287    := by decide +kernel
private theorem c3287_iso   : LeafIso 3287    := by decide +kernel
private theorem c3287_nof2  : NoF2ChkSq 3287  := by decide +kernel
private theorem c3287_nof3  : NoF3ChkSq 3287  := by decide +kernel
private theorem c3287_nof4z : NoF4zChkSq 3287 := by decide +kernel
theorem C'_3287 : C' 3287 :=
  ⟨c3287_sqf, c3287_range, c3287_ell, leafNSq_of_sq c3287_nsq, leafHAr_of_sq c3287_har,
   c3287_r, c3287_e', c3287_f1, leafS2_of_sq c3287_s2, leafS3_of_sq c3287_s3,
   c3287_iso, leafR8_of_sq c3287_nof2 c3287_nof3 c3287_nof4z⟩
theorem not_tile'_3287 (D : CongruentDissection 3287) : False :=
  not_tile_of_conditions' 3287 C'_3287 D

end Erdos634.Draft.AllN2

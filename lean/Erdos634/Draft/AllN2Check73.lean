/- AllN2Check73: N = 2274, 2278, 2279, 2282, 2283
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2274_sqf   : LeafSqf 2274   := by decide +kernel
private theorem c2274_range : LeafRange 2274  := by decide +kernel
private theorem c2274_ell   : LeafEll 2274    := by decide +kernel
private theorem c2274_nsq   : NSqChkSq 2274   := by decide +kernel
private theorem c2274_har   : HArithChkSq 2274 := by decide +kernel
private theorem c2274_r     : LeafR 2274      := by decide +kernel
private theorem c2274_e'    : LeafE' 2274     := by decide +kernel
private theorem c2274_f1    : LeafF1 2274     := Or.inl (by decide)
private theorem c2274_s2    : S2ChkSq 2274    := by decide +kernel
private theorem c2274_s3    : S3ChkSq 2274    := by decide +kernel
private theorem c2274_iso   : LeafIso 2274    := by decide +kernel
private theorem c2274_nof2  : NoF2ChkSq 2274  := by decide +kernel
private theorem c2274_nof3  : NoF3ChkSq 2274  := by decide +kernel
private theorem c2274_nof4z : NoF4zChkSq 2274 := by decide +kernel
theorem C'_2274 : C' 2274 :=
  ⟨c2274_sqf, c2274_range, c2274_ell, leafNSq_of_sq c2274_nsq, leafHAr_of_sq c2274_har,
   c2274_r, c2274_e', c2274_f1, leafS2_of_sq c2274_s2, leafS3_of_sq c2274_s3,
   c2274_iso, leafR8_of_sq c2274_nof2 c2274_nof3 c2274_nof4z⟩
theorem not_tile'_2274 (D : CongruentDissection 2274) : False :=
  not_tile_of_conditions' 2274 C'_2274 D

private theorem c2278_sqf   : LeafSqf 2278   := by decide +kernel
private theorem c2278_range : LeafRange 2278  := by decide +kernel
private theorem c2278_ell   : LeafEll 2278    := by decide +kernel
private theorem c2278_nsq   : NSqChkSq 2278   := by decide +kernel
private theorem c2278_har   : HArithChkSq 2278 := by decide +kernel
private theorem c2278_r     : LeafR 2278      := by decide +kernel
private theorem c2278_e'    : LeafE' 2278     := by decide +kernel
private theorem c2278_f1    : LeafF1 2278     := Or.inl (by decide)
private theorem c2278_s2    : S2ChkSq 2278    := by decide +kernel
private theorem c2278_s3    : S3ChkSq 2278    := by decide +kernel
private theorem c2278_iso   : LeafIso 2278    := by decide +kernel
private theorem c2278_nof2  : NoF2ChkSq 2278  := by decide +kernel
private theorem c2278_nof3  : NoF3ChkSq 2278  := by decide +kernel
private theorem c2278_nof4z : NoF4zChkSq 2278 := by decide +kernel
theorem C'_2278 : C' 2278 :=
  ⟨c2278_sqf, c2278_range, c2278_ell, leafNSq_of_sq c2278_nsq, leafHAr_of_sq c2278_har,
   c2278_r, c2278_e', c2278_f1, leafS2_of_sq c2278_s2, leafS3_of_sq c2278_s3,
   c2278_iso, leafR8_of_sq c2278_nof2 c2278_nof3 c2278_nof4z⟩
theorem not_tile'_2278 (D : CongruentDissection 2278) : False :=
  not_tile_of_conditions' 2278 C'_2278 D

private theorem c2279_sqf   : LeafSqf 2279   := by decide +kernel
private theorem c2279_range : LeafRange 2279  := by decide +kernel
private theorem c2279_ell   : LeafEll 2279    := by decide +kernel
private theorem c2279_nsq   : NSqChkSq 2279   := by decide +kernel
private theorem c2279_har   : HArithChkSq 2279 := by decide +kernel
private theorem c2279_r     : LeafR 2279      := by decide +kernel
private theorem c2279_e'    : LeafE' 2279     := by decide +kernel
private theorem c2279_f1    : LeafF1 2279     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2279_s2    : S2ChkSq 2279    := by decide +kernel
private theorem c2279_s3    : S3ChkSq 2279    := by decide +kernel
private theorem c2279_iso   : LeafIso 2279    := by decide +kernel
private theorem c2279_nof2  : NoF2ChkSq 2279  := by decide +kernel
private theorem c2279_nof3  : NoF3ChkSq 2279  := by decide +kernel
private theorem c2279_nof4z : NoF4zChkSq 2279 := by decide +kernel
theorem C'_2279 : C' 2279 :=
  ⟨c2279_sqf, c2279_range, c2279_ell, leafNSq_of_sq c2279_nsq, leafHAr_of_sq c2279_har,
   c2279_r, c2279_e', c2279_f1, leafS2_of_sq c2279_s2, leafS3_of_sq c2279_s3,
   c2279_iso, leafR8_of_sq c2279_nof2 c2279_nof3 c2279_nof4z⟩
theorem not_tile'_2279 (D : CongruentDissection 2279) : False :=
  not_tile_of_conditions' 2279 C'_2279 D

private theorem c2282_sqf   : LeafSqf 2282   := by decide +kernel
private theorem c2282_range : LeafRange 2282  := by decide +kernel
private theorem c2282_ell   : LeafEll 2282    := by decide +kernel
private theorem c2282_nsq   : NSqChkSq 2282   := by decide +kernel
private theorem c2282_har   : HArithChkSq 2282 := by decide +kernel
private theorem c2282_r     : LeafR 2282      := by decide +kernel
private theorem c2282_e'    : LeafE' 2282     := by decide +kernel
private theorem c2282_f1    : LeafF1 2282     := Or.inl (by decide)
private theorem c2282_s2    : S2ChkSq 2282    := by decide +kernel
private theorem c2282_s3    : S3ChkSq 2282    := by decide +kernel
private theorem c2282_iso   : LeafIso 2282    := by decide +kernel
private theorem c2282_nof2  : NoF2ChkSq 2282  := by decide +kernel
private theorem c2282_nof3  : NoF3ChkSq 2282  := by decide +kernel
private theorem c2282_nof4z : NoF4zChkSq 2282 := by decide +kernel
theorem C'_2282 : C' 2282 :=
  ⟨c2282_sqf, c2282_range, c2282_ell, leafNSq_of_sq c2282_nsq, leafHAr_of_sq c2282_har,
   c2282_r, c2282_e', c2282_f1, leafS2_of_sq c2282_s2, leafS3_of_sq c2282_s3,
   c2282_iso, leafR8_of_sq c2282_nof2 c2282_nof3 c2282_nof4z⟩
theorem not_tile'_2282 (D : CongruentDissection 2282) : False :=
  not_tile_of_conditions' 2282 C'_2282 D

private theorem c2283_sqf   : LeafSqf 2283   := by decide +kernel
private theorem c2283_range : LeafRange 2283  := by decide +kernel
private theorem c2283_ell   : LeafEll 2283    := by decide +kernel
private theorem c2283_nsq   : NSqChkSq 2283   := by decide +kernel
private theorem c2283_har   : HArithChkSq 2283 := by decide +kernel
private theorem c2283_r     : LeafR 2283      := by decide +kernel
private theorem c2283_e'    : LeafE' 2283     := by decide +kernel
private theorem c2283_f1    : LeafF1 2283     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2283_s2    : S2ChkSq 2283    := by decide +kernel
private theorem c2283_s3    : S3ChkSq 2283    := by decide +kernel
private theorem c2283_iso   : LeafIso 2283    := by decide +kernel
private theorem c2283_nof2  : NoF2ChkSq 2283  := by decide +kernel
private theorem c2283_nof3  : NoF3ChkSq 2283  := by decide +kernel
private theorem c2283_nof4z : NoF4zChkSq 2283 := by decide +kernel
theorem C'_2283 : C' 2283 :=
  ⟨c2283_sqf, c2283_range, c2283_ell, leafNSq_of_sq c2283_nsq, leafHAr_of_sq c2283_har,
   c2283_r, c2283_e', c2283_f1, leafS2_of_sq c2283_s2, leafS3_of_sq c2283_s3,
   c2283_iso, leafR8_of_sq c2283_nof2 c2283_nof3 c2283_nof4z⟩
theorem not_tile'_2283 (D : CongruentDissection 2283) : False :=
  not_tile_of_conditions' 2283 C'_2283 D

end Erdos634.Draft.AllN2

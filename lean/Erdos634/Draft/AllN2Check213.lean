/- AllN2Check213: N = 4081, 4083, 4085, 4087, 4091
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4081_sqf   : LeafSqf 4081   := by decide +kernel
private theorem c4081_range : LeafRange 4081  := by decide +kernel
private theorem c4081_ell   : LeafEll 4081    := by decide +kernel
private theorem c4081_nsq   : NSqChkSq 4081   := by decide +kernel
private theorem c4081_har   : HArithChkSq 4081 := by decide +kernel
private theorem c4081_r     : LeafR 4081      := by decide +kernel
private theorem c4081_e'    : LeafE' 4081     := by decide +kernel
private theorem c4081_f1    : LeafF1 4081     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4081_s2    : S2ChkSq 4081    := by decide +kernel
private theorem c4081_s3    : S3ChkSq 4081    := by decide +kernel
private theorem c4081_iso   : LeafIso 4081    := by decide +kernel
private theorem c4081_nof2  : NoF2ChkSq 4081  := by decide +kernel
private theorem c4081_nof3  : NoF3ChkSq 4081  := by decide +kernel
private theorem c4081_nof4z : NoF4zChkSq 4081 := by decide +kernel
theorem C'_4081 : C' 4081 :=
  ⟨c4081_sqf, c4081_range, c4081_ell, leafNSq_of_sq c4081_nsq, leafHAr_of_sq c4081_har,
   c4081_r, c4081_e', c4081_f1, leafS2_of_sq c4081_s2, leafS3_of_sq c4081_s3,
   c4081_iso, leafR8_of_sq c4081_nof2 c4081_nof3 c4081_nof4z⟩
theorem not_tile'_4081 (D : CongruentDissection 4081) : False :=
  not_tile_of_conditions' 4081 C'_4081 D

private theorem c4083_sqf   : LeafSqf 4083   := by decide +kernel
private theorem c4083_range : LeafRange 4083  := by decide +kernel
private theorem c4083_ell   : LeafEll 4083    := by decide +kernel
private theorem c4083_nsq   : NSqChkSq 4083   := by decide +kernel
private theorem c4083_har   : HArithChkSq 4083 := by decide +kernel
private theorem c4083_r     : LeafR 4083      := by decide +kernel
private theorem c4083_e'    : LeafE' 4083     := by decide +kernel
private theorem c4083_f1    : LeafF1 4083     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4083_s2    : S2ChkSq 4083    := by decide +kernel
private theorem c4083_s3    : S3ChkSq 4083    := by decide +kernel
private theorem c4083_iso   : LeafIso 4083    := by decide +kernel
private theorem c4083_nof2  : NoF2ChkSq 4083  := by decide +kernel
private theorem c4083_nof3  : NoF3ChkSq 4083  := by decide +kernel
private theorem c4083_nof4z : NoF4zChkSq 4083 := by decide +kernel
theorem C'_4083 : C' 4083 :=
  ⟨c4083_sqf, c4083_range, c4083_ell, leafNSq_of_sq c4083_nsq, leafHAr_of_sq c4083_har,
   c4083_r, c4083_e', c4083_f1, leafS2_of_sq c4083_s2, leafS3_of_sq c4083_s3,
   c4083_iso, leafR8_of_sq c4083_nof2 c4083_nof3 c4083_nof4z⟩
theorem not_tile'_4083 (D : CongruentDissection 4083) : False :=
  not_tile_of_conditions' 4083 C'_4083 D

private theorem c4085_sqf   : LeafSqf 4085   := by decide +kernel
private theorem c4085_range : LeafRange 4085  := by decide +kernel
private theorem c4085_ell   : LeafEll 4085    := by decide +kernel
private theorem c4085_nsq   : NSqChkSq 4085   := by decide +kernel
private theorem c4085_har   : HArithChkSq 4085 := by decide +kernel
private theorem c4085_r     : LeafR 4085      := by decide +kernel
private theorem c4085_e'    : LeafE' 4085     := by decide +kernel
private theorem c4085_f1    : LeafF1 4085     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4085_s2    : S2ChkSq 4085    := by decide +kernel
private theorem c4085_s3    : S3ChkSq 4085    := by decide +kernel
private theorem c4085_iso   : LeafIso 4085    := by decide +kernel
private theorem c4085_nof2  : NoF2ChkSq 4085  := by decide +kernel
private theorem c4085_nof3  : NoF3ChkSq 4085  := by decide +kernel
private theorem c4085_nof4z : NoF4zChkSq 4085 := by decide +kernel
theorem C'_4085 : C' 4085 :=
  ⟨c4085_sqf, c4085_range, c4085_ell, leafNSq_of_sq c4085_nsq, leafHAr_of_sq c4085_har,
   c4085_r, c4085_e', c4085_f1, leafS2_of_sq c4085_s2, leafS3_of_sq c4085_s3,
   c4085_iso, leafR8_of_sq c4085_nof2 c4085_nof3 c4085_nof4z⟩
theorem not_tile'_4085 (D : CongruentDissection 4085) : False :=
  not_tile_of_conditions' 4085 C'_4085 D

private theorem c4087_sqf   : LeafSqf 4087   := by decide +kernel
private theorem c4087_range : LeafRange 4087  := by decide +kernel
private theorem c4087_ell   : LeafEll 4087    := by decide +kernel
private theorem c4087_nsq   : NSqChkSq 4087   := by decide +kernel
private theorem c4087_har   : HArithChkSq 4087 := by decide +kernel
private theorem c4087_r     : LeafR 4087      := by decide +kernel
private theorem c4087_e'    : LeafE' 4087     := by decide +kernel
private theorem c4087_f1    : LeafF1 4087     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4087_s2    : S2ChkSq 4087    := by decide +kernel
private theorem c4087_s3    : S3ChkSq 4087    := by decide +kernel
private theorem c4087_iso   : LeafIso 4087    := by decide +kernel
private theorem c4087_nof2  : NoF2ChkSq 4087  := by decide +kernel
private theorem c4087_nof3  : NoF3ChkSq 4087  := by decide +kernel
private theorem c4087_nof4z : NoF4zChkSq 4087 := by decide +kernel
theorem C'_4087 : C' 4087 :=
  ⟨c4087_sqf, c4087_range, c4087_ell, leafNSq_of_sq c4087_nsq, leafHAr_of_sq c4087_har,
   c4087_r, c4087_e', c4087_f1, leafS2_of_sq c4087_s2, leafS3_of_sq c4087_s3,
   c4087_iso, leafR8_of_sq c4087_nof2 c4087_nof3 c4087_nof4z⟩
theorem not_tile'_4087 (D : CongruentDissection 4087) : False :=
  not_tile_of_conditions' 4087 C'_4087 D

private theorem c4091_sqf   : LeafSqf 4091   := by decide +kernel
private theorem c4091_range : LeafRange 4091  := by decide +kernel
private theorem c4091_ell   : LeafEll 4091    := by decide +kernel
private theorem c4091_nsq   : NSqChkSq 4091   := by decide +kernel
private theorem c4091_har   : HArithChkSq 4091 := by decide +kernel
private theorem c4091_r     : LeafR 4091      := by decide +kernel
private theorem c4091_e'    : LeafE' 4091     := by decide +kernel
private theorem c4091_f1    : LeafF1 4091     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4091_s2    : S2ChkSq 4091    := by decide +kernel
private theorem c4091_s3    : S3ChkSq 4091    := by decide +kernel
private theorem c4091_iso   : LeafIso 4091    := by decide +kernel
private theorem c4091_nof2  : NoF2ChkSq 4091  := by decide +kernel
private theorem c4091_nof3  : NoF3ChkSq 4091  := by decide +kernel
private theorem c4091_nof4z : NoF4zChkSq 4091 := by decide +kernel
theorem C'_4091 : C' 4091 :=
  ⟨c4091_sqf, c4091_range, c4091_ell, leafNSq_of_sq c4091_nsq, leafHAr_of_sq c4091_har,
   c4091_r, c4091_e', c4091_f1, leafS2_of_sq c4091_s2, leafS3_of_sq c4091_s3,
   c4091_iso, leafR8_of_sq c4091_nof2 c4091_nof3 c4091_nof4z⟩
theorem not_tile'_4091 (D : CongruentDissection 4091) : False :=
  not_tile_of_conditions' 4091 C'_4091 D

end Erdos634.Draft.AllN2

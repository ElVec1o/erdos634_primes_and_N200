/- AllN2Check290: N = 5026, 5027, 5029, 5030, 5033
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c5026_sqf   : LeafSqf 5026   := by decide +kernel
private theorem c5026_range : LeafRange 5026  := by decide +kernel
private theorem c5026_ell   : LeafEll 5026    := by decide +kernel
private theorem c5026_nsq   : NSqChkSq 5026   := by decide +kernel
private theorem c5026_har   : HArithChkSq 5026 := by decide +kernel
private theorem c5026_r     : LeafR 5026      := by decide +kernel
private theorem c5026_e'    : LeafE' 5026     := by decide +kernel
private theorem c5026_f1    : LeafF1 5026     := Or.inl (by decide)
private theorem c5026_s2    : S2ChkSq 5026    := by decide +kernel
private theorem c5026_s3    : S3ChkSq 5026    := by decide +kernel
private theorem c5026_iso   : LeafIso 5026    := by decide +kernel
private theorem c5026_nof2  : NoF2ChkSq 5026  := by decide +kernel
private theorem c5026_nof3  : NoF3ChkSq 5026  := by decide +kernel
private theorem c5026_nof4z : NoF4zChkSq 5026 := by decide +kernel
theorem C'_5026 : C' 5026 :=
  ⟨c5026_sqf, c5026_range, c5026_ell, leafNSq_of_sq c5026_nsq, leafHAr_of_sq c5026_har,
   c5026_r, c5026_e', c5026_f1, leafS2_of_sq c5026_s2, leafS3_of_sq c5026_s3,
   c5026_iso, leafR8_of_sq c5026_nof2 c5026_nof3 c5026_nof4z⟩
theorem not_tile'_5026 (D : CongruentDissection 5026) : False :=
  not_tile_of_conditions' 5026 C'_5026 D

private theorem c5027_sqf   : LeafSqf 5027   := by decide +kernel
private theorem c5027_range : LeafRange 5027  := by decide +kernel
private theorem c5027_ell   : LeafEll 5027    := by decide +kernel
private theorem c5027_nsq   : NSqChkSq 5027   := by decide +kernel
private theorem c5027_har   : HArithChkSq 5027 := by decide +kernel
private theorem c5027_r     : LeafR 5027      := by decide +kernel
private theorem c5027_e'    : LeafE' 5027     := by decide +kernel
private theorem c5027_f1    : LeafF1 5027     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c5027_s2    : S2ChkSq 5027    := by decide +kernel
private theorem c5027_s3    : S3ChkSq 5027    := by decide +kernel
private theorem c5027_iso   : LeafIso 5027    := by decide +kernel
private theorem c5027_nof2  : NoF2ChkSq 5027  := by decide +kernel
private theorem c5027_nof3  : NoF3ChkSq 5027  := by decide +kernel
private theorem c5027_nof4z : NoF4zChkSq 5027 := by decide +kernel
theorem C'_5027 : C' 5027 :=
  ⟨c5027_sqf, c5027_range, c5027_ell, leafNSq_of_sq c5027_nsq, leafHAr_of_sq c5027_har,
   c5027_r, c5027_e', c5027_f1, leafS2_of_sq c5027_s2, leafS3_of_sq c5027_s3,
   c5027_iso, leafR8_of_sq c5027_nof2 c5027_nof3 c5027_nof4z⟩
theorem not_tile'_5027 (D : CongruentDissection 5027) : False :=
  not_tile_of_conditions' 5027 C'_5027 D

private theorem c5029_sqf   : LeafSqf 5029   := by decide +kernel
private theorem c5029_range : LeafRange 5029  := by decide +kernel
private theorem c5029_ell   : LeafEll 5029    := by decide +kernel
private theorem c5029_nsq   : NSqChkSq 5029   := by decide +kernel
private theorem c5029_har   : HArithChkSq 5029 := by decide +kernel
private theorem c5029_r     : LeafR 5029      := by decide +kernel
private theorem c5029_e'    : LeafE' 5029     := by decide +kernel
private theorem c5029_f1    : LeafF1 5029     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c5029_s2    : S2ChkSq 5029    := by decide +kernel
private theorem c5029_s3    : S3ChkSq 5029    := by decide +kernel
private theorem c5029_iso   : LeafIso 5029    := by decide +kernel
private theorem c5029_nof2  : NoF2ChkSq 5029  := by decide +kernel
private theorem c5029_nof3  : NoF3ChkSq 5029  := by decide +kernel
private theorem c5029_nof4z : NoF4zChkSq 5029 := by decide +kernel
theorem C'_5029 : C' 5029 :=
  ⟨c5029_sqf, c5029_range, c5029_ell, leafNSq_of_sq c5029_nsq, leafHAr_of_sq c5029_har,
   c5029_r, c5029_e', c5029_f1, leafS2_of_sq c5029_s2, leafS3_of_sq c5029_s3,
   c5029_iso, leafR8_of_sq c5029_nof2 c5029_nof3 c5029_nof4z⟩
theorem not_tile'_5029 (D : CongruentDissection 5029) : False :=
  not_tile_of_conditions' 5029 C'_5029 D

private theorem c5030_sqf   : LeafSqf 5030   := by decide +kernel
private theorem c5030_range : LeafRange 5030  := by decide +kernel
private theorem c5030_ell   : LeafEll 5030    := by decide +kernel
private theorem c5030_nsq   : NSqChkSq 5030   := by decide +kernel
private theorem c5030_har   : HArithChkSq 5030 := by decide +kernel
private theorem c5030_r     : LeafR 5030      := by decide +kernel
private theorem c5030_e'    : LeafE' 5030     := by decide +kernel
private theorem c5030_f1    : LeafF1 5030     := Or.inl (by decide)
private theorem c5030_s2    : S2ChkSq 5030    := by decide +kernel
private theorem c5030_s3    : S3ChkSq 5030    := by decide +kernel
private theorem c5030_iso   : LeafIso 5030    := by decide +kernel
private theorem c5030_nof2  : NoF2ChkSq 5030  := by decide +kernel
private theorem c5030_nof3  : NoF3ChkSq 5030  := by decide +kernel
private theorem c5030_nof4z : NoF4zChkSq 5030 := by decide +kernel
theorem C'_5030 : C' 5030 :=
  ⟨c5030_sqf, c5030_range, c5030_ell, leafNSq_of_sq c5030_nsq, leafHAr_of_sq c5030_har,
   c5030_r, c5030_e', c5030_f1, leafS2_of_sq c5030_s2, leafS3_of_sq c5030_s3,
   c5030_iso, leafR8_of_sq c5030_nof2 c5030_nof3 c5030_nof4z⟩
theorem not_tile'_5030 (D : CongruentDissection 5030) : False :=
  not_tile_of_conditions' 5030 C'_5030 D

private theorem c5033_sqf   : LeafSqf 5033   := by decide +kernel
private theorem c5033_range : LeafRange 5033  := by decide +kernel
private theorem c5033_ell   : LeafEll 5033    := by decide +kernel
private theorem c5033_nsq   : NSqChkSq 5033   := by decide +kernel
private theorem c5033_har   : HArithChkSq 5033 := by decide +kernel
private theorem c5033_r     : LeafR 5033      := by decide +kernel
private theorem c5033_e'    : LeafE' 5033     := by decide +kernel
private theorem c5033_f1    : LeafF1 5033     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c5033_s2    : S2ChkSq 5033    := by decide +kernel
private theorem c5033_s3    : S3ChkSq 5033    := by decide +kernel
private theorem c5033_iso   : LeafIso 5033    := by decide +kernel
private theorem c5033_nof2  : NoF2ChkSq 5033  := by decide +kernel
private theorem c5033_nof3  : NoF3ChkSq 5033  := by decide +kernel
private theorem c5033_nof4z : NoF4zChkSq 5033 := by decide +kernel
theorem C'_5033 : C' 5033 :=
  ⟨c5033_sqf, c5033_range, c5033_ell, leafNSq_of_sq c5033_nsq, leafHAr_of_sq c5033_har,
   c5033_r, c5033_e', c5033_f1, leafS2_of_sq c5033_s2, leafS3_of_sq c5033_s3,
   c5033_iso, leafR8_of_sq c5033_nof2 c5033_nof3 c5033_nof4z⟩
theorem not_tile'_5033 (D : CongruentDissection 5033) : False :=
  not_tile_of_conditions' 5033 C'_5033 D

end Erdos634.Draft.AllN2

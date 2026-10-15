/- AllN2Check54: N = 2027, 2030, 2031, 2033, 2035
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2027_sqf   : LeafSqf 2027   := by decide +kernel
private theorem c2027_range : LeafRange 2027  := by decide +kernel
private theorem c2027_ell   : LeafEll 2027    := by decide +kernel
private theorem c2027_nsq   : NSqChkSq 2027   := by decide +kernel
private theorem c2027_har   : HArithChkSq 2027 := by decide +kernel
private theorem c2027_r     : LeafR 2027      := by decide +kernel
private theorem c2027_e'    : LeafE' 2027     := by decide +kernel
private theorem c2027_f1    : LeafF1 2027     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2027_s2    : S2ChkSq 2027    := by decide +kernel
private theorem c2027_s3    : S3ChkSq 2027    := by decide +kernel
private theorem c2027_iso   : LeafIso 2027    := by decide +kernel
private theorem c2027_nof2  : NoF2ChkSq 2027  := by decide +kernel
private theorem c2027_nof3  : NoF3ChkSq 2027  := by decide +kernel
private theorem c2027_nof4z : NoF4zChkSq 2027 := by decide +kernel
theorem C'_2027 : C' 2027 :=
  ⟨c2027_sqf, c2027_range, c2027_ell, leafNSq_of_sq c2027_nsq, leafHAr_of_sq c2027_har,
   c2027_r, c2027_e', c2027_f1, leafS2_of_sq c2027_s2, leafS3_of_sq c2027_s3,
   c2027_iso, leafR8_of_sq c2027_nof2 c2027_nof3 c2027_nof4z⟩
theorem not_tile'_2027 (D : CongruentDissection 2027) : False :=
  not_tile_of_conditions' 2027 C'_2027 D

private theorem c2030_sqf   : LeafSqf 2030   := by decide +kernel
private theorem c2030_range : LeafRange 2030  := by decide +kernel
private theorem c2030_ell   : LeafEll 2030    := by decide +kernel
private theorem c2030_nsq   : NSqChkSq 2030   := by decide +kernel
private theorem c2030_har   : HArithChkSq 2030 := by decide +kernel
private theorem c2030_r     : LeafR 2030      := by decide +kernel
private theorem c2030_e'    : LeafE' 2030     := by decide +kernel
private theorem c2030_f1    : LeafF1 2030     := Or.inl (by decide)
private theorem c2030_s2    : S2ChkSq 2030    := by decide +kernel
private theorem c2030_s3    : S3ChkSq 2030    := by decide +kernel
private theorem c2030_iso   : LeafIso 2030    := by decide +kernel
private theorem c2030_nof2  : NoF2ChkSq 2030  := by decide +kernel
private theorem c2030_nof3  : NoF3ChkSq 2030  := by decide +kernel
private theorem c2030_nof4z : NoF4zChkSq 2030 := by decide +kernel
theorem C'_2030 : C' 2030 :=
  ⟨c2030_sqf, c2030_range, c2030_ell, leafNSq_of_sq c2030_nsq, leafHAr_of_sq c2030_har,
   c2030_r, c2030_e', c2030_f1, leafS2_of_sq c2030_s2, leafS3_of_sq c2030_s3,
   c2030_iso, leafR8_of_sq c2030_nof2 c2030_nof3 c2030_nof4z⟩
theorem not_tile'_2030 (D : CongruentDissection 2030) : False :=
  not_tile_of_conditions' 2030 C'_2030 D

private theorem c2031_sqf   : LeafSqf 2031   := by decide +kernel
private theorem c2031_range : LeafRange 2031  := by decide +kernel
private theorem c2031_ell   : LeafEll 2031    := by decide +kernel
private theorem c2031_nsq   : NSqChkSq 2031   := by decide +kernel
private theorem c2031_har   : HArithChkSq 2031 := by decide +kernel
private theorem c2031_r     : LeafR 2031      := by decide +kernel
private theorem c2031_e'    : LeafE' 2031     := by decide +kernel
private theorem c2031_f1    : LeafF1 2031     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2031_s2    : S2ChkSq 2031    := by decide +kernel
private theorem c2031_s3    : S3ChkSq 2031    := by decide +kernel
private theorem c2031_iso   : LeafIso 2031    := by decide +kernel
private theorem c2031_nof2  : NoF2ChkSq 2031  := by decide +kernel
private theorem c2031_nof3  : NoF3ChkSq 2031  := by decide +kernel
private theorem c2031_nof4z : NoF4zChkSq 2031 := by decide +kernel
theorem C'_2031 : C' 2031 :=
  ⟨c2031_sqf, c2031_range, c2031_ell, leafNSq_of_sq c2031_nsq, leafHAr_of_sq c2031_har,
   c2031_r, c2031_e', c2031_f1, leafS2_of_sq c2031_s2, leafS3_of_sq c2031_s3,
   c2031_iso, leafR8_of_sq c2031_nof2 c2031_nof3 c2031_nof4z⟩
theorem not_tile'_2031 (D : CongruentDissection 2031) : False :=
  not_tile_of_conditions' 2031 C'_2031 D

private theorem c2033_sqf   : LeafSqf 2033   := by decide +kernel
private theorem c2033_range : LeafRange 2033  := by decide +kernel
private theorem c2033_ell   : LeafEll 2033    := by decide +kernel
private theorem c2033_nsq   : NSqChkSq 2033   := by decide +kernel
private theorem c2033_har   : HArithChkSq 2033 := by decide +kernel
private theorem c2033_r     : LeafR 2033      := by decide +kernel
private theorem c2033_e'    : LeafE' 2033     := by decide +kernel
private theorem c2033_f1    : LeafF1 2033     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2033_s2    : S2ChkSq 2033    := by decide +kernel
private theorem c2033_s3    : S3ChkSq 2033    := by decide +kernel
private theorem c2033_iso   : LeafIso 2033    := by decide +kernel
private theorem c2033_nof2  : NoF2ChkSq 2033  := by decide +kernel
private theorem c2033_nof3  : NoF3ChkSq 2033  := by decide +kernel
private theorem c2033_nof4z : NoF4zChkSq 2033 := by decide +kernel
theorem C'_2033 : C' 2033 :=
  ⟨c2033_sqf, c2033_range, c2033_ell, leafNSq_of_sq c2033_nsq, leafHAr_of_sq c2033_har,
   c2033_r, c2033_e', c2033_f1, leafS2_of_sq c2033_s2, leafS3_of_sq c2033_s3,
   c2033_iso, leafR8_of_sq c2033_nof2 c2033_nof3 c2033_nof4z⟩
theorem not_tile'_2033 (D : CongruentDissection 2033) : False :=
  not_tile_of_conditions' 2033 C'_2033 D

private theorem c2035_sqf   : LeafSqf 2035   := by decide +kernel
private theorem c2035_range : LeafRange 2035  := by decide +kernel
private theorem c2035_ell   : LeafEll 2035    := by decide +kernel
private theorem c2035_nsq   : NSqChkSq 2035   := by decide +kernel
private theorem c2035_har   : HArithChkSq 2035 := by decide +kernel
private theorem c2035_r     : LeafR 2035      := by decide +kernel
private theorem c2035_e'    : LeafE' 2035     := by decide +kernel
private theorem c2035_f1    : LeafF1 2035     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2035_s2    : S2ChkSq 2035    := by decide +kernel
private theorem c2035_s3    : S3ChkSq 2035    := by decide +kernel
private theorem c2035_iso   : LeafIso 2035    := by decide +kernel
private theorem c2035_nof2  : NoF2ChkSq 2035  := by decide +kernel
private theorem c2035_nof3  : NoF3ChkSq 2035  := by decide +kernel
private theorem c2035_nof4z : NoF4zChkSq 2035 := by decide +kernel
theorem C'_2035 : C' 2035 :=
  ⟨c2035_sqf, c2035_range, c2035_ell, leafNSq_of_sq c2035_nsq, leafHAr_of_sq c2035_har,
   c2035_r, c2035_e', c2035_f1, leafS2_of_sq c2035_s2, leafS3_of_sq c2035_s3,
   c2035_iso, leafR8_of_sq c2035_nof2 c2035_nof3 c2035_nof4z⟩
theorem not_tile'_2035 (D : CongruentDissection 2035) : False :=
  not_tile_of_conditions' 2035 C'_2035 D

end Erdos634.Draft.AllN2

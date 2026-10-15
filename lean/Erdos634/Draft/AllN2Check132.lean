/- AllN2Check132: N = 3022, 3023, 3027, 3030, 3031
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3022_sqf   : LeafSqf 3022   := by decide +kernel
private theorem c3022_range : LeafRange 3022  := by decide +kernel
private theorem c3022_ell   : LeafEll 3022    := by decide +kernel
private theorem c3022_nsq   : NSqChkSq 3022   := by decide +kernel
private theorem c3022_har   : HArithChkSq 3022 := by decide +kernel
private theorem c3022_r     : LeafR 3022      := by decide +kernel
private theorem c3022_e'    : LeafE' 3022     := by decide +kernel
private theorem c3022_f1    : LeafF1 3022     := Or.inl (by decide)
private theorem c3022_s2    : S2ChkSq 3022    := by decide +kernel
private theorem c3022_s3    : S3ChkSq 3022    := by decide +kernel
private theorem c3022_iso   : LeafIso 3022    := by decide +kernel
private theorem c3022_nof2  : NoF2ChkSq 3022  := by decide +kernel
private theorem c3022_nof3  : NoF3ChkSq 3022  := by decide +kernel
private theorem c3022_nof4z : NoF4zChkSq 3022 := by decide +kernel
theorem C'_3022 : C' 3022 :=
  ⟨c3022_sqf, c3022_range, c3022_ell, leafNSq_of_sq c3022_nsq, leafHAr_of_sq c3022_har,
   c3022_r, c3022_e', c3022_f1, leafS2_of_sq c3022_s2, leafS3_of_sq c3022_s3,
   c3022_iso, leafR8_of_sq c3022_nof2 c3022_nof3 c3022_nof4z⟩
theorem not_tile'_3022 (D : CongruentDissection 3022) : False :=
  not_tile_of_conditions' 3022 C'_3022 D

private theorem c3023_sqf   : LeafSqf 3023   := by decide +kernel
private theorem c3023_range : LeafRange 3023  := by decide +kernel
private theorem c3023_ell   : LeafEll 3023    := by decide +kernel
private theorem c3023_nsq   : NSqChkSq 3023   := by decide +kernel
private theorem c3023_har   : HArithChkSq 3023 := by decide +kernel
private theorem c3023_r     : LeafR 3023      := by decide +kernel
private theorem c3023_e'    : LeafE' 3023     := by decide +kernel
private theorem c3023_f1    : LeafF1 3023     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3023_s2    : S2ChkSq 3023    := by decide +kernel
private theorem c3023_s3    : S3ChkSq 3023    := by decide +kernel
private theorem c3023_iso   : LeafIso 3023    := by decide +kernel
private theorem c3023_nof2  : NoF2ChkSq 3023  := by decide +kernel
private theorem c3023_nof3  : NoF3ChkSq 3023  := by decide +kernel
private theorem c3023_nof4z : NoF4zChkSq 3023 := by decide +kernel
theorem C'_3023 : C' 3023 :=
  ⟨c3023_sqf, c3023_range, c3023_ell, leafNSq_of_sq c3023_nsq, leafHAr_of_sq c3023_har,
   c3023_r, c3023_e', c3023_f1, leafS2_of_sq c3023_s2, leafS3_of_sq c3023_s3,
   c3023_iso, leafR8_of_sq c3023_nof2 c3023_nof3 c3023_nof4z⟩
theorem not_tile'_3023 (D : CongruentDissection 3023) : False :=
  not_tile_of_conditions' 3023 C'_3023 D

private theorem c3027_sqf   : LeafSqf 3027   := by decide +kernel
private theorem c3027_range : LeafRange 3027  := by decide +kernel
private theorem c3027_ell   : LeafEll 3027    := by decide +kernel
private theorem c3027_nsq   : NSqChkSq 3027   := by decide +kernel
private theorem c3027_har   : HArithChkSq 3027 := by decide +kernel
private theorem c3027_r     : LeafR 3027      := by decide +kernel
private theorem c3027_e'    : LeafE' 3027     := by decide +kernel
private theorem c3027_f1    : LeafF1 3027     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3027_s2    : S2ChkSq 3027    := by decide +kernel
private theorem c3027_s3    : S3ChkSq 3027    := by decide +kernel
private theorem c3027_iso   : LeafIso 3027    := by decide +kernel
private theorem c3027_nof2  : NoF2ChkSq 3027  := by decide +kernel
private theorem c3027_nof3  : NoF3ChkSq 3027  := by decide +kernel
private theorem c3027_nof4z : NoF4zChkSq 3027 := by decide +kernel
theorem C'_3027 : C' 3027 :=
  ⟨c3027_sqf, c3027_range, c3027_ell, leafNSq_of_sq c3027_nsq, leafHAr_of_sq c3027_har,
   c3027_r, c3027_e', c3027_f1, leafS2_of_sq c3027_s2, leafS3_of_sq c3027_s3,
   c3027_iso, leafR8_of_sq c3027_nof2 c3027_nof3 c3027_nof4z⟩
theorem not_tile'_3027 (D : CongruentDissection 3027) : False :=
  not_tile_of_conditions' 3027 C'_3027 D

private theorem c3030_sqf   : LeafSqf 3030   := by decide +kernel
private theorem c3030_range : LeafRange 3030  := by decide +kernel
private theorem c3030_ell   : LeafEll 3030    := by decide +kernel
private theorem c3030_nsq   : NSqChkSq 3030   := by decide +kernel
private theorem c3030_har   : HArithChkSq 3030 := by decide +kernel
private theorem c3030_r     : LeafR 3030      := by decide +kernel
private theorem c3030_e'    : LeafE' 3030     := by decide +kernel
private theorem c3030_f1    : LeafF1 3030     := Or.inl (by decide)
private theorem c3030_s2    : S2ChkSq 3030    := by decide +kernel
private theorem c3030_s3    : S3ChkSq 3030    := by decide +kernel
private theorem c3030_iso   : LeafIso 3030    := by decide +kernel
private theorem c3030_nof2  : NoF2ChkSq 3030  := by decide +kernel
private theorem c3030_nof3  : NoF3ChkSq 3030  := by decide +kernel
private theorem c3030_nof4z : NoF4zChkSq 3030 := by decide +kernel
theorem C'_3030 : C' 3030 :=
  ⟨c3030_sqf, c3030_range, c3030_ell, leafNSq_of_sq c3030_nsq, leafHAr_of_sq c3030_har,
   c3030_r, c3030_e', c3030_f1, leafS2_of_sq c3030_s2, leafS3_of_sq c3030_s3,
   c3030_iso, leafR8_of_sq c3030_nof2 c3030_nof3 c3030_nof4z⟩
theorem not_tile'_3030 (D : CongruentDissection 3030) : False :=
  not_tile_of_conditions' 3030 C'_3030 D

private theorem c3031_sqf   : LeafSqf 3031   := by decide +kernel
private theorem c3031_range : LeafRange 3031  := by decide +kernel
private theorem c3031_ell   : LeafEll 3031    := by decide +kernel
private theorem c3031_nsq   : NSqChkSq 3031   := by decide +kernel
private theorem c3031_har   : HArithChkSq 3031 := by decide +kernel
private theorem c3031_r     : LeafR 3031      := by decide +kernel
private theorem c3031_e'    : LeafE' 3031     := by decide +kernel
private theorem c3031_f1    : LeafF1 3031     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3031_s2    : S2ChkSq 3031    := by decide +kernel
private theorem c3031_s3    : S3ChkSq 3031    := by decide +kernel
private theorem c3031_iso   : LeafIso 3031    := by decide +kernel
private theorem c3031_nof2  : NoF2ChkSq 3031  := by decide +kernel
private theorem c3031_nof3  : NoF3ChkSq 3031  := by decide +kernel
private theorem c3031_nof4z : NoF4zChkSq 3031 := by decide +kernel
theorem C'_3031 : C' 3031 :=
  ⟨c3031_sqf, c3031_range, c3031_ell, leafNSq_of_sq c3031_nsq, leafHAr_of_sq c3031_har,
   c3031_r, c3031_e', c3031_f1, leafS2_of_sq c3031_s2, leafS3_of_sq c3031_s3,
   c3031_iso, leafR8_of_sq c3031_nof2 c3031_nof3 c3031_nof4z⟩
theorem not_tile'_3031 (D : CongruentDissection 3031) : False :=
  not_tile_of_conditions' 3031 C'_3031 D

end Erdos634.Draft.AllN2

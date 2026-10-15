/- AllN2Check209: N = 4027, 4030, 4031, 4037, 4038
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4027_sqf   : LeafSqf 4027   := by decide +kernel
private theorem c4027_range : LeafRange 4027  := by decide +kernel
private theorem c4027_ell   : LeafEll 4027    := by decide +kernel
private theorem c4027_nsq   : NSqChkSq 4027   := by decide +kernel
private theorem c4027_har   : HArithChkSq 4027 := by decide +kernel
private theorem c4027_r     : LeafR 4027      := by decide +kernel
private theorem c4027_e'    : LeafE' 4027     := by decide +kernel
private theorem c4027_f1    : LeafF1 4027     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4027_s2    : S2ChkSq 4027    := by decide +kernel
private theorem c4027_s3    : S3ChkSq 4027    := by decide +kernel
private theorem c4027_iso   : LeafIso 4027    := by decide +kernel
private theorem c4027_nof2  : NoF2ChkSq 4027  := by decide +kernel
private theorem c4027_nof3  : NoF3ChkSq 4027  := by decide +kernel
private theorem c4027_nof4z : NoF4zChkSq 4027 := by decide +kernel
theorem C'_4027 : C' 4027 :=
  ⟨c4027_sqf, c4027_range, c4027_ell, leafNSq_of_sq c4027_nsq, leafHAr_of_sq c4027_har,
   c4027_r, c4027_e', c4027_f1, leafS2_of_sq c4027_s2, leafS3_of_sq c4027_s3,
   c4027_iso, leafR8_of_sq c4027_nof2 c4027_nof3 c4027_nof4z⟩
theorem not_tile'_4027 (D : CongruentDissection 4027) : False :=
  not_tile_of_conditions' 4027 C'_4027 D

private theorem c4030_sqf   : LeafSqf 4030   := by decide +kernel
private theorem c4030_range : LeafRange 4030  := by decide +kernel
private theorem c4030_ell   : LeafEll 4030    := by decide +kernel
private theorem c4030_nsq   : NSqChkSq 4030   := by decide +kernel
private theorem c4030_har   : HArithChkSq 4030 := by decide +kernel
private theorem c4030_r     : LeafR 4030      := by decide +kernel
private theorem c4030_e'    : LeafE' 4030     := by decide +kernel
private theorem c4030_f1    : LeafF1 4030     := Or.inl (by decide)
private theorem c4030_s2    : S2ChkSq 4030    := by decide +kernel
private theorem c4030_s3    : S3ChkSq 4030    := by decide +kernel
private theorem c4030_iso   : LeafIso 4030    := by decide +kernel
private theorem c4030_nof2  : NoF2ChkSq 4030  := by decide +kernel
private theorem c4030_nof3  : NoF3ChkSq 4030  := by decide +kernel
private theorem c4030_nof4z : NoF4zChkSq 4030 := by decide +kernel
theorem C'_4030 : C' 4030 :=
  ⟨c4030_sqf, c4030_range, c4030_ell, leafNSq_of_sq c4030_nsq, leafHAr_of_sq c4030_har,
   c4030_r, c4030_e', c4030_f1, leafS2_of_sq c4030_s2, leafS3_of_sq c4030_s3,
   c4030_iso, leafR8_of_sq c4030_nof2 c4030_nof3 c4030_nof4z⟩
theorem not_tile'_4030 (D : CongruentDissection 4030) : False :=
  not_tile_of_conditions' 4030 C'_4030 D

private theorem c4031_sqf   : LeafSqf 4031   := by decide +kernel
private theorem c4031_range : LeafRange 4031  := by decide +kernel
private theorem c4031_ell   : LeafEll 4031    := by decide +kernel
private theorem c4031_nsq   : NSqChkSq 4031   := by decide +kernel
private theorem c4031_har   : HArithChkSq 4031 := by decide +kernel
private theorem c4031_r     : LeafR 4031      := by decide +kernel
private theorem c4031_e'    : LeafE' 4031     := by decide +kernel
private theorem c4031_f1    : LeafF1 4031     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4031_s2    : S2ChkSq 4031    := by decide +kernel
private theorem c4031_s3    : S3ChkSq 4031    := by decide +kernel
private theorem c4031_iso   : LeafIso 4031    := by decide +kernel
private theorem c4031_nof2  : NoF2ChkSq 4031  := by decide +kernel
private theorem c4031_nof3  : NoF3ChkSq 4031  := by decide +kernel
private theorem c4031_nof4z : NoF4zChkSq 4031 := by decide +kernel
theorem C'_4031 : C' 4031 :=
  ⟨c4031_sqf, c4031_range, c4031_ell, leafNSq_of_sq c4031_nsq, leafHAr_of_sq c4031_har,
   c4031_r, c4031_e', c4031_f1, leafS2_of_sq c4031_s2, leafS3_of_sq c4031_s3,
   c4031_iso, leafR8_of_sq c4031_nof2 c4031_nof3 c4031_nof4z⟩
theorem not_tile'_4031 (D : CongruentDissection 4031) : False :=
  not_tile_of_conditions' 4031 C'_4031 D

private theorem c4037_sqf   : LeafSqf 4037   := by decide +kernel
private theorem c4037_range : LeafRange 4037  := by decide +kernel
private theorem c4037_ell   : LeafEll 4037    := by decide +kernel
private theorem c4037_nsq   : NSqChkSq 4037   := by decide +kernel
private theorem c4037_har   : HArithChkSq 4037 := by decide +kernel
private theorem c4037_r     : LeafR 4037      := by decide +kernel
private theorem c4037_e'    : LeafE' 4037     := by decide +kernel
private theorem c4037_f1    : LeafF1 4037     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4037_s2    : S2ChkSq 4037    := by decide +kernel
private theorem c4037_s3    : S3ChkSq 4037    := by decide +kernel
private theorem c4037_iso   : LeafIso 4037    := by decide +kernel
private theorem c4037_nof2  : NoF2ChkSq 4037  := by decide +kernel
private theorem c4037_nof3  : NoF3ChkSq 4037  := by decide +kernel
private theorem c4037_nof4z : NoF4zChkSq 4037 := by decide +kernel
theorem C'_4037 : C' 4037 :=
  ⟨c4037_sqf, c4037_range, c4037_ell, leafNSq_of_sq c4037_nsq, leafHAr_of_sq c4037_har,
   c4037_r, c4037_e', c4037_f1, leafS2_of_sq c4037_s2, leafS3_of_sq c4037_s3,
   c4037_iso, leafR8_of_sq c4037_nof2 c4037_nof3 c4037_nof4z⟩
theorem not_tile'_4037 (D : CongruentDissection 4037) : False :=
  not_tile_of_conditions' 4037 C'_4037 D

private theorem c4038_sqf   : LeafSqf 4038   := by decide +kernel
private theorem c4038_range : LeafRange 4038  := by decide +kernel
private theorem c4038_ell   : LeafEll 4038    := by decide +kernel
private theorem c4038_nsq   : NSqChkSq 4038   := by decide +kernel
private theorem c4038_har   : HArithChkSq 4038 := by decide +kernel
private theorem c4038_r     : LeafR 4038      := by decide +kernel
private theorem c4038_e'    : LeafE' 4038     := by decide +kernel
private theorem c4038_f1    : LeafF1 4038     := Or.inl (by decide)
private theorem c4038_s2    : S2ChkSq 4038    := by decide +kernel
private theorem c4038_s3    : S3ChkSq 4038    := by decide +kernel
private theorem c4038_iso   : LeafIso 4038    := by decide +kernel
private theorem c4038_nof2  : NoF2ChkSq 4038  := by decide +kernel
private theorem c4038_nof3  : NoF3ChkSq 4038  := by decide +kernel
private theorem c4038_nof4z : NoF4zChkSq 4038 := by decide +kernel
theorem C'_4038 : C' 4038 :=
  ⟨c4038_sqf, c4038_range, c4038_ell, leafNSq_of_sq c4038_nsq, leafHAr_of_sq c4038_har,
   c4038_r, c4038_e', c4038_f1, leafS2_of_sq c4038_s2, leafS3_of_sq c4038_s3,
   c4038_iso, leafR8_of_sq c4038_nof2 c4038_nof3 c4038_nof4z⟩
theorem not_tile'_4038 (D : CongruentDissection 4038) : False :=
  not_tile_of_conditions' 4038 C'_4038 D

end Erdos634.Draft.AllN2

/- AllN2Check208: N = 4009, 4015, 4019, 4022, 4026
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4009_sqf   : LeafSqf 4009   := by decide +kernel
private theorem c4009_range : LeafRange 4009  := by decide +kernel
private theorem c4009_ell   : LeafEll 4009    := by decide +kernel
private theorem c4009_nsq   : NSqChkSq 4009   := by decide +kernel
private theorem c4009_har   : HArithChkSq 4009 := by decide +kernel
private theorem c4009_r     : LeafR 4009      := by decide +kernel
private theorem c4009_e'    : LeafE' 4009     := by decide +kernel
private theorem c4009_f1    : LeafF1 4009     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4009_s2    : S2ChkSq 4009    := by decide +kernel
private theorem c4009_s3    : S3ChkSq 4009    := by decide +kernel
private theorem c4009_iso   : LeafIso 4009    := by decide +kernel
private theorem c4009_nof2  : NoF2ChkSq 4009  := by decide +kernel
private theorem c4009_nof3  : NoF3ChkSq 4009  := by decide +kernel
private theorem c4009_nof4z : NoF4zChkSq 4009 := by decide +kernel
theorem C'_4009 : C' 4009 :=
  ⟨c4009_sqf, c4009_range, c4009_ell, leafNSq_of_sq c4009_nsq, leafHAr_of_sq c4009_har,
   c4009_r, c4009_e', c4009_f1, leafS2_of_sq c4009_s2, leafS3_of_sq c4009_s3,
   c4009_iso, leafR8_of_sq c4009_nof2 c4009_nof3 c4009_nof4z⟩
theorem not_tile'_4009 (D : CongruentDissection 4009) : False :=
  not_tile_of_conditions' 4009 C'_4009 D

private theorem c4015_sqf   : LeafSqf 4015   := by decide +kernel
private theorem c4015_range : LeafRange 4015  := by decide +kernel
private theorem c4015_ell   : LeafEll 4015    := by decide +kernel
private theorem c4015_nsq   : NSqChkSq 4015   := by decide +kernel
private theorem c4015_har   : HArithChkSq 4015 := by decide +kernel
private theorem c4015_r     : LeafR 4015      := by decide +kernel
private theorem c4015_e'    : LeafE' 4015     := by decide +kernel
private theorem c4015_f1    : LeafF1 4015     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4015_s2    : S2ChkSq 4015    := by decide +kernel
private theorem c4015_s3    : S3ChkSq 4015    := by decide +kernel
private theorem c4015_iso   : LeafIso 4015    := by decide +kernel
private theorem c4015_nof2  : NoF2ChkSq 4015  := by decide +kernel
private theorem c4015_nof3  : NoF3ChkSq 4015  := by decide +kernel
private theorem c4015_nof4z : NoF4zChkSq 4015 := by decide +kernel
theorem C'_4015 : C' 4015 :=
  ⟨c4015_sqf, c4015_range, c4015_ell, leafNSq_of_sq c4015_nsq, leafHAr_of_sq c4015_har,
   c4015_r, c4015_e', c4015_f1, leafS2_of_sq c4015_s2, leafS3_of_sq c4015_s3,
   c4015_iso, leafR8_of_sq c4015_nof2 c4015_nof3 c4015_nof4z⟩
theorem not_tile'_4015 (D : CongruentDissection 4015) : False :=
  not_tile_of_conditions' 4015 C'_4015 D

private theorem c4019_sqf   : LeafSqf 4019   := by decide +kernel
private theorem c4019_range : LeafRange 4019  := by decide +kernel
private theorem c4019_ell   : LeafEll 4019    := by decide +kernel
private theorem c4019_nsq   : NSqChkSq 4019   := by decide +kernel
private theorem c4019_har   : HArithChkSq 4019 := by decide +kernel
private theorem c4019_r     : LeafR 4019      := by decide +kernel
private theorem c4019_e'    : LeafE' 4019     := by decide +kernel
private theorem c4019_f1    : LeafF1 4019     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4019_s2    : S2ChkSq 4019    := by decide +kernel
private theorem c4019_s3    : S3ChkSq 4019    := by decide +kernel
private theorem c4019_iso   : LeafIso 4019    := by decide +kernel
private theorem c4019_nof2  : NoF2ChkSq 4019  := by decide +kernel
private theorem c4019_nof3  : NoF3ChkSq 4019  := by decide +kernel
private theorem c4019_nof4z : NoF4zChkSq 4019 := by decide +kernel
theorem C'_4019 : C' 4019 :=
  ⟨c4019_sqf, c4019_range, c4019_ell, leafNSq_of_sq c4019_nsq, leafHAr_of_sq c4019_har,
   c4019_r, c4019_e', c4019_f1, leafS2_of_sq c4019_s2, leafS3_of_sq c4019_s3,
   c4019_iso, leafR8_of_sq c4019_nof2 c4019_nof3 c4019_nof4z⟩
theorem not_tile'_4019 (D : CongruentDissection 4019) : False :=
  not_tile_of_conditions' 4019 C'_4019 D

private theorem c4022_sqf   : LeafSqf 4022   := by decide +kernel
private theorem c4022_range : LeafRange 4022  := by decide +kernel
private theorem c4022_ell   : LeafEll 4022    := by decide +kernel
private theorem c4022_nsq   : NSqChkSq 4022   := by decide +kernel
private theorem c4022_har   : HArithChkSq 4022 := by decide +kernel
private theorem c4022_r     : LeafR 4022      := by decide +kernel
private theorem c4022_e'    : LeafE' 4022     := by decide +kernel
private theorem c4022_f1    : LeafF1 4022     := Or.inl (by decide)
private theorem c4022_s2    : S2ChkSq 4022    := by decide +kernel
private theorem c4022_s3    : S3ChkSq 4022    := by decide +kernel
private theorem c4022_iso   : LeafIso 4022    := by decide +kernel
private theorem c4022_nof2  : NoF2ChkSq 4022  := by decide +kernel
private theorem c4022_nof3  : NoF3ChkSq 4022  := by decide +kernel
private theorem c4022_nof4z : NoF4zChkSq 4022 := by decide +kernel
theorem C'_4022 : C' 4022 :=
  ⟨c4022_sqf, c4022_range, c4022_ell, leafNSq_of_sq c4022_nsq, leafHAr_of_sq c4022_har,
   c4022_r, c4022_e', c4022_f1, leafS2_of_sq c4022_s2, leafS3_of_sq c4022_s3,
   c4022_iso, leafR8_of_sq c4022_nof2 c4022_nof3 c4022_nof4z⟩
theorem not_tile'_4022 (D : CongruentDissection 4022) : False :=
  not_tile_of_conditions' 4022 C'_4022 D

private theorem c4026_sqf   : LeafSqf 4026   := by decide +kernel
private theorem c4026_range : LeafRange 4026  := by decide +kernel
private theorem c4026_ell   : LeafEll 4026    := by decide +kernel
private theorem c4026_nsq   : NSqChkSq 4026   := by decide +kernel
private theorem c4026_har   : HArithChkSq 4026 := by decide +kernel
private theorem c4026_r     : LeafR 4026      := by decide +kernel
private theorem c4026_e'    : LeafE' 4026     := by decide +kernel
private theorem c4026_f1    : LeafF1 4026     := Or.inl (by decide)
private theorem c4026_s2    : S2ChkSq 4026    := by decide +kernel
private theorem c4026_s3    : S3ChkSq 4026    := by decide +kernel
private theorem c4026_iso   : LeafIso 4026    := by decide +kernel
private theorem c4026_nof2  : NoF2ChkSq 4026  := by decide +kernel
private theorem c4026_nof3  : NoF3ChkSq 4026  := by decide +kernel
private theorem c4026_nof4z : NoF4zChkSq 4026 := by decide +kernel
theorem C'_4026 : C' 4026 :=
  ⟨c4026_sqf, c4026_range, c4026_ell, leafNSq_of_sq c4026_nsq, leafHAr_of_sq c4026_har,
   c4026_r, c4026_e', c4026_f1, leafS2_of_sq c4026_s2, leafS3_of_sq c4026_s3,
   c4026_iso, leafR8_of_sq c4026_nof2 c4026_nof3 c4026_nof4z⟩
theorem not_tile'_4026 (D : CongruentDissection 4026) : False :=
  not_tile_of_conditions' 4026 C'_4026 D

end Erdos634.Draft.AllN2

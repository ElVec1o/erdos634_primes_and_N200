/- AllN2Check291: N = 5034, 5035, 5038, 5039, 5051
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c5034_sqf   : LeafSqf 5034   := by decide +kernel
private theorem c5034_range : LeafRange 5034  := by decide +kernel
private theorem c5034_ell   : LeafEll 5034    := by decide +kernel
private theorem c5034_nsq   : NSqChkSq 5034   := by decide +kernel
private theorem c5034_har   : HArithChkSq 5034 := by decide +kernel
private theorem c5034_r     : LeafR 5034      := by decide +kernel
private theorem c5034_e'    : LeafE' 5034     := by decide +kernel
private theorem c5034_f1    : LeafF1 5034     := Or.inl (by decide)
private theorem c5034_s2    : S2ChkSq 5034    := by decide +kernel
private theorem c5034_s3    : S3ChkSq 5034    := by decide +kernel
private theorem c5034_iso   : LeafIso 5034    := by decide +kernel
private theorem c5034_nof2  : NoF2ChkSq 5034  := by decide +kernel
private theorem c5034_nof3  : NoF3ChkSq 5034  := by decide +kernel
private theorem c5034_nof4z : NoF4zChkSq 5034 := by decide +kernel
theorem C'_5034 : C' 5034 :=
  ⟨c5034_sqf, c5034_range, c5034_ell, leafNSq_of_sq c5034_nsq, leafHAr_of_sq c5034_har,
   c5034_r, c5034_e', c5034_f1, leafS2_of_sq c5034_s2, leafS3_of_sq c5034_s3,
   c5034_iso, leafR8_of_sq c5034_nof2 c5034_nof3 c5034_nof4z⟩
theorem not_tile'_5034 (D : CongruentDissection 5034) : False :=
  not_tile_of_conditions' 5034 C'_5034 D

private theorem c5035_sqf   : LeafSqf 5035   := by decide +kernel
private theorem c5035_range : LeafRange 5035  := by decide +kernel
private theorem c5035_ell   : LeafEll 5035    := by decide +kernel
private theorem c5035_nsq   : NSqChkSq 5035   := by decide +kernel
private theorem c5035_har   : HArithChkSq 5035 := by decide +kernel
private theorem c5035_r     : LeafR 5035      := by decide +kernel
private theorem c5035_e'    : LeafE' 5035     := by decide +kernel
private theorem c5035_f1    : LeafF1 5035     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c5035_s2    : S2ChkSq 5035    := by decide +kernel
private theorem c5035_s3    : S3ChkSq 5035    := by decide +kernel
private theorem c5035_iso   : LeafIso 5035    := by decide +kernel
private theorem c5035_nof2  : NoF2ChkSq 5035  := by decide +kernel
private theorem c5035_nof3  : NoF3ChkSq 5035  := by decide +kernel
private theorem c5035_nof4z : NoF4zChkSq 5035 := by decide +kernel
theorem C'_5035 : C' 5035 :=
  ⟨c5035_sqf, c5035_range, c5035_ell, leafNSq_of_sq c5035_nsq, leafHAr_of_sq c5035_har,
   c5035_r, c5035_e', c5035_f1, leafS2_of_sq c5035_s2, leafS3_of_sq c5035_s3,
   c5035_iso, leafR8_of_sq c5035_nof2 c5035_nof3 c5035_nof4z⟩
theorem not_tile'_5035 (D : CongruentDissection 5035) : False :=
  not_tile_of_conditions' 5035 C'_5035 D

private theorem c5038_sqf   : LeafSqf 5038   := by decide +kernel
private theorem c5038_range : LeafRange 5038  := by decide +kernel
private theorem c5038_ell   : LeafEll 5038    := by decide +kernel
private theorem c5038_nsq   : NSqChkSq 5038   := by decide +kernel
private theorem c5038_har   : HArithChkSq 5038 := by decide +kernel
private theorem c5038_r     : LeafR 5038      := by decide +kernel
private theorem c5038_e'    : LeafE' 5038     := by decide +kernel
private theorem c5038_f1    : LeafF1 5038     := Or.inl (by decide)
private theorem c5038_s2    : S2ChkSq 5038    := by decide +kernel
private theorem c5038_s3    : S3ChkSq 5038    := by decide +kernel
private theorem c5038_iso   : LeafIso 5038    := by decide +kernel
private theorem c5038_nof2  : NoF2ChkSq 5038  := by decide +kernel
private theorem c5038_nof3  : NoF3ChkSq 5038  := by decide +kernel
private theorem c5038_nof4z : NoF4zChkSq 5038 := by decide +kernel
theorem C'_5038 : C' 5038 :=
  ⟨c5038_sqf, c5038_range, c5038_ell, leafNSq_of_sq c5038_nsq, leafHAr_of_sq c5038_har,
   c5038_r, c5038_e', c5038_f1, leafS2_of_sq c5038_s2, leafS3_of_sq c5038_s3,
   c5038_iso, leafR8_of_sq c5038_nof2 c5038_nof3 c5038_nof4z⟩
theorem not_tile'_5038 (D : CongruentDissection 5038) : False :=
  not_tile_of_conditions' 5038 C'_5038 D

private theorem c5039_sqf   : LeafSqf 5039   := by decide +kernel
private theorem c5039_range : LeafRange 5039  := by decide +kernel
private theorem c5039_ell   : LeafEll 5039    := by decide +kernel
private theorem c5039_nsq   : NSqChkSq 5039   := by decide +kernel
private theorem c5039_har   : HArithChkSq 5039 := by decide +kernel
private theorem c5039_r     : LeafR 5039      := by decide +kernel
private theorem c5039_e'    : LeafE' 5039     := by decide +kernel
private theorem c5039_f1    : LeafF1 5039     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c5039_s2    : S2ChkSq 5039    := by decide +kernel
private theorem c5039_s3    : S3ChkSq 5039    := by decide +kernel
private theorem c5039_iso   : LeafIso 5039    := by decide +kernel
private theorem c5039_nof2  : NoF2ChkSq 5039  := by decide +kernel
private theorem c5039_nof3  : NoF3ChkSq 5039  := by decide +kernel
private theorem c5039_nof4z : NoF4zChkSq 5039 := by decide +kernel
theorem C'_5039 : C' 5039 :=
  ⟨c5039_sqf, c5039_range, c5039_ell, leafNSq_of_sq c5039_nsq, leafHAr_of_sq c5039_har,
   c5039_r, c5039_e', c5039_f1, leafS2_of_sq c5039_s2, leafS3_of_sq c5039_s3,
   c5039_iso, leafR8_of_sq c5039_nof2 c5039_nof3 c5039_nof4z⟩
theorem not_tile'_5039 (D : CongruentDissection 5039) : False :=
  not_tile_of_conditions' 5039 C'_5039 D

private theorem c5051_sqf   : LeafSqf 5051   := by decide +kernel
private theorem c5051_range : LeafRange 5051  := by decide +kernel
private theorem c5051_ell   : LeafEll 5051    := by decide +kernel
private theorem c5051_nsq   : NSqChkSq 5051   := by decide +kernel
private theorem c5051_har   : HArithChkSq 5051 := by decide +kernel
private theorem c5051_r     : LeafR 5051      := by decide +kernel
private theorem c5051_e'    : LeafE' 5051     := by decide +kernel
private theorem c5051_f1    : LeafF1 5051     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c5051_s2    : S2ChkSq 5051    := by decide +kernel
private theorem c5051_s3    : S3ChkSq 5051    := by decide +kernel
private theorem c5051_iso   : LeafIso 5051    := by decide +kernel
private theorem c5051_nof2  : NoF2ChkSq 5051  := by decide +kernel
private theorem c5051_nof3  : NoF3ChkSq 5051  := by decide +kernel
private theorem c5051_nof4z : NoF4zChkSq 5051 := by decide +kernel
theorem C'_5051 : C' 5051 :=
  ⟨c5051_sqf, c5051_range, c5051_ell, leafNSq_of_sq c5051_nsq, leafHAr_of_sq c5051_har,
   c5051_r, c5051_e', c5051_f1, leafS2_of_sq c5051_s2, leafS3_of_sq c5051_s3,
   c5051_iso, leafR8_of_sq c5051_nof2 c5051_nof3 c5051_nof4z⟩
theorem not_tile'_5051 (D : CongruentDissection 5051) : False :=
  not_tile_of_conditions' 5051 C'_5051 D

end Erdos634.Draft.AllN2

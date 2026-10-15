/- AllN2Check210: N = 4039, 4042, 4043, 4051, 4054
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4039_sqf   : LeafSqf 4039   := by decide +kernel
private theorem c4039_range : LeafRange 4039  := by decide +kernel
private theorem c4039_ell   : LeafEll 4039    := by decide +kernel
private theorem c4039_nsq   : NSqChkSq 4039   := by decide +kernel
private theorem c4039_har   : HArithChkSq 4039 := by decide +kernel
private theorem c4039_r     : LeafR 4039      := by decide +kernel
private theorem c4039_e'    : LeafE' 4039     := by decide +kernel
private theorem c4039_f1    : LeafF1 4039     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4039_s2    : S2ChkSq 4039    := by decide +kernel
private theorem c4039_s3    : S3ChkSq 4039    := by decide +kernel
private theorem c4039_iso   : LeafIso 4039    := by decide +kernel
private theorem c4039_nof2  : NoF2ChkSq 4039  := by decide +kernel
private theorem c4039_nof3  : NoF3ChkSq 4039  := by decide +kernel
private theorem c4039_nof4z : NoF4zChkSq 4039 := by decide +kernel
theorem C'_4039 : C' 4039 :=
  ⟨c4039_sqf, c4039_range, c4039_ell, leafNSq_of_sq c4039_nsq, leafHAr_of_sq c4039_har,
   c4039_r, c4039_e', c4039_f1, leafS2_of_sq c4039_s2, leafS3_of_sq c4039_s3,
   c4039_iso, leafR8_of_sq c4039_nof2 c4039_nof3 c4039_nof4z⟩
theorem not_tile'_4039 (D : CongruentDissection 4039) : False :=
  not_tile_of_conditions' 4039 C'_4039 D

private theorem c4042_sqf   : LeafSqf 4042   := by decide +kernel
private theorem c4042_range : LeafRange 4042  := by decide +kernel
private theorem c4042_ell   : LeafEll 4042    := by decide +kernel
private theorem c4042_nsq   : NSqChkSq 4042   := by decide +kernel
private theorem c4042_har   : HArithChkSq 4042 := by decide +kernel
private theorem c4042_r     : LeafR 4042      := by decide +kernel
private theorem c4042_e'    : LeafE' 4042     := by decide +kernel
private theorem c4042_f1    : LeafF1 4042     := Or.inl (by decide)
private theorem c4042_s2    : S2ChkSq 4042    := by decide +kernel
private theorem c4042_s3    : S3ChkSq 4042    := by decide +kernel
private theorem c4042_iso   : LeafIso 4042    := by decide +kernel
private theorem c4042_nof2  : NoF2ChkSq 4042  := by decide +kernel
private theorem c4042_nof3  : NoF3ChkSq 4042  := by decide +kernel
private theorem c4042_nof4z : NoF4zChkSq 4042 := by decide +kernel
theorem C'_4042 : C' 4042 :=
  ⟨c4042_sqf, c4042_range, c4042_ell, leafNSq_of_sq c4042_nsq, leafHAr_of_sq c4042_har,
   c4042_r, c4042_e', c4042_f1, leafS2_of_sq c4042_s2, leafS3_of_sq c4042_s3,
   c4042_iso, leafR8_of_sq c4042_nof2 c4042_nof3 c4042_nof4z⟩
theorem not_tile'_4042 (D : CongruentDissection 4042) : False :=
  not_tile_of_conditions' 4042 C'_4042 D

private theorem c4043_sqf   : LeafSqf 4043   := by decide +kernel
private theorem c4043_range : LeafRange 4043  := by decide +kernel
private theorem c4043_ell   : LeafEll 4043    := by decide +kernel
private theorem c4043_nsq   : NSqChkSq 4043   := by decide +kernel
private theorem c4043_har   : HArithChkSq 4043 := by decide +kernel
private theorem c4043_r     : LeafR 4043      := by decide +kernel
private theorem c4043_e'    : LeafE' 4043     := by decide +kernel
private theorem c4043_f1    : LeafF1 4043     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4043_s2    : S2ChkSq 4043    := by decide +kernel
private theorem c4043_s3    : S3ChkSq 4043    := by decide +kernel
private theorem c4043_iso   : LeafIso 4043    := by decide +kernel
private theorem c4043_nof2  : NoF2ChkSq 4043  := by decide +kernel
private theorem c4043_nof3  : NoF3ChkSq 4043  := by decide +kernel
private theorem c4043_nof4z : NoF4zChkSq 4043 := by decide +kernel
theorem C'_4043 : C' 4043 :=
  ⟨c4043_sqf, c4043_range, c4043_ell, leafNSq_of_sq c4043_nsq, leafHAr_of_sq c4043_har,
   c4043_r, c4043_e', c4043_f1, leafS2_of_sq c4043_s2, leafS3_of_sq c4043_s3,
   c4043_iso, leafR8_of_sq c4043_nof2 c4043_nof3 c4043_nof4z⟩
theorem not_tile'_4043 (D : CongruentDissection 4043) : False :=
  not_tile_of_conditions' 4043 C'_4043 D

private theorem c4051_sqf   : LeafSqf 4051   := by decide +kernel
private theorem c4051_range : LeafRange 4051  := by decide +kernel
private theorem c4051_ell   : LeafEll 4051    := by decide +kernel
private theorem c4051_nsq   : NSqChkSq 4051   := by decide +kernel
private theorem c4051_har   : HArithChkSq 4051 := by decide +kernel
private theorem c4051_r     : LeafR 4051      := by decide +kernel
private theorem c4051_e'    : LeafE' 4051     := by decide +kernel
private theorem c4051_f1    : LeafF1 4051     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4051_s2    : S2ChkSq 4051    := by decide +kernel
private theorem c4051_s3    : S3ChkSq 4051    := by decide +kernel
private theorem c4051_iso   : LeafIso 4051    := by decide +kernel
private theorem c4051_nof2  : NoF2ChkSq 4051  := by decide +kernel
private theorem c4051_nof3  : NoF3ChkSq 4051  := by decide +kernel
private theorem c4051_nof4z : NoF4zChkSq 4051 := by decide +kernel
theorem C'_4051 : C' 4051 :=
  ⟨c4051_sqf, c4051_range, c4051_ell, leafNSq_of_sq c4051_nsq, leafHAr_of_sq c4051_har,
   c4051_r, c4051_e', c4051_f1, leafS2_of_sq c4051_s2, leafS3_of_sq c4051_s3,
   c4051_iso, leafR8_of_sq c4051_nof2 c4051_nof3 c4051_nof4z⟩
theorem not_tile'_4051 (D : CongruentDissection 4051) : False :=
  not_tile_of_conditions' 4051 C'_4051 D

private theorem c4054_sqf   : LeafSqf 4054   := by decide +kernel
private theorem c4054_range : LeafRange 4054  := by decide +kernel
private theorem c4054_ell   : LeafEll 4054    := by decide +kernel
private theorem c4054_nsq   : NSqChkSq 4054   := by decide +kernel
private theorem c4054_har   : HArithChkSq 4054 := by decide +kernel
private theorem c4054_r     : LeafR 4054      := by decide +kernel
private theorem c4054_e'    : LeafE' 4054     := by decide +kernel
private theorem c4054_f1    : LeafF1 4054     := Or.inl (by decide)
private theorem c4054_s2    : S2ChkSq 4054    := by decide +kernel
private theorem c4054_s3    : S3ChkSq 4054    := by decide +kernel
private theorem c4054_iso   : LeafIso 4054    := by decide +kernel
private theorem c4054_nof2  : NoF2ChkSq 4054  := by decide +kernel
private theorem c4054_nof3  : NoF3ChkSq 4054  := by decide +kernel
private theorem c4054_nof4z : NoF4zChkSq 4054 := by decide +kernel
theorem C'_4054 : C' 4054 :=
  ⟨c4054_sqf, c4054_range, c4054_ell, leafNSq_of_sq c4054_nsq, leafHAr_of_sq c4054_har,
   c4054_r, c4054_e', c4054_f1, leafS2_of_sq c4054_s2, leafS3_of_sq c4054_s3,
   c4054_iso, leafR8_of_sq c4054_nof2 c4054_nof3 c4054_nof4z⟩
theorem not_tile'_4054 (D : CongruentDissection 4054) : False :=
  not_tile_of_conditions' 4054 C'_4054 D

end Erdos634.Draft.AllN2

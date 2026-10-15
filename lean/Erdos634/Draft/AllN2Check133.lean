/- AllN2Check133: N = 3035, 3039, 3043, 3046, 3047
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3035_sqf   : LeafSqf 3035   := by decide +kernel
private theorem c3035_range : LeafRange 3035  := by decide +kernel
private theorem c3035_ell   : LeafEll 3035    := by decide +kernel
private theorem c3035_nsq   : NSqChkSq 3035   := by decide +kernel
private theorem c3035_har   : HArithChkSq 3035 := by decide +kernel
private theorem c3035_r     : LeafR 3035      := by decide +kernel
private theorem c3035_e'    : LeafE' 3035     := by decide +kernel
private theorem c3035_f1    : LeafF1 3035     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3035_s2    : S2ChkSq 3035    := by decide +kernel
private theorem c3035_s3    : S3ChkSq 3035    := by decide +kernel
private theorem c3035_iso   : LeafIso 3035    := by decide +kernel
private theorem c3035_nof2  : NoF2ChkSq 3035  := by decide +kernel
private theorem c3035_nof3  : NoF3ChkSq 3035  := by decide +kernel
private theorem c3035_nof4z : NoF4zChkSq 3035 := by decide +kernel
theorem C'_3035 : C' 3035 :=
  ⟨c3035_sqf, c3035_range, c3035_ell, leafNSq_of_sq c3035_nsq, leafHAr_of_sq c3035_har,
   c3035_r, c3035_e', c3035_f1, leafS2_of_sq c3035_s2, leafS3_of_sq c3035_s3,
   c3035_iso, leafR8_of_sq c3035_nof2 c3035_nof3 c3035_nof4z⟩
theorem not_tile'_3035 (D : CongruentDissection 3035) : False :=
  not_tile_of_conditions' 3035 C'_3035 D

private theorem c3039_sqf   : LeafSqf 3039   := by decide +kernel
private theorem c3039_range : LeafRange 3039  := by decide +kernel
private theorem c3039_ell   : LeafEll 3039    := by decide +kernel
private theorem c3039_nsq   : NSqChkSq 3039   := by decide +kernel
private theorem c3039_har   : HArithChkSq 3039 := by decide +kernel
private theorem c3039_r     : LeafR 3039      := by decide +kernel
private theorem c3039_e'    : LeafE' 3039     := by decide +kernel
private theorem c3039_f1    : LeafF1 3039     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3039_s2    : S2ChkSq 3039    := by decide +kernel
private theorem c3039_s3    : S3ChkSq 3039    := by decide +kernel
private theorem c3039_iso   : LeafIso 3039    := by decide +kernel
private theorem c3039_nof2  : NoF2ChkSq 3039  := by decide +kernel
private theorem c3039_nof3  : NoF3ChkSq 3039  := by decide +kernel
private theorem c3039_nof4z : NoF4zChkSq 3039 := by decide +kernel
theorem C'_3039 : C' 3039 :=
  ⟨c3039_sqf, c3039_range, c3039_ell, leafNSq_of_sq c3039_nsq, leafHAr_of_sq c3039_har,
   c3039_r, c3039_e', c3039_f1, leafS2_of_sq c3039_s2, leafS3_of_sq c3039_s3,
   c3039_iso, leafR8_of_sq c3039_nof2 c3039_nof3 c3039_nof4z⟩
theorem not_tile'_3039 (D : CongruentDissection 3039) : False :=
  not_tile_of_conditions' 3039 C'_3039 D

private theorem c3043_sqf   : LeafSqf 3043   := by decide +kernel
private theorem c3043_range : LeafRange 3043  := by decide +kernel
private theorem c3043_ell   : LeafEll 3043    := by decide +kernel
private theorem c3043_nsq   : NSqChkSq 3043   := by decide +kernel
private theorem c3043_har   : HArithChkSq 3043 := by decide +kernel
private theorem c3043_r     : LeafR 3043      := by decide +kernel
private theorem c3043_e'    : LeafE' 3043     := by decide +kernel
private theorem c3043_f1    : LeafF1 3043     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3043_s2    : S2ChkSq 3043    := by decide +kernel
private theorem c3043_s3    : S3ChkSq 3043    := by decide +kernel
private theorem c3043_iso   : LeafIso 3043    := by decide +kernel
private theorem c3043_nof2  : NoF2ChkSq 3043  := by decide +kernel
private theorem c3043_nof3  : NoF3ChkSq 3043  := by decide +kernel
private theorem c3043_nof4z : NoF4zChkSq 3043 := by decide +kernel
theorem C'_3043 : C' 3043 :=
  ⟨c3043_sqf, c3043_range, c3043_ell, leafNSq_of_sq c3043_nsq, leafHAr_of_sq c3043_har,
   c3043_r, c3043_e', c3043_f1, leafS2_of_sq c3043_s2, leafS3_of_sq c3043_s3,
   c3043_iso, leafR8_of_sq c3043_nof2 c3043_nof3 c3043_nof4z⟩
theorem not_tile'_3043 (D : CongruentDissection 3043) : False :=
  not_tile_of_conditions' 3043 C'_3043 D

private theorem c3046_sqf   : LeafSqf 3046   := by decide +kernel
private theorem c3046_range : LeafRange 3046  := by decide +kernel
private theorem c3046_ell   : LeafEll 3046    := by decide +kernel
private theorem c3046_nsq   : NSqChkSq 3046   := by decide +kernel
private theorem c3046_har   : HArithChkSq 3046 := by decide +kernel
private theorem c3046_r     : LeafR 3046      := by decide +kernel
private theorem c3046_e'    : LeafE' 3046     := by decide +kernel
private theorem c3046_f1    : LeafF1 3046     := Or.inl (by decide)
private theorem c3046_s2    : S2ChkSq 3046    := by decide +kernel
private theorem c3046_s3    : S3ChkSq 3046    := by decide +kernel
private theorem c3046_iso   : LeafIso 3046    := by decide +kernel
private theorem c3046_nof2  : NoF2ChkSq 3046  := by decide +kernel
private theorem c3046_nof3  : NoF3ChkSq 3046  := by decide +kernel
private theorem c3046_nof4z : NoF4zChkSq 3046 := by decide +kernel
theorem C'_3046 : C' 3046 :=
  ⟨c3046_sqf, c3046_range, c3046_ell, leafNSq_of_sq c3046_nsq, leafHAr_of_sq c3046_har,
   c3046_r, c3046_e', c3046_f1, leafS2_of_sq c3046_s2, leafS3_of_sq c3046_s3,
   c3046_iso, leafR8_of_sq c3046_nof2 c3046_nof3 c3046_nof4z⟩
theorem not_tile'_3046 (D : CongruentDissection 3046) : False :=
  not_tile_of_conditions' 3046 C'_3046 D

private theorem c3047_sqf   : LeafSqf 3047   := by decide +kernel
private theorem c3047_range : LeafRange 3047  := by decide +kernel
private theorem c3047_ell   : LeafEll 3047    := by decide +kernel
private theorem c3047_nsq   : NSqChkSq 3047   := by decide +kernel
private theorem c3047_har   : HArithChkSq 3047 := by decide +kernel
private theorem c3047_r     : LeafR 3047      := by decide +kernel
private theorem c3047_e'    : LeafE' 3047     := by decide +kernel
private theorem c3047_f1    : LeafF1 3047     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3047_s2    : S2ChkSq 3047    := by decide +kernel
private theorem c3047_s3    : S3ChkSq 3047    := by decide +kernel
private theorem c3047_iso   : LeafIso 3047    := by decide +kernel
private theorem c3047_nof2  : NoF2ChkSq 3047  := by decide +kernel
private theorem c3047_nof3  : NoF3ChkSq 3047  := by decide +kernel
private theorem c3047_nof4z : NoF4zChkSq 3047 := by decide +kernel
theorem C'_3047 : C' 3047 :=
  ⟨c3047_sqf, c3047_range, c3047_ell, leafNSq_of_sq c3047_nsq, leafHAr_of_sq c3047_har,
   c3047_r, c3047_e', c3047_f1, leafS2_of_sq c3047_s2, leafS3_of_sq c3047_s3,
   c3047_iso, leafR8_of_sq c3047_nof2 c3047_nof3 c3047_nof4z⟩
theorem not_tile'_3047 (D : CongruentDissection 3047) : False :=
  not_tile_of_conditions' 3047 C'_3047 D

end Erdos634.Draft.AllN2

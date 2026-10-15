/- AllN2Check55: N = 2038, 2039, 2047, 2049, 2051
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2038_sqf   : LeafSqf 2038   := by decide +kernel
private theorem c2038_range : LeafRange 2038  := by decide +kernel
private theorem c2038_ell   : LeafEll 2038    := by decide +kernel
private theorem c2038_nsq   : NSqChkSq 2038   := by decide +kernel
private theorem c2038_har   : HArithChkSq 2038 := by decide +kernel
private theorem c2038_r     : LeafR 2038      := by decide +kernel
private theorem c2038_e'    : LeafE' 2038     := by decide +kernel
private theorem c2038_f1    : LeafF1 2038     := Or.inl (by decide)
private theorem c2038_s2    : S2ChkSq 2038    := by decide +kernel
private theorem c2038_s3    : S3ChkSq 2038    := by decide +kernel
private theorem c2038_iso   : LeafIso 2038    := by decide +kernel
private theorem c2038_nof2  : NoF2ChkSq 2038  := by decide +kernel
private theorem c2038_nof3  : NoF3ChkSq 2038  := by decide +kernel
private theorem c2038_nof4z : NoF4zChkSq 2038 := by decide +kernel
theorem C'_2038 : C' 2038 :=
  ⟨c2038_sqf, c2038_range, c2038_ell, leafNSq_of_sq c2038_nsq, leafHAr_of_sq c2038_har,
   c2038_r, c2038_e', c2038_f1, leafS2_of_sq c2038_s2, leafS3_of_sq c2038_s3,
   c2038_iso, leafR8_of_sq c2038_nof2 c2038_nof3 c2038_nof4z⟩
theorem not_tile'_2038 (D : CongruentDissection 2038) : False :=
  not_tile_of_conditions' 2038 C'_2038 D

private theorem c2039_sqf   : LeafSqf 2039   := by decide +kernel
private theorem c2039_range : LeafRange 2039  := by decide +kernel
private theorem c2039_ell   : LeafEll 2039    := by decide +kernel
private theorem c2039_nsq   : NSqChkSq 2039   := by decide +kernel
private theorem c2039_har   : HArithChkSq 2039 := by decide +kernel
private theorem c2039_r     : LeafR 2039      := by decide +kernel
private theorem c2039_e'    : LeafE' 2039     := by decide +kernel
private theorem c2039_f1    : LeafF1 2039     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2039_s2    : S2ChkSq 2039    := by decide +kernel
private theorem c2039_s3    : S3ChkSq 2039    := by decide +kernel
private theorem c2039_iso   : LeafIso 2039    := by decide +kernel
private theorem c2039_nof2  : NoF2ChkSq 2039  := by decide +kernel
private theorem c2039_nof3  : NoF3ChkSq 2039  := by decide +kernel
private theorem c2039_nof4z : NoF4zChkSq 2039 := by decide +kernel
theorem C'_2039 : C' 2039 :=
  ⟨c2039_sqf, c2039_range, c2039_ell, leafNSq_of_sq c2039_nsq, leafHAr_of_sq c2039_har,
   c2039_r, c2039_e', c2039_f1, leafS2_of_sq c2039_s2, leafS3_of_sq c2039_s3,
   c2039_iso, leafR8_of_sq c2039_nof2 c2039_nof3 c2039_nof4z⟩
theorem not_tile'_2039 (D : CongruentDissection 2039) : False :=
  not_tile_of_conditions' 2039 C'_2039 D

private theorem c2047_sqf   : LeafSqf 2047   := by decide +kernel
private theorem c2047_range : LeafRange 2047  := by decide +kernel
private theorem c2047_ell   : LeafEll 2047    := by decide +kernel
private theorem c2047_nsq   : NSqChkSq 2047   := by decide +kernel
private theorem c2047_har   : HArithChkSq 2047 := by decide +kernel
private theorem c2047_r     : LeafR 2047      := by decide +kernel
private theorem c2047_e'    : LeafE' 2047     := by decide +kernel
private theorem c2047_f1    : LeafF1 2047     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2047_s2    : S2ChkSq 2047    := by decide +kernel
private theorem c2047_s3    : S3ChkSq 2047    := by decide +kernel
private theorem c2047_iso   : LeafIso 2047    := by decide +kernel
private theorem c2047_nof2  : NoF2ChkSq 2047  := by decide +kernel
private theorem c2047_nof3  : NoF3ChkSq 2047  := by decide +kernel
private theorem c2047_nof4z : NoF4zChkSq 2047 := by decide +kernel
theorem C'_2047 : C' 2047 :=
  ⟨c2047_sqf, c2047_range, c2047_ell, leafNSq_of_sq c2047_nsq, leafHAr_of_sq c2047_har,
   c2047_r, c2047_e', c2047_f1, leafS2_of_sq c2047_s2, leafS3_of_sq c2047_s3,
   c2047_iso, leafR8_of_sq c2047_nof2 c2047_nof3 c2047_nof4z⟩
theorem not_tile'_2047 (D : CongruentDissection 2047) : False :=
  not_tile_of_conditions' 2047 C'_2047 D

private theorem c2049_sqf   : LeafSqf 2049   := by decide +kernel
private theorem c2049_range : LeafRange 2049  := by decide +kernel
private theorem c2049_ell   : LeafEll 2049    := by decide +kernel
private theorem c2049_nsq   : NSqChkSq 2049   := by decide +kernel
private theorem c2049_har   : HArithChkSq 2049 := by decide +kernel
private theorem c2049_r     : LeafR 2049      := by decide +kernel
private theorem c2049_e'    : LeafE' 2049     := by decide +kernel
private theorem c2049_f1    : LeafF1 2049     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2049_s2    : S2ChkSq 2049    := by decide +kernel
private theorem c2049_s3    : S3ChkSq 2049    := by decide +kernel
private theorem c2049_iso   : LeafIso 2049    := by decide +kernel
private theorem c2049_nof2  : NoF2ChkSq 2049  := by decide +kernel
private theorem c2049_nof3  : NoF3ChkSq 2049  := by decide +kernel
private theorem c2049_nof4z : NoF4zChkSq 2049 := by decide +kernel
theorem C'_2049 : C' 2049 :=
  ⟨c2049_sqf, c2049_range, c2049_ell, leafNSq_of_sq c2049_nsq, leafHAr_of_sq c2049_har,
   c2049_r, c2049_e', c2049_f1, leafS2_of_sq c2049_s2, leafS3_of_sq c2049_s3,
   c2049_iso, leafR8_of_sq c2049_nof2 c2049_nof3 c2049_nof4z⟩
theorem not_tile'_2049 (D : CongruentDissection 2049) : False :=
  not_tile_of_conditions' 2049 C'_2049 D

private theorem c2051_sqf   : LeafSqf 2051   := by decide +kernel
private theorem c2051_range : LeafRange 2051  := by decide +kernel
private theorem c2051_ell   : LeafEll 2051    := by decide +kernel
private theorem c2051_nsq   : NSqChkSq 2051   := by decide +kernel
private theorem c2051_har   : HArithChkSq 2051 := by decide +kernel
private theorem c2051_r     : LeafR 2051      := by decide +kernel
private theorem c2051_e'    : LeafE' 2051     := by decide +kernel
private theorem c2051_f1    : LeafF1 2051     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2051_s2    : S2ChkSq 2051    := by decide +kernel
private theorem c2051_s3    : S3ChkSq 2051    := by decide +kernel
private theorem c2051_iso   : LeafIso 2051    := by decide +kernel
private theorem c2051_nof2  : NoF2ChkSq 2051  := by decide +kernel
private theorem c2051_nof3  : NoF3ChkSq 2051  := by decide +kernel
private theorem c2051_nof4z : NoF4zChkSq 2051 := by decide +kernel
theorem C'_2051 : C' 2051 :=
  ⟨c2051_sqf, c2051_range, c2051_ell, leafNSq_of_sq c2051_nsq, leafHAr_of_sq c2051_har,
   c2051_r, c2051_e', c2051_f1, leafS2_of_sq c2051_s2, leafS3_of_sq c2051_s3,
   c2051_iso, leafR8_of_sq c2051_nof2 c2051_nof3 c2051_nof4z⟩
theorem not_tile'_2051 (D : CongruentDissection 2051) : False :=
  not_tile_of_conditions' 2051 C'_2051 D

end Erdos634.Draft.AllN2

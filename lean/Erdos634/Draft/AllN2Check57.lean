/- AllN2Check57: N = 2073, 2077, 2078, 2082, 2083
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2073_sqf   : LeafSqf 2073   := by decide +kernel
private theorem c2073_range : LeafRange 2073  := by decide +kernel
private theorem c2073_ell   : LeafEll 2073    := by decide +kernel
private theorem c2073_nsq   : NSqChkSq 2073   := by decide +kernel
private theorem c2073_har   : HArithChkSq 2073 := by decide +kernel
private theorem c2073_r     : LeafR 2073      := by decide +kernel
private theorem c2073_e'    : LeafE' 2073     := by decide +kernel
private theorem c2073_f1    : LeafF1 2073     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2073_s2    : S2ChkSq 2073    := by decide +kernel
private theorem c2073_s3    : S3ChkSq 2073    := by decide +kernel
private theorem c2073_iso   : LeafIso 2073    := by decide +kernel
private theorem c2073_nof2  : NoF2ChkSq 2073  := by decide +kernel
private theorem c2073_nof3  : NoF3ChkSq 2073  := by decide +kernel
private theorem c2073_nof4z : NoF4zChkSq 2073 := by decide +kernel
theorem C'_2073 : C' 2073 :=
  ⟨c2073_sqf, c2073_range, c2073_ell, leafNSq_of_sq c2073_nsq, leafHAr_of_sq c2073_har,
   c2073_r, c2073_e', c2073_f1, leafS2_of_sq c2073_s2, leafS3_of_sq c2073_s3,
   c2073_iso, leafR8_of_sq c2073_nof2 c2073_nof3 c2073_nof4z⟩
theorem not_tile'_2073 (D : CongruentDissection 2073) : False :=
  not_tile_of_conditions' 2073 C'_2073 D

private theorem c2077_sqf   : LeafSqf 2077   := by decide +kernel
private theorem c2077_range : LeafRange 2077  := by decide +kernel
private theorem c2077_ell   : LeafEll 2077    := by decide +kernel
private theorem c2077_nsq   : NSqChkSq 2077   := by decide +kernel
private theorem c2077_har   : HArithChkSq 2077 := by decide +kernel
private theorem c2077_r     : LeafR 2077      := by decide +kernel
private theorem c2077_e'    : LeafE' 2077     := by decide +kernel
private theorem c2077_f1    : LeafF1 2077     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2077_s2    : S2ChkSq 2077    := by decide +kernel
private theorem c2077_s3    : S3ChkSq 2077    := by decide +kernel
private theorem c2077_iso   : LeafIso 2077    := by decide +kernel
private theorem c2077_nof2  : NoF2ChkSq 2077  := by decide +kernel
private theorem c2077_nof3  : NoF3ChkSq 2077  := by decide +kernel
private theorem c2077_nof4z : NoF4zChkSq 2077 := by decide +kernel
theorem C'_2077 : C' 2077 :=
  ⟨c2077_sqf, c2077_range, c2077_ell, leafNSq_of_sq c2077_nsq, leafHAr_of_sq c2077_har,
   c2077_r, c2077_e', c2077_f1, leafS2_of_sq c2077_s2, leafS3_of_sq c2077_s3,
   c2077_iso, leafR8_of_sq c2077_nof2 c2077_nof3 c2077_nof4z⟩
theorem not_tile'_2077 (D : CongruentDissection 2077) : False :=
  not_tile_of_conditions' 2077 C'_2077 D

private theorem c2078_sqf   : LeafSqf 2078   := by decide +kernel
private theorem c2078_range : LeafRange 2078  := by decide +kernel
private theorem c2078_ell   : LeafEll 2078    := by decide +kernel
private theorem c2078_nsq   : NSqChkSq 2078   := by decide +kernel
private theorem c2078_har   : HArithChkSq 2078 := by decide +kernel
private theorem c2078_r     : LeafR 2078      := by decide +kernel
private theorem c2078_e'    : LeafE' 2078     := by decide +kernel
private theorem c2078_f1    : LeafF1 2078     := Or.inl (by decide)
private theorem c2078_s2    : S2ChkSq 2078    := by decide +kernel
private theorem c2078_s3    : S3ChkSq 2078    := by decide +kernel
private theorem c2078_iso   : LeafIso 2078    := by decide +kernel
private theorem c2078_nof2  : NoF2ChkSq 2078  := by decide +kernel
private theorem c2078_nof3  : NoF3ChkSq 2078  := by decide +kernel
private theorem c2078_nof4z : NoF4zChkSq 2078 := by decide +kernel
theorem C'_2078 : C' 2078 :=
  ⟨c2078_sqf, c2078_range, c2078_ell, leafNSq_of_sq c2078_nsq, leafHAr_of_sq c2078_har,
   c2078_r, c2078_e', c2078_f1, leafS2_of_sq c2078_s2, leafS3_of_sq c2078_s3,
   c2078_iso, leafR8_of_sq c2078_nof2 c2078_nof3 c2078_nof4z⟩
theorem not_tile'_2078 (D : CongruentDissection 2078) : False :=
  not_tile_of_conditions' 2078 C'_2078 D

private theorem c2082_sqf   : LeafSqf 2082   := by decide +kernel
private theorem c2082_range : LeafRange 2082  := by decide +kernel
private theorem c2082_ell   : LeafEll 2082    := by decide +kernel
private theorem c2082_nsq   : NSqChkSq 2082   := by decide +kernel
private theorem c2082_har   : HArithChkSq 2082 := by decide +kernel
private theorem c2082_r     : LeafR 2082      := by decide +kernel
private theorem c2082_e'    : LeafE' 2082     := by decide +kernel
private theorem c2082_f1    : LeafF1 2082     := Or.inl (by decide)
private theorem c2082_s2    : S2ChkSq 2082    := by decide +kernel
private theorem c2082_s3    : S3ChkSq 2082    := by decide +kernel
private theorem c2082_iso   : LeafIso 2082    := by decide +kernel
private theorem c2082_nof2  : NoF2ChkSq 2082  := by decide +kernel
private theorem c2082_nof3  : NoF3ChkSq 2082  := by decide +kernel
private theorem c2082_nof4z : NoF4zChkSq 2082 := by decide +kernel
theorem C'_2082 : C' 2082 :=
  ⟨c2082_sqf, c2082_range, c2082_ell, leafNSq_of_sq c2082_nsq, leafHAr_of_sq c2082_har,
   c2082_r, c2082_e', c2082_f1, leafS2_of_sq c2082_s2, leafS3_of_sq c2082_s3,
   c2082_iso, leafR8_of_sq c2082_nof2 c2082_nof3 c2082_nof4z⟩
theorem not_tile'_2082 (D : CongruentDissection 2082) : False :=
  not_tile_of_conditions' 2082 C'_2082 D

private theorem c2083_sqf   : LeafSqf 2083   := by decide +kernel
private theorem c2083_range : LeafRange 2083  := by decide +kernel
private theorem c2083_ell   : LeafEll 2083    := by decide +kernel
private theorem c2083_nsq   : NSqChkSq 2083   := by decide +kernel
private theorem c2083_har   : HArithChkSq 2083 := by decide +kernel
private theorem c2083_r     : LeafR 2083      := by decide +kernel
private theorem c2083_e'    : LeafE' 2083     := by decide +kernel
private theorem c2083_f1    : LeafF1 2083     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2083_s2    : S2ChkSq 2083    := by decide +kernel
private theorem c2083_s3    : S3ChkSq 2083    := by decide +kernel
private theorem c2083_iso   : LeafIso 2083    := by decide +kernel
private theorem c2083_nof2  : NoF2ChkSq 2083  := by decide +kernel
private theorem c2083_nof3  : NoF3ChkSq 2083  := by decide +kernel
private theorem c2083_nof4z : NoF4zChkSq 2083 := by decide +kernel
theorem C'_2083 : C' 2083 :=
  ⟨c2083_sqf, c2083_range, c2083_ell, leafNSq_of_sq c2083_nsq, leafHAr_of_sq c2083_har,
   c2083_r, c2083_e', c2083_f1, leafS2_of_sq c2083_s2, leafS3_of_sq c2083_s3,
   c2083_iso, leafR8_of_sq c2083_nof2 c2083_nof3 c2083_nof4z⟩
theorem not_tile'_2083 (D : CongruentDissection 2083) : False :=
  not_tile_of_conditions' 2083 C'_2083 D

end Erdos634.Draft.AllN2

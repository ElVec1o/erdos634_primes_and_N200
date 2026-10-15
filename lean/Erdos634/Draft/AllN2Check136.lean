/- AllN2Check136: N = 3070, 3071, 3073, 3079, 3082
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3070_sqf   : LeafSqf 3070   := by decide +kernel
private theorem c3070_range : LeafRange 3070  := by decide +kernel
private theorem c3070_ell   : LeafEll 3070    := by decide +kernel
private theorem c3070_nsq   : NSqChkSq 3070   := by decide +kernel
private theorem c3070_har   : HArithChkSq 3070 := by decide +kernel
private theorem c3070_r     : LeafR 3070      := by decide +kernel
private theorem c3070_e'    : LeafE' 3070     := by decide +kernel
private theorem c3070_f1    : LeafF1 3070     := Or.inl (by decide)
private theorem c3070_s2    : S2ChkSq 3070    := by decide +kernel
private theorem c3070_s3    : S3ChkSq 3070    := by decide +kernel
private theorem c3070_iso   : LeafIso 3070    := by decide +kernel
private theorem c3070_nof2  : NoF2ChkSq 3070  := by decide +kernel
private theorem c3070_nof3  : NoF3ChkSq 3070  := by decide +kernel
private theorem c3070_nof4z : NoF4zChkSq 3070 := by decide +kernel
theorem C'_3070 : C' 3070 :=
  ⟨c3070_sqf, c3070_range, c3070_ell, leafNSq_of_sq c3070_nsq, leafHAr_of_sq c3070_har,
   c3070_r, c3070_e', c3070_f1, leafS2_of_sq c3070_s2, leafS3_of_sq c3070_s3,
   c3070_iso, leafR8_of_sq c3070_nof2 c3070_nof3 c3070_nof4z⟩
theorem not_tile'_3070 (D : CongruentDissection 3070) : False :=
  not_tile_of_conditions' 3070 C'_3070 D

private theorem c3071_sqf   : LeafSqf 3071   := by decide +kernel
private theorem c3071_range : LeafRange 3071  := by decide +kernel
private theorem c3071_ell   : LeafEll 3071    := by decide +kernel
private theorem c3071_nsq   : NSqChkSq 3071   := by decide +kernel
private theorem c3071_har   : HArithChkSq 3071 := by decide +kernel
private theorem c3071_r     : LeafR 3071      := by decide +kernel
private theorem c3071_e'    : LeafE' 3071     := by decide +kernel
private theorem c3071_f1    : LeafF1 3071     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3071_s2    : S2ChkSq 3071    := by decide +kernel
private theorem c3071_s3    : S3ChkSq 3071    := by decide +kernel
private theorem c3071_iso   : LeafIso 3071    := by decide +kernel
private theorem c3071_nof2  : NoF2ChkSq 3071  := by decide +kernel
private theorem c3071_nof3  : NoF3ChkSq 3071  := by decide +kernel
private theorem c3071_nof4z : NoF4zChkSq 3071 := by decide +kernel
theorem C'_3071 : C' 3071 :=
  ⟨c3071_sqf, c3071_range, c3071_ell, leafNSq_of_sq c3071_nsq, leafHAr_of_sq c3071_har,
   c3071_r, c3071_e', c3071_f1, leafS2_of_sq c3071_s2, leafS3_of_sq c3071_s3,
   c3071_iso, leafR8_of_sq c3071_nof2 c3071_nof3 c3071_nof4z⟩
theorem not_tile'_3071 (D : CongruentDissection 3071) : False :=
  not_tile_of_conditions' 3071 C'_3071 D

private theorem c3073_sqf   : LeafSqf 3073   := by decide +kernel
private theorem c3073_range : LeafRange 3073  := by decide +kernel
private theorem c3073_ell   : LeafEll 3073    := by decide +kernel
private theorem c3073_nsq   : NSqChkSq 3073   := by decide +kernel
private theorem c3073_har   : HArithChkSq 3073 := by decide +kernel
private theorem c3073_r     : LeafR 3073      := by decide +kernel
private theorem c3073_e'    : LeafE' 3073     := by decide +kernel
private theorem c3073_f1    : LeafF1 3073     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3073_s2    : S2ChkSq 3073    := by decide +kernel
private theorem c3073_s3    : S3ChkSq 3073    := by decide +kernel
private theorem c3073_iso   : LeafIso 3073    := by decide +kernel
private theorem c3073_nof2  : NoF2ChkSq 3073  := by decide +kernel
private theorem c3073_nof3  : NoF3ChkSq 3073  := by decide +kernel
private theorem c3073_nof4z : NoF4zChkSq 3073 := by decide +kernel
theorem C'_3073 : C' 3073 :=
  ⟨c3073_sqf, c3073_range, c3073_ell, leafNSq_of_sq c3073_nsq, leafHAr_of_sq c3073_har,
   c3073_r, c3073_e', c3073_f1, leafS2_of_sq c3073_s2, leafS3_of_sq c3073_s3,
   c3073_iso, leafR8_of_sq c3073_nof2 c3073_nof3 c3073_nof4z⟩
theorem not_tile'_3073 (D : CongruentDissection 3073) : False :=
  not_tile_of_conditions' 3073 C'_3073 D

private theorem c3079_sqf   : LeafSqf 3079   := by decide +kernel
private theorem c3079_range : LeafRange 3079  := by decide +kernel
private theorem c3079_ell   : LeafEll 3079    := by decide +kernel
private theorem c3079_nsq   : NSqChkSq 3079   := by decide +kernel
private theorem c3079_har   : HArithChkSq 3079 := by decide +kernel
private theorem c3079_r     : LeafR 3079      := by decide +kernel
private theorem c3079_e'    : LeafE' 3079     := by decide +kernel
private theorem c3079_f1    : LeafF1 3079     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3079_s2    : S2ChkSq 3079    := by decide +kernel
private theorem c3079_s3    : S3ChkSq 3079    := by decide +kernel
private theorem c3079_iso   : LeafIso 3079    := by decide +kernel
private theorem c3079_nof2  : NoF2ChkSq 3079  := by decide +kernel
private theorem c3079_nof3  : NoF3ChkSq 3079  := by decide +kernel
private theorem c3079_nof4z : NoF4zChkSq 3079 := by decide +kernel
theorem C'_3079 : C' 3079 :=
  ⟨c3079_sqf, c3079_range, c3079_ell, leafNSq_of_sq c3079_nsq, leafHAr_of_sq c3079_har,
   c3079_r, c3079_e', c3079_f1, leafS2_of_sq c3079_s2, leafS3_of_sq c3079_s3,
   c3079_iso, leafR8_of_sq c3079_nof2 c3079_nof3 c3079_nof4z⟩
theorem not_tile'_3079 (D : CongruentDissection 3079) : False :=
  not_tile_of_conditions' 3079 C'_3079 D

private theorem c3082_sqf   : LeafSqf 3082   := by decide +kernel
private theorem c3082_range : LeafRange 3082  := by decide +kernel
private theorem c3082_ell   : LeafEll 3082    := by decide +kernel
private theorem c3082_nsq   : NSqChkSq 3082   := by decide +kernel
private theorem c3082_har   : HArithChkSq 3082 := by decide +kernel
private theorem c3082_r     : LeafR 3082      := by decide +kernel
private theorem c3082_e'    : LeafE' 3082     := by decide +kernel
private theorem c3082_f1    : LeafF1 3082     := Or.inl (by decide)
private theorem c3082_s2    : S2ChkSq 3082    := by decide +kernel
private theorem c3082_s3    : S3ChkSq 3082    := by decide +kernel
private theorem c3082_iso   : LeafIso 3082    := by decide +kernel
private theorem c3082_nof2  : NoF2ChkSq 3082  := by decide +kernel
private theorem c3082_nof3  : NoF3ChkSq 3082  := by decide +kernel
private theorem c3082_nof4z : NoF4zChkSq 3082 := by decide +kernel
theorem C'_3082 : C' 3082 :=
  ⟨c3082_sqf, c3082_range, c3082_ell, leafNSq_of_sq c3082_nsq, leafHAr_of_sq c3082_har,
   c3082_r, c3082_e', c3082_f1, leafS2_of_sq c3082_s2, leafS3_of_sq c3082_s3,
   c3082_iso, leafR8_of_sq c3082_nof2 c3082_nof3 c3082_nof4z⟩
theorem not_tile'_3082 (D : CongruentDissection 3082) : False :=
  not_tile_of_conditions' 3082 C'_3082 D

end Erdos634.Draft.AllN2

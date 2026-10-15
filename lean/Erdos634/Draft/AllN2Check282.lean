/- AllN2Check282: N = 4931, 4934, 4938, 4939, 4942
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4931_sqf   : LeafSqf 4931   := by decide +kernel
private theorem c4931_range : LeafRange 4931  := by decide +kernel
private theorem c4931_ell   : LeafEll 4931    := by decide +kernel
private theorem c4931_nsq   : NSqChkSq 4931   := by decide +kernel
private theorem c4931_har   : HArithChkSq 4931 := by decide +kernel
private theorem c4931_r     : LeafR 4931      := by decide +kernel
private theorem c4931_e'    : LeafE' 4931     := by decide +kernel
private theorem c4931_f1    : LeafF1 4931     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4931_s2    : S2ChkSq 4931    := by decide +kernel
private theorem c4931_s3    : S3ChkSq 4931    := by decide +kernel
private theorem c4931_iso   : LeafIso 4931    := by decide +kernel
private theorem c4931_nof2  : NoF2ChkSq 4931  := by decide +kernel
private theorem c4931_nof3  : NoF3ChkSq 4931  := by decide +kernel
private theorem c4931_nof4z : NoF4zChkSq 4931 := by decide +kernel
theorem C'_4931 : C' 4931 :=
  ⟨c4931_sqf, c4931_range, c4931_ell, leafNSq_of_sq c4931_nsq, leafHAr_of_sq c4931_har,
   c4931_r, c4931_e', c4931_f1, leafS2_of_sq c4931_s2, leafS3_of_sq c4931_s3,
   c4931_iso, leafR8_of_sq c4931_nof2 c4931_nof3 c4931_nof4z⟩
theorem not_tile'_4931 (D : CongruentDissection 4931) : False :=
  not_tile_of_conditions' 4931 C'_4931 D

private theorem c4934_sqf   : LeafSqf 4934   := by decide +kernel
private theorem c4934_range : LeafRange 4934  := by decide +kernel
private theorem c4934_ell   : LeafEll 4934    := by decide +kernel
private theorem c4934_nsq   : NSqChkSq 4934   := by decide +kernel
private theorem c4934_har   : HArithChkSq 4934 := by decide +kernel
private theorem c4934_r     : LeafR 4934      := by decide +kernel
private theorem c4934_e'    : LeafE' 4934     := by decide +kernel
private theorem c4934_f1    : LeafF1 4934     := Or.inl (by decide)
private theorem c4934_s2    : S2ChkSq 4934    := by decide +kernel
private theorem c4934_s3    : S3ChkSq 4934    := by decide +kernel
private theorem c4934_iso   : LeafIso 4934    := by decide +kernel
private theorem c4934_nof2  : NoF2ChkSq 4934  := by decide +kernel
private theorem c4934_nof3  : NoF3ChkSq 4934  := by decide +kernel
private theorem c4934_nof4z : NoF4zChkSq 4934 := by decide +kernel
theorem C'_4934 : C' 4934 :=
  ⟨c4934_sqf, c4934_range, c4934_ell, leafNSq_of_sq c4934_nsq, leafHAr_of_sq c4934_har,
   c4934_r, c4934_e', c4934_f1, leafS2_of_sq c4934_s2, leafS3_of_sq c4934_s3,
   c4934_iso, leafR8_of_sq c4934_nof2 c4934_nof3 c4934_nof4z⟩
theorem not_tile'_4934 (D : CongruentDissection 4934) : False :=
  not_tile_of_conditions' 4934 C'_4934 D

private theorem c4938_sqf   : LeafSqf 4938   := by decide +kernel
private theorem c4938_range : LeafRange 4938  := by decide +kernel
private theorem c4938_ell   : LeafEll 4938    := by decide +kernel
private theorem c4938_nsq   : NSqChkSq 4938   := by decide +kernel
private theorem c4938_har   : HArithChkSq 4938 := by decide +kernel
private theorem c4938_r     : LeafR 4938      := by decide +kernel
private theorem c4938_e'    : LeafE' 4938     := by decide +kernel
private theorem c4938_f1    : LeafF1 4938     := Or.inl (by decide)
private theorem c4938_s2    : S2ChkSq 4938    := by decide +kernel
private theorem c4938_s3    : S3ChkSq 4938    := by decide +kernel
private theorem c4938_iso   : LeafIso 4938    := by decide +kernel
private theorem c4938_nof2  : NoF2ChkSq 4938  := by decide +kernel
private theorem c4938_nof3  : NoF3ChkSq 4938  := by decide +kernel
private theorem c4938_nof4z : NoF4zChkSq 4938 := by decide +kernel
theorem C'_4938 : C' 4938 :=
  ⟨c4938_sqf, c4938_range, c4938_ell, leafNSq_of_sq c4938_nsq, leafHAr_of_sq c4938_har,
   c4938_r, c4938_e', c4938_f1, leafS2_of_sq c4938_s2, leafS3_of_sq c4938_s3,
   c4938_iso, leafR8_of_sq c4938_nof2 c4938_nof3 c4938_nof4z⟩
theorem not_tile'_4938 (D : CongruentDissection 4938) : False :=
  not_tile_of_conditions' 4938 C'_4938 D

private theorem c4939_sqf   : LeafSqf 4939   := by decide +kernel
private theorem c4939_range : LeafRange 4939  := by decide +kernel
private theorem c4939_ell   : LeafEll 4939    := by decide +kernel
private theorem c4939_nsq   : NSqChkSq 4939   := by decide +kernel
private theorem c4939_har   : HArithChkSq 4939 := by decide +kernel
private theorem c4939_r     : LeafR 4939      := by decide +kernel
private theorem c4939_e'    : LeafE' 4939     := by decide +kernel
private theorem c4939_f1    : LeafF1 4939     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4939_s2    : S2ChkSq 4939    := by decide +kernel
private theorem c4939_s3    : S3ChkSq 4939    := by decide +kernel
private theorem c4939_iso   : LeafIso 4939    := by decide +kernel
private theorem c4939_nof2  : NoF2ChkSq 4939  := by decide +kernel
private theorem c4939_nof3  : NoF3ChkSq 4939  := by decide +kernel
private theorem c4939_nof4z : NoF4zChkSq 4939 := by decide +kernel
theorem C'_4939 : C' 4939 :=
  ⟨c4939_sqf, c4939_range, c4939_ell, leafNSq_of_sq c4939_nsq, leafHAr_of_sq c4939_har,
   c4939_r, c4939_e', c4939_f1, leafS2_of_sq c4939_s2, leafS3_of_sq c4939_s3,
   c4939_iso, leafR8_of_sq c4939_nof2 c4939_nof3 c4939_nof4z⟩
theorem not_tile'_4939 (D : CongruentDissection 4939) : False :=
  not_tile_of_conditions' 4939 C'_4939 D

private theorem c4942_sqf   : LeafSqf 4942   := by decide +kernel
private theorem c4942_range : LeafRange 4942  := by decide +kernel
private theorem c4942_ell   : LeafEll 4942    := by decide +kernel
private theorem c4942_nsq   : NSqChkSq 4942   := by decide +kernel
private theorem c4942_har   : HArithChkSq 4942 := by decide +kernel
private theorem c4942_r     : LeafR 4942      := by decide +kernel
private theorem c4942_e'    : LeafE' 4942     := by decide +kernel
private theorem c4942_f1    : LeafF1 4942     := Or.inl (by decide)
private theorem c4942_s2    : S2ChkSq 4942    := by decide +kernel
private theorem c4942_s3    : S3ChkSq 4942    := by decide +kernel
private theorem c4942_iso   : LeafIso 4942    := by decide +kernel
private theorem c4942_nof2  : NoF2ChkSq 4942  := by decide +kernel
private theorem c4942_nof3  : NoF3ChkSq 4942  := by decide +kernel
private theorem c4942_nof4z : NoF4zChkSq 4942 := by decide +kernel
theorem C'_4942 : C' 4942 :=
  ⟨c4942_sqf, c4942_range, c4942_ell, leafNSq_of_sq c4942_nsq, leafHAr_of_sq c4942_har,
   c4942_r, c4942_e', c4942_f1, leafS2_of_sq c4942_s2, leafS3_of_sq c4942_s3,
   c4942_iso, leafR8_of_sq c4942_nof2 c4942_nof3 c4942_nof4z⟩
theorem not_tile'_4942 (D : CongruentDissection 4942) : False :=
  not_tile_of_conditions' 4942 C'_4942 D

end Erdos634.Draft.AllN2

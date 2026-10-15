/- AllN2Check125: N = 2933, 2935, 2939, 2942, 2945
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2933_sqf   : LeafSqf 2933   := by decide +kernel
private theorem c2933_range : LeafRange 2933  := by decide +kernel
private theorem c2933_ell   : LeafEll 2933    := by decide +kernel
private theorem c2933_nsq   : NSqChkSq 2933   := by decide +kernel
private theorem c2933_har   : HArithChkSq 2933 := by decide +kernel
private theorem c2933_r     : LeafR 2933      := by decide +kernel
private theorem c2933_e'    : LeafE' 2933     := by decide +kernel
private theorem c2933_f1    : LeafF1 2933     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2933_s2    : S2ChkSq 2933    := by decide +kernel
private theorem c2933_s3    : S3ChkSq 2933    := by decide +kernel
private theorem c2933_iso   : LeafIso 2933    := by decide +kernel
private theorem c2933_nof2  : NoF2ChkSq 2933  := by decide +kernel
private theorem c2933_nof3  : NoF3ChkSq 2933  := by decide +kernel
private theorem c2933_nof4z : NoF4zChkSq 2933 := by decide +kernel
theorem C'_2933 : C' 2933 :=
  ⟨c2933_sqf, c2933_range, c2933_ell, leafNSq_of_sq c2933_nsq, leafHAr_of_sq c2933_har,
   c2933_r, c2933_e', c2933_f1, leafS2_of_sq c2933_s2, leafS3_of_sq c2933_s3,
   c2933_iso, leafR8_of_sq c2933_nof2 c2933_nof3 c2933_nof4z⟩
theorem not_tile'_2933 (D : CongruentDissection 2933) : False :=
  not_tile_of_conditions' 2933 C'_2933 D

private theorem c2935_sqf   : LeafSqf 2935   := by decide +kernel
private theorem c2935_range : LeafRange 2935  := by decide +kernel
private theorem c2935_ell   : LeafEll 2935    := by decide +kernel
private theorem c2935_nsq   : NSqChkSq 2935   := by decide +kernel
private theorem c2935_har   : HArithChkSq 2935 := by decide +kernel
private theorem c2935_r     : LeafR 2935      := by decide +kernel
private theorem c2935_e'    : LeafE' 2935     := by decide +kernel
private theorem c2935_f1    : LeafF1 2935     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2935_s2    : S2ChkSq 2935    := by decide +kernel
private theorem c2935_s3    : S3ChkSq 2935    := by decide +kernel
private theorem c2935_iso   : LeafIso 2935    := by decide +kernel
private theorem c2935_nof2  : NoF2ChkSq 2935  := by decide +kernel
private theorem c2935_nof3  : NoF3ChkSq 2935  := by decide +kernel
private theorem c2935_nof4z : NoF4zChkSq 2935 := by decide +kernel
theorem C'_2935 : C' 2935 :=
  ⟨c2935_sqf, c2935_range, c2935_ell, leafNSq_of_sq c2935_nsq, leafHAr_of_sq c2935_har,
   c2935_r, c2935_e', c2935_f1, leafS2_of_sq c2935_s2, leafS3_of_sq c2935_s3,
   c2935_iso, leafR8_of_sq c2935_nof2 c2935_nof3 c2935_nof4z⟩
theorem not_tile'_2935 (D : CongruentDissection 2935) : False :=
  not_tile_of_conditions' 2935 C'_2935 D

private theorem c2939_sqf   : LeafSqf 2939   := by decide +kernel
private theorem c2939_range : LeafRange 2939  := by decide +kernel
private theorem c2939_ell   : LeafEll 2939    := by decide +kernel
private theorem c2939_nsq   : NSqChkSq 2939   := by decide +kernel
private theorem c2939_har   : HArithChkSq 2939 := by decide +kernel
private theorem c2939_r     : LeafR 2939      := by decide +kernel
private theorem c2939_e'    : LeafE' 2939     := by decide +kernel
private theorem c2939_f1    : LeafF1 2939     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2939_s2    : S2ChkSq 2939    := by decide +kernel
private theorem c2939_s3    : S3ChkSq 2939    := by decide +kernel
private theorem c2939_iso   : LeafIso 2939    := by decide +kernel
private theorem c2939_nof2  : NoF2ChkSq 2939  := by decide +kernel
private theorem c2939_nof3  : NoF3ChkSq 2939  := by decide +kernel
private theorem c2939_nof4z : NoF4zChkSq 2939 := by decide +kernel
theorem C'_2939 : C' 2939 :=
  ⟨c2939_sqf, c2939_range, c2939_ell, leafNSq_of_sq c2939_nsq, leafHAr_of_sq c2939_har,
   c2939_r, c2939_e', c2939_f1, leafS2_of_sq c2939_s2, leafS3_of_sq c2939_s3,
   c2939_iso, leafR8_of_sq c2939_nof2 c2939_nof3 c2939_nof4z⟩
theorem not_tile'_2939 (D : CongruentDissection 2939) : False :=
  not_tile_of_conditions' 2939 C'_2939 D

private theorem c2942_sqf   : LeafSqf 2942   := by decide +kernel
private theorem c2942_range : LeafRange 2942  := by decide +kernel
private theorem c2942_ell   : LeafEll 2942    := by decide +kernel
private theorem c2942_nsq   : NSqChkSq 2942   := by decide +kernel
private theorem c2942_har   : HArithChkSq 2942 := by decide +kernel
private theorem c2942_r     : LeafR 2942      := by decide +kernel
private theorem c2942_e'    : LeafE' 2942     := by decide +kernel
private theorem c2942_f1    : LeafF1 2942     := Or.inl (by decide)
private theorem c2942_s2    : S2ChkSq 2942    := by decide +kernel
private theorem c2942_s3    : S3ChkSq 2942    := by decide +kernel
private theorem c2942_iso   : LeafIso 2942    := by decide +kernel
private theorem c2942_nof2  : NoF2ChkSq 2942  := by decide +kernel
private theorem c2942_nof3  : NoF3ChkSq 2942  := by decide +kernel
private theorem c2942_nof4z : NoF4zChkSq 2942 := by decide +kernel
theorem C'_2942 : C' 2942 :=
  ⟨c2942_sqf, c2942_range, c2942_ell, leafNSq_of_sq c2942_nsq, leafHAr_of_sq c2942_har,
   c2942_r, c2942_e', c2942_f1, leafS2_of_sq c2942_s2, leafS3_of_sq c2942_s3,
   c2942_iso, leafR8_of_sq c2942_nof2 c2942_nof3 c2942_nof4z⟩
theorem not_tile'_2942 (D : CongruentDissection 2942) : False :=
  not_tile_of_conditions' 2942 C'_2942 D

private theorem c2945_sqf   : LeafSqf 2945   := by decide +kernel
private theorem c2945_range : LeafRange 2945  := by decide +kernel
private theorem c2945_ell   : LeafEll 2945    := by decide +kernel
private theorem c2945_nsq   : NSqChkSq 2945   := by decide +kernel
private theorem c2945_har   : HArithChkSq 2945 := by decide +kernel
private theorem c2945_r     : LeafR 2945      := by decide +kernel
private theorem c2945_e'    : LeafE' 2945     := by decide +kernel
private theorem c2945_f1    : LeafF1 2945     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2945_s2    : S2ChkSq 2945    := by decide +kernel
private theorem c2945_s3    : S3ChkSq 2945    := by decide +kernel
private theorem c2945_iso   : LeafIso 2945    := by decide +kernel
private theorem c2945_nof2  : NoF2ChkSq 2945  := by decide +kernel
private theorem c2945_nof3  : NoF3ChkSq 2945  := by decide +kernel
private theorem c2945_nof4z : NoF4zChkSq 2945 := by decide +kernel
theorem C'_2945 : C' 2945 :=
  ⟨c2945_sqf, c2945_range, c2945_ell, leafNSq_of_sq c2945_nsq, leafHAr_of_sq c2945_har,
   c2945_r, c2945_e', c2945_f1, leafS2_of_sq c2945_s2, leafS3_of_sq c2945_s3,
   c2945_iso, leafR8_of_sq c2945_nof2 c2945_nof3 c2945_nof4z⟩
theorem not_tile'_2945 (D : CongruentDissection 2945) : False :=
  not_tile_of_conditions' 2945 C'_2945 D

end Erdos634.Draft.AllN2

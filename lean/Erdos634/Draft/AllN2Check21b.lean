/- AllN2Check21b: N = 939, 951, 955, 957, 959.
   C' N = true for each. Not in any realizable family. No sorry, no native_decide. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c939_sqf   : LeafSqf 939   := by decide +kernel
private theorem c939_range : LeafRange 939  := by decide +kernel
private theorem c939_ell   : LeafEll 939    := by decide +kernel
private theorem c939_nsq   : NSqChkSq 939   := by decide +kernel
private theorem c939_har   : HArithChkSq 939 := by decide +kernel
private theorem c939_r     : LeafR 939      := by decide +kernel
private theorem c939_e'    : LeafE' 939     := by decide +kernel
private theorem c939_f1    : LeafF1 939     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c939_s2    : S2ChkSq 939    := by decide +kernel
private theorem c939_s3    : S3ChkSq 939    := by decide +kernel
private theorem c939_iso   : LeafIso 939    := by decide +kernel
private theorem c939_nof2  : NoF2ChkSq 939  := by decide +kernel
private theorem c939_nof3  : NoF3ChkSq 939  := by decide +kernel
private theorem c939_nof4z : NoF4zChkSq 939 := by decide +kernel
theorem C'_939 : C' 939 :=
  ⟨c939_sqf, c939_range, c939_ell, leafNSq_of_sq c939_nsq, leafHAr_of_sq c939_har,
   c939_r, c939_e', c939_f1, leafS2_of_sq c939_s2, leafS3_of_sq c939_s3,
   c939_iso, leafR8_of_sq c939_nof2 c939_nof3 c939_nof4z⟩
theorem not_tile'_939 (D : CongruentDissection 939) : False :=
  not_tile_of_conditions' 939 C'_939 D

private theorem c951_sqf   : LeafSqf 951   := by decide +kernel
private theorem c951_range : LeafRange 951  := by decide +kernel
private theorem c951_ell   : LeafEll 951    := by decide +kernel
private theorem c951_nsq   : NSqChkSq 951   := by decide +kernel
private theorem c951_har   : HArithChkSq 951 := by decide +kernel
private theorem c951_r     : LeafR 951      := by decide +kernel
private theorem c951_e'    : LeafE' 951     := by decide +kernel
private theorem c951_f1    : LeafF1 951     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c951_s2    : S2ChkSq 951    := by decide +kernel
private theorem c951_s3    : S3ChkSq 951    := by decide +kernel
private theorem c951_iso   : LeafIso 951    := by decide +kernel
private theorem c951_nof2  : NoF2ChkSq 951  := by decide +kernel
private theorem c951_nof3  : NoF3ChkSq 951  := by decide +kernel
private theorem c951_nof4z : NoF4zChkSq 951 := by decide +kernel
theorem C'_951 : C' 951 :=
  ⟨c951_sqf, c951_range, c951_ell, leafNSq_of_sq c951_nsq, leafHAr_of_sq c951_har,
   c951_r, c951_e', c951_f1, leafS2_of_sq c951_s2, leafS3_of_sq c951_s3,
   c951_iso, leafR8_of_sq c951_nof2 c951_nof3 c951_nof4z⟩
theorem not_tile'_951 (D : CongruentDissection 951) : False :=
  not_tile_of_conditions' 951 C'_951 D

private theorem c955_sqf   : LeafSqf 955   := by decide +kernel
private theorem c955_range : LeafRange 955  := by decide +kernel
private theorem c955_ell   : LeafEll 955    := by decide +kernel
private theorem c955_nsq   : NSqChkSq 955   := by decide +kernel
private theorem c955_har   : HArithChkSq 955 := by decide +kernel
private theorem c955_r     : LeafR 955      := by decide +kernel
private theorem c955_e'    : LeafE' 955     := by decide +kernel
private theorem c955_f1    : LeafF1 955     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c955_s2    : S2ChkSq 955    := by decide +kernel
private theorem c955_s3    : S3ChkSq 955    := by decide +kernel
private theorem c955_iso   : LeafIso 955    := by decide +kernel
private theorem c955_nof2  : NoF2ChkSq 955  := by decide +kernel
private theorem c955_nof3  : NoF3ChkSq 955  := by decide +kernel
private theorem c955_nof4z : NoF4zChkSq 955 := by decide +kernel
theorem C'_955 : C' 955 :=
  ⟨c955_sqf, c955_range, c955_ell, leafNSq_of_sq c955_nsq, leafHAr_of_sq c955_har,
   c955_r, c955_e', c955_f1, leafS2_of_sq c955_s2, leafS3_of_sq c955_s3,
   c955_iso, leafR8_of_sq c955_nof2 c955_nof3 c955_nof4z⟩
theorem not_tile'_955 (D : CongruentDissection 955) : False :=
  not_tile_of_conditions' 955 C'_955 D

private theorem c957_sqf   : LeafSqf 957   := by decide +kernel
private theorem c957_range : LeafRange 957  := by decide +kernel
private theorem c957_ell   : LeafEll 957    := by decide +kernel
private theorem c957_nsq   : NSqChkSq 957   := by decide +kernel
private theorem c957_har   : HArithChkSq 957 := by decide +kernel
private theorem c957_r     : LeafR 957      := by decide +kernel
private theorem c957_e'    : LeafE' 957     := by decide +kernel
private theorem c957_f1    : LeafF1 957     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c957_s2    : S2ChkSq 957    := by decide +kernel
private theorem c957_s3    : S3ChkSq 957    := by decide +kernel
private theorem c957_iso   : LeafIso 957    := by decide +kernel
private theorem c957_nof2  : NoF2ChkSq 957  := by decide +kernel
private theorem c957_nof3  : NoF3ChkSq 957  := by decide +kernel
private theorem c957_nof4z : NoF4zChkSq 957 := by decide +kernel
theorem C'_957 : C' 957 :=
  ⟨c957_sqf, c957_range, c957_ell, leafNSq_of_sq c957_nsq, leafHAr_of_sq c957_har,
   c957_r, c957_e', c957_f1, leafS2_of_sq c957_s2, leafS3_of_sq c957_s3,
   c957_iso, leafR8_of_sq c957_nof2 c957_nof3 c957_nof4z⟩
theorem not_tile'_957 (D : CongruentDissection 957) : False :=
  not_tile_of_conditions' 957 C'_957 D

private theorem c959_sqf   : LeafSqf 959   := by decide +kernel
private theorem c959_range : LeafRange 959  := by decide +kernel
private theorem c959_ell   : LeafEll 959    := by decide +kernel
private theorem c959_nsq   : NSqChkSq 959   := by decide +kernel
private theorem c959_har   : HArithChkSq 959 := by decide +kernel
private theorem c959_r     : LeafR 959      := by decide +kernel
private theorem c959_e'    : LeafE' 959     := by decide +kernel
private theorem c959_f1    : LeafF1 959     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c959_s2    : S2ChkSq 959    := by decide +kernel
private theorem c959_s3    : S3ChkSq 959    := by decide +kernel
private theorem c959_iso   : LeafIso 959    := by decide +kernel
private theorem c959_nof2  : NoF2ChkSq 959  := by decide +kernel
private theorem c959_nof3  : NoF3ChkSq 959  := by decide +kernel
private theorem c959_nof4z : NoF4zChkSq 959 := by decide +kernel
theorem C'_959 : C' 959 :=
  ⟨c959_sqf, c959_range, c959_ell, leafNSq_of_sq c959_nsq, leafHAr_of_sq c959_har,
   c959_r, c959_e', c959_f1, leafS2_of_sq c959_s2, leafS3_of_sq c959_s3,
   c959_iso, leafR8_of_sq c959_nof2 c959_nof3 c959_nof4z⟩
theorem not_tile'_959 (D : CongruentDissection 959) : False :=
  not_tile_of_conditions' 959 C'_959 D

end Erdos634.Draft.AllN2

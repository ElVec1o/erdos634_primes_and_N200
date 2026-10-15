/- AllN2Check49: N = 1939, 1941, 1955, 1959, 1963
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1939_sqf   : LeafSqf 1939   := by decide +kernel
private theorem c1939_range : LeafRange 1939  := by decide +kernel
private theorem c1939_ell   : LeafEll 1939    := by decide +kernel
private theorem c1939_nsq   : NSqChkSq 1939   := by decide +kernel
private theorem c1939_har   : HArithChkSq 1939 := by decide +kernel
private theorem c1939_r     : LeafR 1939      := by decide +kernel
private theorem c1939_e'    : LeafE' 1939     := by decide +kernel
private theorem c1939_f1    : LeafF1 1939     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1939_s2    : S2ChkSq 1939    := by decide +kernel
private theorem c1939_s3    : S3ChkSq 1939    := by decide +kernel
private theorem c1939_iso   : LeafIso 1939    := by decide +kernel
private theorem c1939_nof2  : NoF2ChkSq 1939  := by decide +kernel
private theorem c1939_nof3  : NoF3ChkSq 1939  := by decide +kernel
private theorem c1939_nof4z : NoF4zChkSq 1939 := by decide +kernel
theorem C'_1939 : C' 1939 :=
  ⟨c1939_sqf, c1939_range, c1939_ell, leafNSq_of_sq c1939_nsq, leafHAr_of_sq c1939_har,
   c1939_r, c1939_e', c1939_f1, leafS2_of_sq c1939_s2, leafS3_of_sq c1939_s3,
   c1939_iso, leafR8_of_sq c1939_nof2 c1939_nof3 c1939_nof4z⟩
theorem not_tile'_1939 (D : CongruentDissection 1939) : False :=
  not_tile_of_conditions' 1939 C'_1939 D

private theorem c1941_sqf   : LeafSqf 1941   := by decide +kernel
private theorem c1941_range : LeafRange 1941  := by decide +kernel
private theorem c1941_ell   : LeafEll 1941    := by decide +kernel
private theorem c1941_nsq   : NSqChkSq 1941   := by decide +kernel
private theorem c1941_har   : HArithChkSq 1941 := by decide +kernel
private theorem c1941_r     : LeafR 1941      := by decide +kernel
private theorem c1941_e'    : LeafE' 1941     := by decide +kernel
private theorem c1941_f1    : LeafF1 1941     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1941_s2    : S2ChkSq 1941    := by decide +kernel
private theorem c1941_s3    : S3ChkSq 1941    := by decide +kernel
private theorem c1941_iso   : LeafIso 1941    := by decide +kernel
private theorem c1941_nof2  : NoF2ChkSq 1941  := by decide +kernel
private theorem c1941_nof3  : NoF3ChkSq 1941  := by decide +kernel
private theorem c1941_nof4z : NoF4zChkSq 1941 := by decide +kernel
theorem C'_1941 : C' 1941 :=
  ⟨c1941_sqf, c1941_range, c1941_ell, leafNSq_of_sq c1941_nsq, leafHAr_of_sq c1941_har,
   c1941_r, c1941_e', c1941_f1, leafS2_of_sq c1941_s2, leafS3_of_sq c1941_s3,
   c1941_iso, leafR8_of_sq c1941_nof2 c1941_nof3 c1941_nof4z⟩
theorem not_tile'_1941 (D : CongruentDissection 1941) : False :=
  not_tile_of_conditions' 1941 C'_1941 D

private theorem c1955_sqf   : LeafSqf 1955   := by decide +kernel
private theorem c1955_range : LeafRange 1955  := by decide +kernel
private theorem c1955_ell   : LeafEll 1955    := by decide +kernel
private theorem c1955_nsq   : NSqChkSq 1955   := by decide +kernel
private theorem c1955_har   : HArithChkSq 1955 := by decide +kernel
private theorem c1955_r     : LeafR 1955      := by decide +kernel
private theorem c1955_e'    : LeafE' 1955     := by decide +kernel
private theorem c1955_f1    : LeafF1 1955     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1955_s2    : S2ChkSq 1955    := by decide +kernel
private theorem c1955_s3    : S3ChkSq 1955    := by decide +kernel
private theorem c1955_iso   : LeafIso 1955    := by decide +kernel
private theorem c1955_nof2  : NoF2ChkSq 1955  := by decide +kernel
private theorem c1955_nof3  : NoF3ChkSq 1955  := by decide +kernel
private theorem c1955_nof4z : NoF4zChkSq 1955 := by decide +kernel
theorem C'_1955 : C' 1955 :=
  ⟨c1955_sqf, c1955_range, c1955_ell, leafNSq_of_sq c1955_nsq, leafHAr_of_sq c1955_har,
   c1955_r, c1955_e', c1955_f1, leafS2_of_sq c1955_s2, leafS3_of_sq c1955_s3,
   c1955_iso, leafR8_of_sq c1955_nof2 c1955_nof3 c1955_nof4z⟩
theorem not_tile'_1955 (D : CongruentDissection 1955) : False :=
  not_tile_of_conditions' 1955 C'_1955 D

private theorem c1959_sqf   : LeafSqf 1959   := by decide +kernel
private theorem c1959_range : LeafRange 1959  := by decide +kernel
private theorem c1959_ell   : LeafEll 1959    := by decide +kernel
private theorem c1959_nsq   : NSqChkSq 1959   := by decide +kernel
private theorem c1959_har   : HArithChkSq 1959 := by decide +kernel
private theorem c1959_r     : LeafR 1959      := by decide +kernel
private theorem c1959_e'    : LeafE' 1959     := by decide +kernel
private theorem c1959_f1    : LeafF1 1959     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1959_s2    : S2ChkSq 1959    := by decide +kernel
private theorem c1959_s3    : S3ChkSq 1959    := by decide +kernel
private theorem c1959_iso   : LeafIso 1959    := by decide +kernel
private theorem c1959_nof2  : NoF2ChkSq 1959  := by decide +kernel
private theorem c1959_nof3  : NoF3ChkSq 1959  := by decide +kernel
private theorem c1959_nof4z : NoF4zChkSq 1959 := by decide +kernel
theorem C'_1959 : C' 1959 :=
  ⟨c1959_sqf, c1959_range, c1959_ell, leafNSq_of_sq c1959_nsq, leafHAr_of_sq c1959_har,
   c1959_r, c1959_e', c1959_f1, leafS2_of_sq c1959_s2, leafS3_of_sq c1959_s3,
   c1959_iso, leafR8_of_sq c1959_nof2 c1959_nof3 c1959_nof4z⟩
theorem not_tile'_1959 (D : CongruentDissection 1959) : False :=
  not_tile_of_conditions' 1959 C'_1959 D

private theorem c1963_sqf   : LeafSqf 1963   := by decide +kernel
private theorem c1963_range : LeafRange 1963  := by decide +kernel
private theorem c1963_ell   : LeafEll 1963    := by decide +kernel
private theorem c1963_nsq   : NSqChkSq 1963   := by decide +kernel
private theorem c1963_har   : HArithChkSq 1963 := by decide +kernel
private theorem c1963_r     : LeafR 1963      := by decide +kernel
private theorem c1963_e'    : LeafE' 1963     := by decide +kernel
private theorem c1963_f1    : LeafF1 1963     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1963_s2    : S2ChkSq 1963    := by decide +kernel
private theorem c1963_s3    : S3ChkSq 1963    := by decide +kernel
private theorem c1963_iso   : LeafIso 1963    := by decide +kernel
private theorem c1963_nof2  : NoF2ChkSq 1963  := by decide +kernel
private theorem c1963_nof3  : NoF3ChkSq 1963  := by decide +kernel
private theorem c1963_nof4z : NoF4zChkSq 1963 := by decide +kernel
theorem C'_1963 : C' 1963 :=
  ⟨c1963_sqf, c1963_range, c1963_ell, leafNSq_of_sq c1963_nsq, leafHAr_of_sq c1963_har,
   c1963_r, c1963_e', c1963_f1, leafS2_of_sq c1963_s2, leafS3_of_sq c1963_s3,
   c1963_iso, leafR8_of_sq c1963_nof2 c1963_nof3 c1963_nof4z⟩
theorem not_tile'_1963 (D : CongruentDissection 1963) : False :=
  not_tile_of_conditions' 1963 C'_1963 D

end Erdos634.Draft.AllN2

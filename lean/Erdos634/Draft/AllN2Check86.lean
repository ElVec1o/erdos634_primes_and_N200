/- AllN2Check86: N = 2446, 2447, 2449, 2451, 2453
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2446_sqf   : LeafSqf 2446   := by decide +kernel
private theorem c2446_range : LeafRange 2446  := by decide +kernel
private theorem c2446_ell   : LeafEll 2446    := by decide +kernel
private theorem c2446_nsq   : NSqChkSq 2446   := by decide +kernel
private theorem c2446_har   : HArithChkSq 2446 := by decide +kernel
private theorem c2446_r     : LeafR 2446      := by decide +kernel
private theorem c2446_e'    : LeafE' 2446     := by decide +kernel
private theorem c2446_f1    : LeafF1 2446     := Or.inl (by decide)
private theorem c2446_s2    : S2ChkSq 2446    := by decide +kernel
private theorem c2446_s3    : S3ChkSq 2446    := by decide +kernel
private theorem c2446_iso   : LeafIso 2446    := by decide +kernel
private theorem c2446_nof2  : NoF2ChkSq 2446  := by decide +kernel
private theorem c2446_nof3  : NoF3ChkSq 2446  := by decide +kernel
private theorem c2446_nof4z : NoF4zChkSq 2446 := by decide +kernel
theorem C'_2446 : C' 2446 :=
  ⟨c2446_sqf, c2446_range, c2446_ell, leafNSq_of_sq c2446_nsq, leafHAr_of_sq c2446_har,
   c2446_r, c2446_e', c2446_f1, leafS2_of_sq c2446_s2, leafS3_of_sq c2446_s3,
   c2446_iso, leafR8_of_sq c2446_nof2 c2446_nof3 c2446_nof4z⟩
theorem not_tile'_2446 (D : CongruentDissection 2446) : False :=
  not_tile_of_conditions' 2446 C'_2446 D

private theorem c2447_sqf   : LeafSqf 2447   := by decide +kernel
private theorem c2447_range : LeafRange 2447  := by decide +kernel
private theorem c2447_ell   : LeafEll 2447    := by decide +kernel
private theorem c2447_nsq   : NSqChkSq 2447   := by decide +kernel
private theorem c2447_har   : HArithChkSq 2447 := by decide +kernel
private theorem c2447_r     : LeafR 2447      := by decide +kernel
private theorem c2447_e'    : LeafE' 2447     := by decide +kernel
private theorem c2447_f1    : LeafF1 2447     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2447_s2    : S2ChkSq 2447    := by decide +kernel
private theorem c2447_s3    : S3ChkSq 2447    := by decide +kernel
private theorem c2447_iso   : LeafIso 2447    := by decide +kernel
private theorem c2447_nof2  : NoF2ChkSq 2447  := by decide +kernel
private theorem c2447_nof3  : NoF3ChkSq 2447  := by decide +kernel
private theorem c2447_nof4z : NoF4zChkSq 2447 := by decide +kernel
theorem C'_2447 : C' 2447 :=
  ⟨c2447_sqf, c2447_range, c2447_ell, leafNSq_of_sq c2447_nsq, leafHAr_of_sq c2447_har,
   c2447_r, c2447_e', c2447_f1, leafS2_of_sq c2447_s2, leafS3_of_sq c2447_s3,
   c2447_iso, leafR8_of_sq c2447_nof2 c2447_nof3 c2447_nof4z⟩
theorem not_tile'_2447 (D : CongruentDissection 2447) : False :=
  not_tile_of_conditions' 2447 C'_2447 D

private theorem c2449_sqf   : LeafSqf 2449   := by decide +kernel
private theorem c2449_range : LeafRange 2449  := by decide +kernel
private theorem c2449_ell   : LeafEll 2449    := by decide +kernel
private theorem c2449_nsq   : NSqChkSq 2449   := by decide +kernel
private theorem c2449_har   : HArithChkSq 2449 := by decide +kernel
private theorem c2449_r     : LeafR 2449      := by decide +kernel
private theorem c2449_e'    : LeafE' 2449     := by decide +kernel
private theorem c2449_f1    : LeafF1 2449     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2449_s2    : S2ChkSq 2449    := by decide +kernel
private theorem c2449_s3    : S3ChkSq 2449    := by decide +kernel
private theorem c2449_iso   : LeafIso 2449    := by decide +kernel
private theorem c2449_nof2  : NoF2ChkSq 2449  := by decide +kernel
private theorem c2449_nof3  : NoF3ChkSq 2449  := by decide +kernel
private theorem c2449_nof4z : NoF4zChkSq 2449 := by decide +kernel
theorem C'_2449 : C' 2449 :=
  ⟨c2449_sqf, c2449_range, c2449_ell, leafNSq_of_sq c2449_nsq, leafHAr_of_sq c2449_har,
   c2449_r, c2449_e', c2449_f1, leafS2_of_sq c2449_s2, leafS3_of_sq c2449_s3,
   c2449_iso, leafR8_of_sq c2449_nof2 c2449_nof3 c2449_nof4z⟩
theorem not_tile'_2449 (D : CongruentDissection 2449) : False :=
  not_tile_of_conditions' 2449 C'_2449 D

private theorem c2451_sqf   : LeafSqf 2451   := by decide +kernel
private theorem c2451_range : LeafRange 2451  := by decide +kernel
private theorem c2451_ell   : LeafEll 2451    := by decide +kernel
private theorem c2451_nsq   : NSqChkSq 2451   := by decide +kernel
private theorem c2451_har   : HArithChkSq 2451 := by decide +kernel
private theorem c2451_r     : LeafR 2451      := by decide +kernel
private theorem c2451_e'    : LeafE' 2451     := by decide +kernel
private theorem c2451_f1    : LeafF1 2451     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2451_s2    : S2ChkSq 2451    := by decide +kernel
private theorem c2451_s3    : S3ChkSq 2451    := by decide +kernel
private theorem c2451_iso   : LeafIso 2451    := by decide +kernel
private theorem c2451_nof2  : NoF2ChkSq 2451  := by decide +kernel
private theorem c2451_nof3  : NoF3ChkSq 2451  := by decide +kernel
private theorem c2451_nof4z : NoF4zChkSq 2451 := by decide +kernel
theorem C'_2451 : C' 2451 :=
  ⟨c2451_sqf, c2451_range, c2451_ell, leafNSq_of_sq c2451_nsq, leafHAr_of_sq c2451_har,
   c2451_r, c2451_e', c2451_f1, leafS2_of_sq c2451_s2, leafS3_of_sq c2451_s3,
   c2451_iso, leafR8_of_sq c2451_nof2 c2451_nof3 c2451_nof4z⟩
theorem not_tile'_2451 (D : CongruentDissection 2451) : False :=
  not_tile_of_conditions' 2451 C'_2451 D

private theorem c2453_sqf   : LeafSqf 2453   := by decide +kernel
private theorem c2453_range : LeafRange 2453  := by decide +kernel
private theorem c2453_ell   : LeafEll 2453    := by decide +kernel
private theorem c2453_nsq   : NSqChkSq 2453   := by decide +kernel
private theorem c2453_har   : HArithChkSq 2453 := by decide +kernel
private theorem c2453_r     : LeafR 2453      := by decide +kernel
private theorem c2453_e'    : LeafE' 2453     := by decide +kernel
private theorem c2453_f1    : LeafF1 2453     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2453_s2    : S2ChkSq 2453    := by decide +kernel
private theorem c2453_s3    : S3ChkSq 2453    := by decide +kernel
private theorem c2453_iso   : LeafIso 2453    := by decide +kernel
private theorem c2453_nof2  : NoF2ChkSq 2453  := by decide +kernel
private theorem c2453_nof3  : NoF3ChkSq 2453  := by decide +kernel
private theorem c2453_nof4z : NoF4zChkSq 2453 := by decide +kernel
theorem C'_2453 : C' 2453 :=
  ⟨c2453_sqf, c2453_range, c2453_ell, leafNSq_of_sq c2453_nsq, leafHAr_of_sq c2453_har,
   c2453_r, c2453_e', c2453_f1, leafS2_of_sq c2453_s2, leafS3_of_sq c2453_s3,
   c2453_iso, leafR8_of_sq c2453_nof2 c2453_nof3 c2453_nof4z⟩
theorem not_tile'_2453 (D : CongruentDissection 2453) : False :=
  not_tile_of_conditions' 2453 C'_2453 D

end Erdos634.Draft.AllN2

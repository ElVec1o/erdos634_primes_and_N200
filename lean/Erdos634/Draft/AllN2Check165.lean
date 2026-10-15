/- AllN2Check165: N = 3446, 3451, 3453, 3454, 3455
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3446_sqf   : LeafSqf 3446   := by decide +kernel
private theorem c3446_range : LeafRange 3446  := by decide +kernel
private theorem c3446_ell   : LeafEll 3446    := by decide +kernel
private theorem c3446_nsq   : NSqChkSq 3446   := by decide +kernel
private theorem c3446_har   : HArithChkSq 3446 := by decide +kernel
private theorem c3446_r     : LeafR 3446      := by decide +kernel
private theorem c3446_e'    : LeafE' 3446     := by decide +kernel
private theorem c3446_f1    : LeafF1 3446     := Or.inl (by decide)
private theorem c3446_s2    : S2ChkSq 3446    := by decide +kernel
private theorem c3446_s3    : S3ChkSq 3446    := by decide +kernel
private theorem c3446_iso   : LeafIso 3446    := by decide +kernel
private theorem c3446_nof2  : NoF2ChkSq 3446  := by decide +kernel
private theorem c3446_nof3  : NoF3ChkSq 3446  := by decide +kernel
private theorem c3446_nof4z : NoF4zChkSq 3446 := by decide +kernel
theorem C'_3446 : C' 3446 :=
  ⟨c3446_sqf, c3446_range, c3446_ell, leafNSq_of_sq c3446_nsq, leafHAr_of_sq c3446_har,
   c3446_r, c3446_e', c3446_f1, leafS2_of_sq c3446_s2, leafS3_of_sq c3446_s3,
   c3446_iso, leafR8_of_sq c3446_nof2 c3446_nof3 c3446_nof4z⟩
theorem not_tile'_3446 (D : CongruentDissection 3446) : False :=
  not_tile_of_conditions' 3446 C'_3446 D

private theorem c3451_sqf   : LeafSqf 3451   := by decide +kernel
private theorem c3451_range : LeafRange 3451  := by decide +kernel
private theorem c3451_ell   : LeafEll 3451    := by decide +kernel
private theorem c3451_nsq   : NSqChkSq 3451   := by decide +kernel
private theorem c3451_har   : HArithChkSq 3451 := by decide +kernel
private theorem c3451_r     : LeafR 3451      := by decide +kernel
private theorem c3451_e'    : LeafE' 3451     := by decide +kernel
private theorem c3451_f1    : LeafF1 3451     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3451_s2    : S2ChkSq 3451    := by decide +kernel
private theorem c3451_s3    : S3ChkSq 3451    := by decide +kernel
private theorem c3451_iso   : LeafIso 3451    := by decide +kernel
private theorem c3451_nof2  : NoF2ChkSq 3451  := by decide +kernel
private theorem c3451_nof3  : NoF3ChkSq 3451  := by decide +kernel
private theorem c3451_nof4z : NoF4zChkSq 3451 := by decide +kernel
theorem C'_3451 : C' 3451 :=
  ⟨c3451_sqf, c3451_range, c3451_ell, leafNSq_of_sq c3451_nsq, leafHAr_of_sq c3451_har,
   c3451_r, c3451_e', c3451_f1, leafS2_of_sq c3451_s2, leafS3_of_sq c3451_s3,
   c3451_iso, leafR8_of_sq c3451_nof2 c3451_nof3 c3451_nof4z⟩
theorem not_tile'_3451 (D : CongruentDissection 3451) : False :=
  not_tile_of_conditions' 3451 C'_3451 D

private theorem c3453_sqf   : LeafSqf 3453   := by decide +kernel
private theorem c3453_range : LeafRange 3453  := by decide +kernel
private theorem c3453_ell   : LeafEll 3453    := by decide +kernel
private theorem c3453_nsq   : NSqChkSq 3453   := by decide +kernel
private theorem c3453_har   : HArithChkSq 3453 := by decide +kernel
private theorem c3453_r     : LeafR 3453      := by decide +kernel
private theorem c3453_e'    : LeafE' 3453     := by decide +kernel
private theorem c3453_f1    : LeafF1 3453     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3453_s2    : S2ChkSq 3453    := by decide +kernel
private theorem c3453_s3    : S3ChkSq 3453    := by decide +kernel
private theorem c3453_iso   : LeafIso 3453    := by decide +kernel
private theorem c3453_nof2  : NoF2ChkSq 3453  := by decide +kernel
private theorem c3453_nof3  : NoF3ChkSq 3453  := by decide +kernel
private theorem c3453_nof4z : NoF4zChkSq 3453 := by decide +kernel
theorem C'_3453 : C' 3453 :=
  ⟨c3453_sqf, c3453_range, c3453_ell, leafNSq_of_sq c3453_nsq, leafHAr_of_sq c3453_har,
   c3453_r, c3453_e', c3453_f1, leafS2_of_sq c3453_s2, leafS3_of_sq c3453_s3,
   c3453_iso, leafR8_of_sq c3453_nof2 c3453_nof3 c3453_nof4z⟩
theorem not_tile'_3453 (D : CongruentDissection 3453) : False :=
  not_tile_of_conditions' 3453 C'_3453 D

private theorem c3454_sqf   : LeafSqf 3454   := by decide +kernel
private theorem c3454_range : LeafRange 3454  := by decide +kernel
private theorem c3454_ell   : LeafEll 3454    := by decide +kernel
private theorem c3454_nsq   : NSqChkSq 3454   := by decide +kernel
private theorem c3454_har   : HArithChkSq 3454 := by decide +kernel
private theorem c3454_r     : LeafR 3454      := by decide +kernel
private theorem c3454_e'    : LeafE' 3454     := by decide +kernel
private theorem c3454_f1    : LeafF1 3454     := Or.inl (by decide)
private theorem c3454_s2    : S2ChkSq 3454    := by decide +kernel
private theorem c3454_s3    : S3ChkSq 3454    := by decide +kernel
private theorem c3454_iso   : LeafIso 3454    := by decide +kernel
private theorem c3454_nof2  : NoF2ChkSq 3454  := by decide +kernel
private theorem c3454_nof3  : NoF3ChkSq 3454  := by decide +kernel
private theorem c3454_nof4z : NoF4zChkSq 3454 := by decide +kernel
theorem C'_3454 : C' 3454 :=
  ⟨c3454_sqf, c3454_range, c3454_ell, leafNSq_of_sq c3454_nsq, leafHAr_of_sq c3454_har,
   c3454_r, c3454_e', c3454_f1, leafS2_of_sq c3454_s2, leafS3_of_sq c3454_s3,
   c3454_iso, leafR8_of_sq c3454_nof2 c3454_nof3 c3454_nof4z⟩
theorem not_tile'_3454 (D : CongruentDissection 3454) : False :=
  not_tile_of_conditions' 3454 C'_3454 D

private theorem c3455_sqf   : LeafSqf 3455   := by decide +kernel
private theorem c3455_range : LeafRange 3455  := by decide +kernel
private theorem c3455_ell   : LeafEll 3455    := by decide +kernel
private theorem c3455_nsq   : NSqChkSq 3455   := by decide +kernel
private theorem c3455_har   : HArithChkSq 3455 := by decide +kernel
private theorem c3455_r     : LeafR 3455      := by decide +kernel
private theorem c3455_e'    : LeafE' 3455     := by decide +kernel
private theorem c3455_f1    : LeafF1 3455     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3455_s2    : S2ChkSq 3455    := by decide +kernel
private theorem c3455_s3    : S3ChkSq 3455    := by decide +kernel
private theorem c3455_iso   : LeafIso 3455    := by decide +kernel
private theorem c3455_nof2  : NoF2ChkSq 3455  := by decide +kernel
private theorem c3455_nof3  : NoF3ChkSq 3455  := by decide +kernel
private theorem c3455_nof4z : NoF4zChkSq 3455 := by decide +kernel
theorem C'_3455 : C' 3455 :=
  ⟨c3455_sqf, c3455_range, c3455_ell, leafNSq_of_sq c3455_nsq, leafHAr_of_sq c3455_har,
   c3455_r, c3455_e', c3455_f1, leafS2_of_sq c3455_s2, leafS3_of_sq c3455_s3,
   c3455_iso, leafR8_of_sq c3455_nof2 c3455_nof3 c3455_nof4z⟩
theorem not_tile'_3455 (D : CongruentDissection 3455) : False :=
  not_tile_of_conditions' 3455 C'_3455 D

end Erdos634.Draft.AllN2

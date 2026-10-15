/- AllN2Check284: N = 4962, 4963, 4966, 4967, 4970
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4962_sqf   : LeafSqf 4962   := by decide +kernel
private theorem c4962_range : LeafRange 4962  := by decide +kernel
private theorem c4962_ell   : LeafEll 4962    := by decide +kernel
private theorem c4962_nsq   : NSqChkSq 4962   := by decide +kernel
private theorem c4962_har   : HArithChkSq 4962 := by decide +kernel
private theorem c4962_r     : LeafR 4962      := by decide +kernel
private theorem c4962_e'    : LeafE' 4962     := by decide +kernel
private theorem c4962_f1    : LeafF1 4962     := Or.inl (by decide)
private theorem c4962_s2    : S2ChkSq 4962    := by decide +kernel
private theorem c4962_s3    : S3ChkSq 4962    := by decide +kernel
private theorem c4962_iso   : LeafIso 4962    := by decide +kernel
private theorem c4962_nof2  : NoF2ChkSq 4962  := by decide +kernel
private theorem c4962_nof3  : NoF3ChkSq 4962  := by decide +kernel
private theorem c4962_nof4z : NoF4zChkSq 4962 := by decide +kernel
theorem C'_4962 : C' 4962 :=
  ⟨c4962_sqf, c4962_range, c4962_ell, leafNSq_of_sq c4962_nsq, leafHAr_of_sq c4962_har,
   c4962_r, c4962_e', c4962_f1, leafS2_of_sq c4962_s2, leafS3_of_sq c4962_s3,
   c4962_iso, leafR8_of_sq c4962_nof2 c4962_nof3 c4962_nof4z⟩
theorem not_tile'_4962 (D : CongruentDissection 4962) : False :=
  not_tile_of_conditions' 4962 C'_4962 D

private theorem c4963_sqf   : LeafSqf 4963   := by decide +kernel
private theorem c4963_range : LeafRange 4963  := by decide +kernel
private theorem c4963_ell   : LeafEll 4963    := by decide +kernel
private theorem c4963_nsq   : NSqChkSq 4963   := by decide +kernel
private theorem c4963_har   : HArithChkSq 4963 := by decide +kernel
private theorem c4963_r     : LeafR 4963      := by decide +kernel
private theorem c4963_e'    : LeafE' 4963     := by decide +kernel
private theorem c4963_f1    : LeafF1 4963     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4963_s2    : S2ChkSq 4963    := by decide +kernel
private theorem c4963_s3    : S3ChkSq 4963    := by decide +kernel
private theorem c4963_iso   : LeafIso 4963    := by decide +kernel
private theorem c4963_nof2  : NoF2ChkSq 4963  := by decide +kernel
private theorem c4963_nof3  : NoF3ChkSq 4963  := by decide +kernel
private theorem c4963_nof4z : NoF4zChkSq 4963 := by decide +kernel
theorem C'_4963 : C' 4963 :=
  ⟨c4963_sqf, c4963_range, c4963_ell, leafNSq_of_sq c4963_nsq, leafHAr_of_sq c4963_har,
   c4963_r, c4963_e', c4963_f1, leafS2_of_sq c4963_s2, leafS3_of_sq c4963_s3,
   c4963_iso, leafR8_of_sq c4963_nof2 c4963_nof3 c4963_nof4z⟩
theorem not_tile'_4963 (D : CongruentDissection 4963) : False :=
  not_tile_of_conditions' 4963 C'_4963 D

private theorem c4966_sqf   : LeafSqf 4966   := by decide +kernel
private theorem c4966_range : LeafRange 4966  := by decide +kernel
private theorem c4966_ell   : LeafEll 4966    := by decide +kernel
private theorem c4966_nsq   : NSqChkSq 4966   := by decide +kernel
private theorem c4966_har   : HArithChkSq 4966 := by decide +kernel
private theorem c4966_r     : LeafR 4966      := by decide +kernel
private theorem c4966_e'    : LeafE' 4966     := by decide +kernel
private theorem c4966_f1    : LeafF1 4966     := Or.inl (by decide)
private theorem c4966_s2    : S2ChkSq 4966    := by decide +kernel
private theorem c4966_s3    : S3ChkSq 4966    := by decide +kernel
private theorem c4966_iso   : LeafIso 4966    := by decide +kernel
private theorem c4966_nof2  : NoF2ChkSq 4966  := by decide +kernel
private theorem c4966_nof3  : NoF3ChkSq 4966  := by decide +kernel
private theorem c4966_nof4z : NoF4zChkSq 4966 := by decide +kernel
theorem C'_4966 : C' 4966 :=
  ⟨c4966_sqf, c4966_range, c4966_ell, leafNSq_of_sq c4966_nsq, leafHAr_of_sq c4966_har,
   c4966_r, c4966_e', c4966_f1, leafS2_of_sq c4966_s2, leafS3_of_sq c4966_s3,
   c4966_iso, leafR8_of_sq c4966_nof2 c4966_nof3 c4966_nof4z⟩
theorem not_tile'_4966 (D : CongruentDissection 4966) : False :=
  not_tile_of_conditions' 4966 C'_4966 D

private theorem c4967_sqf   : LeafSqf 4967   := by decide +kernel
private theorem c4967_range : LeafRange 4967  := by decide +kernel
private theorem c4967_ell   : LeafEll 4967    := by decide +kernel
private theorem c4967_nsq   : NSqChkSq 4967   := by decide +kernel
private theorem c4967_har   : HArithChkSq 4967 := by decide +kernel
private theorem c4967_r     : LeafR 4967      := by decide +kernel
private theorem c4967_e'    : LeafE' 4967     := by decide +kernel
private theorem c4967_f1    : LeafF1 4967     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4967_s2    : S2ChkSq 4967    := by decide +kernel
private theorem c4967_s3    : S3ChkSq 4967    := by decide +kernel
private theorem c4967_iso   : LeafIso 4967    := by decide +kernel
private theorem c4967_nof2  : NoF2ChkSq 4967  := by decide +kernel
private theorem c4967_nof3  : NoF3ChkSq 4967  := by decide +kernel
private theorem c4967_nof4z : NoF4zChkSq 4967 := by decide +kernel
theorem C'_4967 : C' 4967 :=
  ⟨c4967_sqf, c4967_range, c4967_ell, leafNSq_of_sq c4967_nsq, leafHAr_of_sq c4967_har,
   c4967_r, c4967_e', c4967_f1, leafS2_of_sq c4967_s2, leafS3_of_sq c4967_s3,
   c4967_iso, leafR8_of_sq c4967_nof2 c4967_nof3 c4967_nof4z⟩
theorem not_tile'_4967 (D : CongruentDissection 4967) : False :=
  not_tile_of_conditions' 4967 C'_4967 D

private theorem c4970_sqf   : LeafSqf 4970   := by decide +kernel
private theorem c4970_range : LeafRange 4970  := by decide +kernel
private theorem c4970_ell   : LeafEll 4970    := by decide +kernel
private theorem c4970_nsq   : NSqChkSq 4970   := by decide +kernel
private theorem c4970_har   : HArithChkSq 4970 := by decide +kernel
private theorem c4970_r     : LeafR 4970      := by decide +kernel
private theorem c4970_e'    : LeafE' 4970     := by decide +kernel
private theorem c4970_f1    : LeafF1 4970     := Or.inl (by decide)
private theorem c4970_s2    : S2ChkSq 4970    := by decide +kernel
private theorem c4970_s3    : S3ChkSq 4970    := by decide +kernel
private theorem c4970_iso   : LeafIso 4970    := by decide +kernel
private theorem c4970_nof2  : NoF2ChkSq 4970  := by decide +kernel
private theorem c4970_nof3  : NoF3ChkSq 4970  := by decide +kernel
private theorem c4970_nof4z : NoF4zChkSq 4970 := by decide +kernel
theorem C'_4970 : C' 4970 :=
  ⟨c4970_sqf, c4970_range, c4970_ell, leafNSq_of_sq c4970_nsq, leafHAr_of_sq c4970_har,
   c4970_r, c4970_e', c4970_f1, leafS2_of_sq c4970_s2, leafS3_of_sq c4970_s3,
   c4970_iso, leafR8_of_sq c4970_nof2 c4970_nof3 c4970_nof4z⟩
theorem not_tile'_4970 (D : CongruentDissection 4970) : False :=
  not_tile_of_conditions' 4970 C'_4970 D

end Erdos634.Draft.AllN2

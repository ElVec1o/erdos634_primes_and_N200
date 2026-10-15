/- AllN2Check127: N = 2959, 2963, 2966, 2971, 2973
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2959_sqf   : LeafSqf 2959   := by decide +kernel
private theorem c2959_range : LeafRange 2959  := by decide +kernel
private theorem c2959_ell   : LeafEll 2959    := by decide +kernel
private theorem c2959_nsq   : NSqChkSq 2959   := by decide +kernel
private theorem c2959_har   : HArithChkSq 2959 := by decide +kernel
private theorem c2959_r     : LeafR 2959      := by decide +kernel
private theorem c2959_e'    : LeafE' 2959     := by decide +kernel
private theorem c2959_f1    : LeafF1 2959     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2959_s2    : S2ChkSq 2959    := by decide +kernel
private theorem c2959_s3    : S3ChkSq 2959    := by decide +kernel
private theorem c2959_iso   : LeafIso 2959    := by decide +kernel
private theorem c2959_nof2  : NoF2ChkSq 2959  := by decide +kernel
private theorem c2959_nof3  : NoF3ChkSq 2959  := by decide +kernel
private theorem c2959_nof4z : NoF4zChkSq 2959 := by decide +kernel
theorem C'_2959 : C' 2959 :=
  ⟨c2959_sqf, c2959_range, c2959_ell, leafNSq_of_sq c2959_nsq, leafHAr_of_sq c2959_har,
   c2959_r, c2959_e', c2959_f1, leafS2_of_sq c2959_s2, leafS3_of_sq c2959_s3,
   c2959_iso, leafR8_of_sq c2959_nof2 c2959_nof3 c2959_nof4z⟩
theorem not_tile'_2959 (D : CongruentDissection 2959) : False :=
  not_tile_of_conditions' 2959 C'_2959 D

private theorem c2963_sqf   : LeafSqf 2963   := by decide +kernel
private theorem c2963_range : LeafRange 2963  := by decide +kernel
private theorem c2963_ell   : LeafEll 2963    := by decide +kernel
private theorem c2963_nsq   : NSqChkSq 2963   := by decide +kernel
private theorem c2963_har   : HArithChkSq 2963 := by decide +kernel
private theorem c2963_r     : LeafR 2963      := by decide +kernel
private theorem c2963_e'    : LeafE' 2963     := by decide +kernel
private theorem c2963_f1    : LeafF1 2963     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2963_s2    : S2ChkSq 2963    := by decide +kernel
private theorem c2963_s3    : S3ChkSq 2963    := by decide +kernel
private theorem c2963_iso   : LeafIso 2963    := by decide +kernel
private theorem c2963_nof2  : NoF2ChkSq 2963  := by decide +kernel
private theorem c2963_nof3  : NoF3ChkSq 2963  := by decide +kernel
private theorem c2963_nof4z : NoF4zChkSq 2963 := by decide +kernel
theorem C'_2963 : C' 2963 :=
  ⟨c2963_sqf, c2963_range, c2963_ell, leafNSq_of_sq c2963_nsq, leafHAr_of_sq c2963_har,
   c2963_r, c2963_e', c2963_f1, leafS2_of_sq c2963_s2, leafS3_of_sq c2963_s3,
   c2963_iso, leafR8_of_sq c2963_nof2 c2963_nof3 c2963_nof4z⟩
theorem not_tile'_2963 (D : CongruentDissection 2963) : False :=
  not_tile_of_conditions' 2963 C'_2963 D

private theorem c2966_sqf   : LeafSqf 2966   := by decide +kernel
private theorem c2966_range : LeafRange 2966  := by decide +kernel
private theorem c2966_ell   : LeafEll 2966    := by decide +kernel
private theorem c2966_nsq   : NSqChkSq 2966   := by decide +kernel
private theorem c2966_har   : HArithChkSq 2966 := by decide +kernel
private theorem c2966_r     : LeafR 2966      := by decide +kernel
private theorem c2966_e'    : LeafE' 2966     := by decide +kernel
private theorem c2966_f1    : LeafF1 2966     := Or.inl (by decide)
private theorem c2966_s2    : S2ChkSq 2966    := by decide +kernel
private theorem c2966_s3    : S3ChkSq 2966    := by decide +kernel
private theorem c2966_iso   : LeafIso 2966    := by decide +kernel
private theorem c2966_nof2  : NoF2ChkSq 2966  := by decide +kernel
private theorem c2966_nof3  : NoF3ChkSq 2966  := by decide +kernel
private theorem c2966_nof4z : NoF4zChkSq 2966 := by decide +kernel
theorem C'_2966 : C' 2966 :=
  ⟨c2966_sqf, c2966_range, c2966_ell, leafNSq_of_sq c2966_nsq, leafHAr_of_sq c2966_har,
   c2966_r, c2966_e', c2966_f1, leafS2_of_sq c2966_s2, leafS3_of_sq c2966_s3,
   c2966_iso, leafR8_of_sq c2966_nof2 c2966_nof3 c2966_nof4z⟩
theorem not_tile'_2966 (D : CongruentDissection 2966) : False :=
  not_tile_of_conditions' 2966 C'_2966 D

private theorem c2971_sqf   : LeafSqf 2971   := by decide +kernel
private theorem c2971_range : LeafRange 2971  := by decide +kernel
private theorem c2971_ell   : LeafEll 2971    := by decide +kernel
private theorem c2971_nsq   : NSqChkSq 2971   := by decide +kernel
private theorem c2971_har   : HArithChkSq 2971 := by decide +kernel
private theorem c2971_r     : LeafR 2971      := by decide +kernel
private theorem c2971_e'    : LeafE' 2971     := by decide +kernel
private theorem c2971_f1    : LeafF1 2971     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2971_s2    : S2ChkSq 2971    := by decide +kernel
private theorem c2971_s3    : S3ChkSq 2971    := by decide +kernel
private theorem c2971_iso   : LeafIso 2971    := by decide +kernel
private theorem c2971_nof2  : NoF2ChkSq 2971  := by decide +kernel
private theorem c2971_nof3  : NoF3ChkSq 2971  := by decide +kernel
private theorem c2971_nof4z : NoF4zChkSq 2971 := by decide +kernel
theorem C'_2971 : C' 2971 :=
  ⟨c2971_sqf, c2971_range, c2971_ell, leafNSq_of_sq c2971_nsq, leafHAr_of_sq c2971_har,
   c2971_r, c2971_e', c2971_f1, leafS2_of_sq c2971_s2, leafS3_of_sq c2971_s3,
   c2971_iso, leafR8_of_sq c2971_nof2 c2971_nof3 c2971_nof4z⟩
theorem not_tile'_2971 (D : CongruentDissection 2971) : False :=
  not_tile_of_conditions' 2971 C'_2971 D

private theorem c2973_sqf   : LeafSqf 2973   := by decide +kernel
private theorem c2973_range : LeafRange 2973  := by decide +kernel
private theorem c2973_ell   : LeafEll 2973    := by decide +kernel
private theorem c2973_nsq   : NSqChkSq 2973   := by decide +kernel
private theorem c2973_har   : HArithChkSq 2973 := by decide +kernel
private theorem c2973_r     : LeafR 2973      := by decide +kernel
private theorem c2973_e'    : LeafE' 2973     := by decide +kernel
private theorem c2973_f1    : LeafF1 2973     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2973_s2    : S2ChkSq 2973    := by decide +kernel
private theorem c2973_s3    : S3ChkSq 2973    := by decide +kernel
private theorem c2973_iso   : LeafIso 2973    := by decide +kernel
private theorem c2973_nof2  : NoF2ChkSq 2973  := by decide +kernel
private theorem c2973_nof3  : NoF3ChkSq 2973  := by decide +kernel
private theorem c2973_nof4z : NoF4zChkSq 2973 := by decide +kernel
theorem C'_2973 : C' 2973 :=
  ⟨c2973_sqf, c2973_range, c2973_ell, leafNSq_of_sq c2973_nsq, leafHAr_of_sq c2973_har,
   c2973_r, c2973_e', c2973_f1, leafS2_of_sq c2973_s2, leafS3_of_sq c2973_s3,
   c2973_iso, leafR8_of_sq c2973_nof2 c2973_nof3 c2973_nof4z⟩
theorem not_tile'_2973 (D : CongruentDissection 2973) : False :=
  not_tile_of_conditions' 2973 C'_2973 D

end Erdos634.Draft.AllN2

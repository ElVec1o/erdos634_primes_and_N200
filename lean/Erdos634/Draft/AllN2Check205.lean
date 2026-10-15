/- AllN2Check205: N = 3963, 3966, 3967, 3974, 3979
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3963_sqf   : LeafSqf 3963   := by decide +kernel
private theorem c3963_range : LeafRange 3963  := by decide +kernel
private theorem c3963_ell   : LeafEll 3963    := by decide +kernel
private theorem c3963_nsq   : NSqChkSq 3963   := by decide +kernel
private theorem c3963_har   : HArithChkSq 3963 := by decide +kernel
private theorem c3963_r     : LeafR 3963      := by decide +kernel
private theorem c3963_e'    : LeafE' 3963     := by decide +kernel
private theorem c3963_f1    : LeafF1 3963     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3963_s2    : S2ChkSq 3963    := by decide +kernel
private theorem c3963_s3    : S3ChkSq 3963    := by decide +kernel
private theorem c3963_iso   : LeafIso 3963    := by decide +kernel
private theorem c3963_nof2  : NoF2ChkSq 3963  := by decide +kernel
private theorem c3963_nof3  : NoF3ChkSq 3963  := by decide +kernel
private theorem c3963_nof4z : NoF4zChkSq 3963 := by decide +kernel
theorem C'_3963 : C' 3963 :=
  ⟨c3963_sqf, c3963_range, c3963_ell, leafNSq_of_sq c3963_nsq, leafHAr_of_sq c3963_har,
   c3963_r, c3963_e', c3963_f1, leafS2_of_sq c3963_s2, leafS3_of_sq c3963_s3,
   c3963_iso, leafR8_of_sq c3963_nof2 c3963_nof3 c3963_nof4z⟩
theorem not_tile'_3963 (D : CongruentDissection 3963) : False :=
  not_tile_of_conditions' 3963 C'_3963 D

private theorem c3966_sqf   : LeafSqf 3966   := by decide +kernel
private theorem c3966_range : LeafRange 3966  := by decide +kernel
private theorem c3966_ell   : LeafEll 3966    := by decide +kernel
private theorem c3966_nsq   : NSqChkSq 3966   := by decide +kernel
private theorem c3966_har   : HArithChkSq 3966 := by decide +kernel
private theorem c3966_r     : LeafR 3966      := by decide +kernel
private theorem c3966_e'    : LeafE' 3966     := by decide +kernel
private theorem c3966_f1    : LeafF1 3966     := Or.inl (by decide)
private theorem c3966_s2    : S2ChkSq 3966    := by decide +kernel
private theorem c3966_s3    : S3ChkSq 3966    := by decide +kernel
private theorem c3966_iso   : LeafIso 3966    := by decide +kernel
private theorem c3966_nof2  : NoF2ChkSq 3966  := by decide +kernel
private theorem c3966_nof3  : NoF3ChkSq 3966  := by decide +kernel
private theorem c3966_nof4z : NoF4zChkSq 3966 := by decide +kernel
theorem C'_3966 : C' 3966 :=
  ⟨c3966_sqf, c3966_range, c3966_ell, leafNSq_of_sq c3966_nsq, leafHAr_of_sq c3966_har,
   c3966_r, c3966_e', c3966_f1, leafS2_of_sq c3966_s2, leafS3_of_sq c3966_s3,
   c3966_iso, leafR8_of_sq c3966_nof2 c3966_nof3 c3966_nof4z⟩
theorem not_tile'_3966 (D : CongruentDissection 3966) : False :=
  not_tile_of_conditions' 3966 C'_3966 D

private theorem c3967_sqf   : LeafSqf 3967   := by decide +kernel
private theorem c3967_range : LeafRange 3967  := by decide +kernel
private theorem c3967_ell   : LeafEll 3967    := by decide +kernel
private theorem c3967_nsq   : NSqChkSq 3967   := by decide +kernel
private theorem c3967_har   : HArithChkSq 3967 := by decide +kernel
private theorem c3967_r     : LeafR 3967      := by decide +kernel
private theorem c3967_e'    : LeafE' 3967     := by decide +kernel
private theorem c3967_f1    : LeafF1 3967     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3967_s2    : S2ChkSq 3967    := by decide +kernel
private theorem c3967_s3    : S3ChkSq 3967    := by decide +kernel
private theorem c3967_iso   : LeafIso 3967    := by decide +kernel
private theorem c3967_nof2  : NoF2ChkSq 3967  := by decide +kernel
private theorem c3967_nof3  : NoF3ChkSq 3967  := by decide +kernel
private theorem c3967_nof4z : NoF4zChkSq 3967 := by decide +kernel
theorem C'_3967 : C' 3967 :=
  ⟨c3967_sqf, c3967_range, c3967_ell, leafNSq_of_sq c3967_nsq, leafHAr_of_sq c3967_har,
   c3967_r, c3967_e', c3967_f1, leafS2_of_sq c3967_s2, leafS3_of_sq c3967_s3,
   c3967_iso, leafR8_of_sq c3967_nof2 c3967_nof3 c3967_nof4z⟩
theorem not_tile'_3967 (D : CongruentDissection 3967) : False :=
  not_tile_of_conditions' 3967 C'_3967 D

private theorem c3974_sqf   : LeafSqf 3974   := by decide +kernel
private theorem c3974_range : LeafRange 3974  := by decide +kernel
private theorem c3974_ell   : LeafEll 3974    := by decide +kernel
private theorem c3974_nsq   : NSqChkSq 3974   := by decide +kernel
private theorem c3974_har   : HArithChkSq 3974 := by decide +kernel
private theorem c3974_r     : LeafR 3974      := by decide +kernel
private theorem c3974_e'    : LeafE' 3974     := by decide +kernel
private theorem c3974_f1    : LeafF1 3974     := Or.inl (by decide)
private theorem c3974_s2    : S2ChkSq 3974    := by decide +kernel
private theorem c3974_s3    : S3ChkSq 3974    := by decide +kernel
private theorem c3974_iso   : LeafIso 3974    := by decide +kernel
private theorem c3974_nof2  : NoF2ChkSq 3974  := by decide +kernel
private theorem c3974_nof3  : NoF3ChkSq 3974  := by decide +kernel
private theorem c3974_nof4z : NoF4zChkSq 3974 := by decide +kernel
theorem C'_3974 : C' 3974 :=
  ⟨c3974_sqf, c3974_range, c3974_ell, leafNSq_of_sq c3974_nsq, leafHAr_of_sq c3974_har,
   c3974_r, c3974_e', c3974_f1, leafS2_of_sq c3974_s2, leafS3_of_sq c3974_s3,
   c3974_iso, leafR8_of_sq c3974_nof2 c3974_nof3 c3974_nof4z⟩
theorem not_tile'_3974 (D : CongruentDissection 3974) : False :=
  not_tile_of_conditions' 3974 C'_3974 D

private theorem c3979_sqf   : LeafSqf 3979   := by decide +kernel
private theorem c3979_range : LeafRange 3979  := by decide +kernel
private theorem c3979_ell   : LeafEll 3979    := by decide +kernel
private theorem c3979_nsq   : NSqChkSq 3979   := by decide +kernel
private theorem c3979_har   : HArithChkSq 3979 := by decide +kernel
private theorem c3979_r     : LeafR 3979      := by decide +kernel
private theorem c3979_e'    : LeafE' 3979     := by decide +kernel
private theorem c3979_f1    : LeafF1 3979     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3979_s2    : S2ChkSq 3979    := by decide +kernel
private theorem c3979_s3    : S3ChkSq 3979    := by decide +kernel
private theorem c3979_iso   : LeafIso 3979    := by decide +kernel
private theorem c3979_nof2  : NoF2ChkSq 3979  := by decide +kernel
private theorem c3979_nof3  : NoF3ChkSq 3979  := by decide +kernel
private theorem c3979_nof4z : NoF4zChkSq 3979 := by decide +kernel
theorem C'_3979 : C' 3979 :=
  ⟨c3979_sqf, c3979_range, c3979_ell, leafNSq_of_sq c3979_nsq, leafHAr_of_sq c3979_har,
   c3979_r, c3979_e', c3979_f1, leafS2_of_sq c3979_s2, leafS3_of_sq c3979_s3,
   c3979_iso, leafR8_of_sq c3979_nof2 c3979_nof3 c3979_nof4z⟩
theorem not_tile'_3979 (D : CongruentDissection 3979) : False :=
  not_tile_of_conditions' 3979 C'_3979 D

end Erdos634.Draft.AllN2

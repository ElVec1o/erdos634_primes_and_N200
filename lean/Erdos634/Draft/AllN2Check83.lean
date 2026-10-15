/- AllN2Check83: N = 2406, 2407, 2411, 2413, 2414
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2406_sqf   : LeafSqf 2406   := by decide +kernel
private theorem c2406_range : LeafRange 2406  := by decide +kernel
private theorem c2406_ell   : LeafEll 2406    := by decide +kernel
private theorem c2406_nsq   : NSqChkSq 2406   := by decide +kernel
private theorem c2406_har   : HArithChkSq 2406 := by decide +kernel
private theorem c2406_r     : LeafR 2406      := by decide +kernel
private theorem c2406_e'    : LeafE' 2406     := by decide +kernel
private theorem c2406_f1    : LeafF1 2406     := Or.inl (by decide)
private theorem c2406_s2    : S2ChkSq 2406    := by decide +kernel
private theorem c2406_s3    : S3ChkSq 2406    := by decide +kernel
private theorem c2406_iso   : LeafIso 2406    := by decide +kernel
private theorem c2406_nof2  : NoF2ChkSq 2406  := by decide +kernel
private theorem c2406_nof3  : NoF3ChkSq 2406  := by decide +kernel
private theorem c2406_nof4z : NoF4zChkSq 2406 := by decide +kernel
theorem C'_2406 : C' 2406 :=
  ⟨c2406_sqf, c2406_range, c2406_ell, leafNSq_of_sq c2406_nsq, leafHAr_of_sq c2406_har,
   c2406_r, c2406_e', c2406_f1, leafS2_of_sq c2406_s2, leafS3_of_sq c2406_s3,
   c2406_iso, leafR8_of_sq c2406_nof2 c2406_nof3 c2406_nof4z⟩
theorem not_tile'_2406 (D : CongruentDissection 2406) : False :=
  not_tile_of_conditions' 2406 C'_2406 D

private theorem c2407_sqf   : LeafSqf 2407   := by decide +kernel
private theorem c2407_range : LeafRange 2407  := by decide +kernel
private theorem c2407_ell   : LeafEll 2407    := by decide +kernel
private theorem c2407_nsq   : NSqChkSq 2407   := by decide +kernel
private theorem c2407_har   : HArithChkSq 2407 := by decide +kernel
private theorem c2407_r     : LeafR 2407      := by decide +kernel
private theorem c2407_e'    : LeafE' 2407     := by decide +kernel
private theorem c2407_f1    : LeafF1 2407     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2407_s2    : S2ChkSq 2407    := by decide +kernel
private theorem c2407_s3    : S3ChkSq 2407    := by decide +kernel
private theorem c2407_iso   : LeafIso 2407    := by decide +kernel
private theorem c2407_nof2  : NoF2ChkSq 2407  := by decide +kernel
private theorem c2407_nof3  : NoF3ChkSq 2407  := by decide +kernel
private theorem c2407_nof4z : NoF4zChkSq 2407 := by decide +kernel
theorem C'_2407 : C' 2407 :=
  ⟨c2407_sqf, c2407_range, c2407_ell, leafNSq_of_sq c2407_nsq, leafHAr_of_sq c2407_har,
   c2407_r, c2407_e', c2407_f1, leafS2_of_sq c2407_s2, leafS3_of_sq c2407_s3,
   c2407_iso, leafR8_of_sq c2407_nof2 c2407_nof3 c2407_nof4z⟩
theorem not_tile'_2407 (D : CongruentDissection 2407) : False :=
  not_tile_of_conditions' 2407 C'_2407 D

private theorem c2411_sqf   : LeafSqf 2411   := by decide +kernel
private theorem c2411_range : LeafRange 2411  := by decide +kernel
private theorem c2411_ell   : LeafEll 2411    := by decide +kernel
private theorem c2411_nsq   : NSqChkSq 2411   := by decide +kernel
private theorem c2411_har   : HArithChkSq 2411 := by decide +kernel
private theorem c2411_r     : LeafR 2411      := by decide +kernel
private theorem c2411_e'    : LeafE' 2411     := by decide +kernel
private theorem c2411_f1    : LeafF1 2411     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2411_s2    : S2ChkSq 2411    := by decide +kernel
private theorem c2411_s3    : S3ChkSq 2411    := by decide +kernel
private theorem c2411_iso   : LeafIso 2411    := by decide +kernel
private theorem c2411_nof2  : NoF2ChkSq 2411  := by decide +kernel
private theorem c2411_nof3  : NoF3ChkSq 2411  := by decide +kernel
private theorem c2411_nof4z : NoF4zChkSq 2411 := by decide +kernel
theorem C'_2411 : C' 2411 :=
  ⟨c2411_sqf, c2411_range, c2411_ell, leafNSq_of_sq c2411_nsq, leafHAr_of_sq c2411_har,
   c2411_r, c2411_e', c2411_f1, leafS2_of_sq c2411_s2, leafS3_of_sq c2411_s3,
   c2411_iso, leafR8_of_sq c2411_nof2 c2411_nof3 c2411_nof4z⟩
theorem not_tile'_2411 (D : CongruentDissection 2411) : False :=
  not_tile_of_conditions' 2411 C'_2411 D

private theorem c2413_sqf   : LeafSqf 2413   := by decide +kernel
private theorem c2413_range : LeafRange 2413  := by decide +kernel
private theorem c2413_ell   : LeafEll 2413    := by decide +kernel
private theorem c2413_nsq   : NSqChkSq 2413   := by decide +kernel
private theorem c2413_har   : HArithChkSq 2413 := by decide +kernel
private theorem c2413_r     : LeafR 2413      := by decide +kernel
private theorem c2413_e'    : LeafE' 2413     := by decide +kernel
private theorem c2413_f1    : LeafF1 2413     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2413_s2    : S2ChkSq 2413    := by decide +kernel
private theorem c2413_s3    : S3ChkSq 2413    := by decide +kernel
private theorem c2413_iso   : LeafIso 2413    := by decide +kernel
private theorem c2413_nof2  : NoF2ChkSq 2413  := by decide +kernel
private theorem c2413_nof3  : NoF3ChkSq 2413  := by decide +kernel
private theorem c2413_nof4z : NoF4zChkSq 2413 := by decide +kernel
theorem C'_2413 : C' 2413 :=
  ⟨c2413_sqf, c2413_range, c2413_ell, leafNSq_of_sq c2413_nsq, leafHAr_of_sq c2413_har,
   c2413_r, c2413_e', c2413_f1, leafS2_of_sq c2413_s2, leafS3_of_sq c2413_s3,
   c2413_iso, leafR8_of_sq c2413_nof2 c2413_nof3 c2413_nof4z⟩
theorem not_tile'_2413 (D : CongruentDissection 2413) : False :=
  not_tile_of_conditions' 2413 C'_2413 D

private theorem c2414_sqf   : LeafSqf 2414   := by decide +kernel
private theorem c2414_range : LeafRange 2414  := by decide +kernel
private theorem c2414_ell   : LeafEll 2414    := by decide +kernel
private theorem c2414_nsq   : NSqChkSq 2414   := by decide +kernel
private theorem c2414_har   : HArithChkSq 2414 := by decide +kernel
private theorem c2414_r     : LeafR 2414      := by decide +kernel
private theorem c2414_e'    : LeafE' 2414     := by decide +kernel
private theorem c2414_f1    : LeafF1 2414     := Or.inl (by decide)
private theorem c2414_s2    : S2ChkSq 2414    := by decide +kernel
private theorem c2414_s3    : S3ChkSq 2414    := by decide +kernel
private theorem c2414_iso   : LeafIso 2414    := by decide +kernel
private theorem c2414_nof2  : NoF2ChkSq 2414  := by decide +kernel
private theorem c2414_nof3  : NoF3ChkSq 2414  := by decide +kernel
private theorem c2414_nof4z : NoF4zChkSq 2414 := by decide +kernel
theorem C'_2414 : C' 2414 :=
  ⟨c2414_sqf, c2414_range, c2414_ell, leafNSq_of_sq c2414_nsq, leafHAr_of_sq c2414_har,
   c2414_r, c2414_e', c2414_f1, leafS2_of_sq c2414_s2, leafS3_of_sq c2414_s3,
   c2414_iso, leafR8_of_sq c2414_nof2 c2414_nof3 c2414_nof4z⟩
theorem not_tile'_2414 (D : CongruentDissection 2414) : False :=
  not_tile_of_conditions' 2414 C'_2414 D

end Erdos634.Draft.AllN2

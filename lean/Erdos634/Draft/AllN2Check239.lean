/- AllN2Check239: N = 4406, 4413, 4414, 4415, 4417
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4406_sqf   : LeafSqf 4406   := by decide +kernel
private theorem c4406_range : LeafRange 4406  := by decide +kernel
private theorem c4406_ell   : LeafEll 4406    := by decide +kernel
private theorem c4406_nsq   : NSqChkSq 4406   := by decide +kernel
private theorem c4406_har   : HArithChkSq 4406 := by decide +kernel
private theorem c4406_r     : LeafR 4406      := by decide +kernel
private theorem c4406_e'    : LeafE' 4406     := by decide +kernel
private theorem c4406_f1    : LeafF1 4406     := Or.inl (by decide)
private theorem c4406_s2    : S2ChkSq 4406    := by decide +kernel
private theorem c4406_s3    : S3ChkSq 4406    := by decide +kernel
private theorem c4406_iso   : LeafIso 4406    := by decide +kernel
private theorem c4406_nof2  : NoF2ChkSq 4406  := by decide +kernel
private theorem c4406_nof3  : NoF3ChkSq 4406  := by decide +kernel
private theorem c4406_nof4z : NoF4zChkSq 4406 := by decide +kernel
theorem C'_4406 : C' 4406 :=
  ⟨c4406_sqf, c4406_range, c4406_ell, leafNSq_of_sq c4406_nsq, leafHAr_of_sq c4406_har,
   c4406_r, c4406_e', c4406_f1, leafS2_of_sq c4406_s2, leafS3_of_sq c4406_s3,
   c4406_iso, leafR8_of_sq c4406_nof2 c4406_nof3 c4406_nof4z⟩
theorem not_tile'_4406 (D : CongruentDissection 4406) : False :=
  not_tile_of_conditions' 4406 C'_4406 D

private theorem c4413_sqf   : LeafSqf 4413   := by decide +kernel
private theorem c4413_range : LeafRange 4413  := by decide +kernel
private theorem c4413_ell   : LeafEll 4413    := by decide +kernel
private theorem c4413_nsq   : NSqChkSq 4413   := by decide +kernel
private theorem c4413_har   : HArithChkSq 4413 := by decide +kernel
private theorem c4413_r     : LeafR 4413      := by decide +kernel
private theorem c4413_e'    : LeafE' 4413     := by decide +kernel
private theorem c4413_f1    : LeafF1 4413     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4413_s2    : S2ChkSq 4413    := by decide +kernel
private theorem c4413_s3    : S3ChkSq 4413    := by decide +kernel
private theorem c4413_iso   : LeafIso 4413    := by decide +kernel
private theorem c4413_nof2  : NoF2ChkSq 4413  := by decide +kernel
private theorem c4413_nof3  : NoF3ChkSq 4413  := by decide +kernel
private theorem c4413_nof4z : NoF4zChkSq 4413 := by decide +kernel
theorem C'_4413 : C' 4413 :=
  ⟨c4413_sqf, c4413_range, c4413_ell, leafNSq_of_sq c4413_nsq, leafHAr_of_sq c4413_har,
   c4413_r, c4413_e', c4413_f1, leafS2_of_sq c4413_s2, leafS3_of_sq c4413_s3,
   c4413_iso, leafR8_of_sq c4413_nof2 c4413_nof3 c4413_nof4z⟩
theorem not_tile'_4413 (D : CongruentDissection 4413) : False :=
  not_tile_of_conditions' 4413 C'_4413 D

private theorem c4414_sqf   : LeafSqf 4414   := by decide +kernel
private theorem c4414_range : LeafRange 4414  := by decide +kernel
private theorem c4414_ell   : LeafEll 4414    := by decide +kernel
private theorem c4414_nsq   : NSqChkSq 4414   := by decide +kernel
private theorem c4414_har   : HArithChkSq 4414 := by decide +kernel
private theorem c4414_r     : LeafR 4414      := by decide +kernel
private theorem c4414_e'    : LeafE' 4414     := by decide +kernel
private theorem c4414_f1    : LeafF1 4414     := Or.inl (by decide)
private theorem c4414_s2    : S2ChkSq 4414    := by decide +kernel
private theorem c4414_s3    : S3ChkSq 4414    := by decide +kernel
private theorem c4414_iso   : LeafIso 4414    := by decide +kernel
private theorem c4414_nof2  : NoF2ChkSq 4414  := by decide +kernel
private theorem c4414_nof3  : NoF3ChkSq 4414  := by decide +kernel
private theorem c4414_nof4z : NoF4zChkSq 4414 := by decide +kernel
theorem C'_4414 : C' 4414 :=
  ⟨c4414_sqf, c4414_range, c4414_ell, leafNSq_of_sq c4414_nsq, leafHAr_of_sq c4414_har,
   c4414_r, c4414_e', c4414_f1, leafS2_of_sq c4414_s2, leafS3_of_sq c4414_s3,
   c4414_iso, leafR8_of_sq c4414_nof2 c4414_nof3 c4414_nof4z⟩
theorem not_tile'_4414 (D : CongruentDissection 4414) : False :=
  not_tile_of_conditions' 4414 C'_4414 D

private theorem c4415_sqf   : LeafSqf 4415   := by decide +kernel
private theorem c4415_range : LeafRange 4415  := by decide +kernel
private theorem c4415_ell   : LeafEll 4415    := by decide +kernel
private theorem c4415_nsq   : NSqChkSq 4415   := by decide +kernel
private theorem c4415_har   : HArithChkSq 4415 := by decide +kernel
private theorem c4415_r     : LeafR 4415      := by decide +kernel
private theorem c4415_e'    : LeafE' 4415     := by decide +kernel
private theorem c4415_f1    : LeafF1 4415     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4415_s2    : S2ChkSq 4415    := by decide +kernel
private theorem c4415_s3    : S3ChkSq 4415    := by decide +kernel
private theorem c4415_iso   : LeafIso 4415    := by decide +kernel
private theorem c4415_nof2  : NoF2ChkSq 4415  := by decide +kernel
private theorem c4415_nof3  : NoF3ChkSq 4415  := by decide +kernel
private theorem c4415_nof4z : NoF4zChkSq 4415 := by decide +kernel
theorem C'_4415 : C' 4415 :=
  ⟨c4415_sqf, c4415_range, c4415_ell, leafNSq_of_sq c4415_nsq, leafHAr_of_sq c4415_har,
   c4415_r, c4415_e', c4415_f1, leafS2_of_sq c4415_s2, leafS3_of_sq c4415_s3,
   c4415_iso, leafR8_of_sq c4415_nof2 c4415_nof3 c4415_nof4z⟩
theorem not_tile'_4415 (D : CongruentDissection 4415) : False :=
  not_tile_of_conditions' 4415 C'_4415 D

private theorem c4417_sqf   : LeafSqf 4417   := by decide +kernel
private theorem c4417_range : LeafRange 4417  := by decide +kernel
private theorem c4417_ell   : LeafEll 4417    := by decide +kernel
private theorem c4417_nsq   : NSqChkSq 4417   := by decide +kernel
private theorem c4417_har   : HArithChkSq 4417 := by decide +kernel
private theorem c4417_r     : LeafR 4417      := by decide +kernel
private theorem c4417_e'    : LeafE' 4417     := by decide +kernel
private theorem c4417_f1    : LeafF1 4417     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4417_s2    : S2ChkSq 4417    := by decide +kernel
private theorem c4417_s3    : S3ChkSq 4417    := by decide +kernel
private theorem c4417_iso   : LeafIso 4417    := by decide +kernel
private theorem c4417_nof2  : NoF2ChkSq 4417  := by decide +kernel
private theorem c4417_nof3  : NoF3ChkSq 4417  := by decide +kernel
private theorem c4417_nof4z : NoF4zChkSq 4417 := by decide +kernel
theorem C'_4417 : C' 4417 :=
  ⟨c4417_sqf, c4417_range, c4417_ell, leafNSq_of_sq c4417_nsq, leafHAr_of_sq c4417_har,
   c4417_r, c4417_e', c4417_f1, leafS2_of_sq c4417_s2, leafS3_of_sq c4417_s3,
   c4417_iso, leafR8_of_sq c4417_nof2 c4417_nof3 c4417_nof4z⟩
theorem not_tile'_4417 (D : CongruentDissection 4417) : False :=
  not_tile_of_conditions' 4417 C'_4417 D

end Erdos634.Draft.AllN2

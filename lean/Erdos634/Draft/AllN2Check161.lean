/- AllN2Check161: N = 3391, 3395, 3397, 3398, 3401
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3391_sqf   : LeafSqf 3391   := by decide +kernel
private theorem c3391_range : LeafRange 3391  := by decide +kernel
private theorem c3391_ell   : LeafEll 3391    := by decide +kernel
private theorem c3391_nsq   : NSqChkSq 3391   := by decide +kernel
private theorem c3391_har   : HArithChkSq 3391 := by decide +kernel
private theorem c3391_r     : LeafR 3391      := by decide +kernel
private theorem c3391_e'    : LeafE' 3391     := by decide +kernel
private theorem c3391_f1    : LeafF1 3391     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3391_s2    : S2ChkSq 3391    := by decide +kernel
private theorem c3391_s3    : S3ChkSq 3391    := by decide +kernel
private theorem c3391_iso   : LeafIso 3391    := by decide +kernel
private theorem c3391_nof2  : NoF2ChkSq 3391  := by decide +kernel
private theorem c3391_nof3  : NoF3ChkSq 3391  := by decide +kernel
private theorem c3391_nof4z : NoF4zChkSq 3391 := by decide +kernel
theorem C'_3391 : C' 3391 :=
  ⟨c3391_sqf, c3391_range, c3391_ell, leafNSq_of_sq c3391_nsq, leafHAr_of_sq c3391_har,
   c3391_r, c3391_e', c3391_f1, leafS2_of_sq c3391_s2, leafS3_of_sq c3391_s3,
   c3391_iso, leafR8_of_sq c3391_nof2 c3391_nof3 c3391_nof4z⟩
theorem not_tile'_3391 (D : CongruentDissection 3391) : False :=
  not_tile_of_conditions' 3391 C'_3391 D

private theorem c3395_sqf   : LeafSqf 3395   := by decide +kernel
private theorem c3395_range : LeafRange 3395  := by decide +kernel
private theorem c3395_ell   : LeafEll 3395    := by decide +kernel
private theorem c3395_nsq   : NSqChkSq 3395   := by decide +kernel
private theorem c3395_har   : HArithChkSq 3395 := by decide +kernel
private theorem c3395_r     : LeafR 3395      := by decide +kernel
private theorem c3395_e'    : LeafE' 3395     := by decide +kernel
private theorem c3395_f1    : LeafF1 3395     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3395_s2    : S2ChkSq 3395    := by decide +kernel
private theorem c3395_s3    : S3ChkSq 3395    := by decide +kernel
private theorem c3395_iso   : LeafIso 3395    := by decide +kernel
private theorem c3395_nof2  : NoF2ChkSq 3395  := by decide +kernel
private theorem c3395_nof3  : NoF3ChkSq 3395  := by decide +kernel
private theorem c3395_nof4z : NoF4zChkSq 3395 := by decide +kernel
theorem C'_3395 : C' 3395 :=
  ⟨c3395_sqf, c3395_range, c3395_ell, leafNSq_of_sq c3395_nsq, leafHAr_of_sq c3395_har,
   c3395_r, c3395_e', c3395_f1, leafS2_of_sq c3395_s2, leafS3_of_sq c3395_s3,
   c3395_iso, leafR8_of_sq c3395_nof2 c3395_nof3 c3395_nof4z⟩
theorem not_tile'_3395 (D : CongruentDissection 3395) : False :=
  not_tile_of_conditions' 3395 C'_3395 D

private theorem c3397_sqf   : LeafSqf 3397   := by decide +kernel
private theorem c3397_range : LeafRange 3397  := by decide +kernel
private theorem c3397_ell   : LeafEll 3397    := by decide +kernel
private theorem c3397_nsq   : NSqChkSq 3397   := by decide +kernel
private theorem c3397_har   : HArithChkSq 3397 := by decide +kernel
private theorem c3397_r     : LeafR 3397      := by decide +kernel
private theorem c3397_e'    : LeafE' 3397     := by decide +kernel
private theorem c3397_f1    : LeafF1 3397     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3397_s2    : S2ChkSq 3397    := by decide +kernel
private theorem c3397_s3    : S3ChkSq 3397    := by decide +kernel
private theorem c3397_iso   : LeafIso 3397    := by decide +kernel
private theorem c3397_nof2  : NoF2ChkSq 3397  := by decide +kernel
private theorem c3397_nof3  : NoF3ChkSq 3397  := by decide +kernel
private theorem c3397_nof4z : NoF4zChkSq 3397 := by decide +kernel
theorem C'_3397 : C' 3397 :=
  ⟨c3397_sqf, c3397_range, c3397_ell, leafNSq_of_sq c3397_nsq, leafHAr_of_sq c3397_har,
   c3397_r, c3397_e', c3397_f1, leafS2_of_sq c3397_s2, leafS3_of_sq c3397_s3,
   c3397_iso, leafR8_of_sq c3397_nof2 c3397_nof3 c3397_nof4z⟩
theorem not_tile'_3397 (D : CongruentDissection 3397) : False :=
  not_tile_of_conditions' 3397 C'_3397 D

private theorem c3398_sqf   : LeafSqf 3398   := by decide +kernel
private theorem c3398_range : LeafRange 3398  := by decide +kernel
private theorem c3398_ell   : LeafEll 3398    := by decide +kernel
private theorem c3398_nsq   : NSqChkSq 3398   := by decide +kernel
private theorem c3398_har   : HArithChkSq 3398 := by decide +kernel
private theorem c3398_r     : LeafR 3398      := by decide +kernel
private theorem c3398_e'    : LeafE' 3398     := by decide +kernel
private theorem c3398_f1    : LeafF1 3398     := Or.inl (by decide)
private theorem c3398_s2    : S2ChkSq 3398    := by decide +kernel
private theorem c3398_s3    : S3ChkSq 3398    := by decide +kernel
private theorem c3398_iso   : LeafIso 3398    := by decide +kernel
private theorem c3398_nof2  : NoF2ChkSq 3398  := by decide +kernel
private theorem c3398_nof3  : NoF3ChkSq 3398  := by decide +kernel
private theorem c3398_nof4z : NoF4zChkSq 3398 := by decide +kernel
theorem C'_3398 : C' 3398 :=
  ⟨c3398_sqf, c3398_range, c3398_ell, leafNSq_of_sq c3398_nsq, leafHAr_of_sq c3398_har,
   c3398_r, c3398_e', c3398_f1, leafS2_of_sq c3398_s2, leafS3_of_sq c3398_s3,
   c3398_iso, leafR8_of_sq c3398_nof2 c3398_nof3 c3398_nof4z⟩
theorem not_tile'_3398 (D : CongruentDissection 3398) : False :=
  not_tile_of_conditions' 3398 C'_3398 D

private theorem c3401_sqf   : LeafSqf 3401   := by decide +kernel
private theorem c3401_range : LeafRange 3401  := by decide +kernel
private theorem c3401_ell   : LeafEll 3401    := by decide +kernel
private theorem c3401_nsq   : NSqChkSq 3401   := by decide +kernel
private theorem c3401_har   : HArithChkSq 3401 := by decide +kernel
private theorem c3401_r     : LeafR 3401      := by decide +kernel
private theorem c3401_e'    : LeafE' 3401     := by decide +kernel
private theorem c3401_f1    : LeafF1 3401     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3401_s2    : S2ChkSq 3401    := by decide +kernel
private theorem c3401_s3    : S3ChkSq 3401    := by decide +kernel
private theorem c3401_iso   : LeafIso 3401    := by decide +kernel
private theorem c3401_nof2  : NoF2ChkSq 3401  := by decide +kernel
private theorem c3401_nof3  : NoF3ChkSq 3401  := by decide +kernel
private theorem c3401_nof4z : NoF4zChkSq 3401 := by decide +kernel
theorem C'_3401 : C' 3401 :=
  ⟨c3401_sqf, c3401_range, c3401_ell, leafNSq_of_sq c3401_nsq, leafHAr_of_sq c3401_har,
   c3401_r, c3401_e', c3401_f1, leafS2_of_sq c3401_s2, leafS3_of_sq c3401_s3,
   c3401_iso, leafR8_of_sq c3401_nof2 c3401_nof3 c3401_nof4z⟩
theorem not_tile'_3401 (D : CongruentDissection 3401) : False :=
  not_tile_of_conditions' 3401 C'_3401 D

end Erdos634.Draft.AllN2

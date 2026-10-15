/- AllN2Check81: N = 2387, 2390, 2391, 2395, 2397
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2387_sqf   : LeafSqf 2387   := by decide +kernel
private theorem c2387_range : LeafRange 2387  := by decide +kernel
private theorem c2387_ell   : LeafEll 2387    := by decide +kernel
private theorem c2387_nsq   : NSqChkSq 2387   := by decide +kernel
private theorem c2387_har   : HArithChkSq 2387 := by decide +kernel
private theorem c2387_r     : LeafR 2387      := by decide +kernel
private theorem c2387_e'    : LeafE' 2387     := by decide +kernel
private theorem c2387_f1    : LeafF1 2387     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2387_s2    : S2ChkSq 2387    := by decide +kernel
private theorem c2387_s3    : S3ChkSq 2387    := by decide +kernel
private theorem c2387_iso   : LeafIso 2387    := by decide +kernel
private theorem c2387_nof2  : NoF2ChkSq 2387  := by decide +kernel
private theorem c2387_nof3  : NoF3ChkSq 2387  := by decide +kernel
private theorem c2387_nof4z : NoF4zChkSq 2387 := by decide +kernel
theorem C'_2387 : C' 2387 :=
  ⟨c2387_sqf, c2387_range, c2387_ell, leafNSq_of_sq c2387_nsq, leafHAr_of_sq c2387_har,
   c2387_r, c2387_e', c2387_f1, leafS2_of_sq c2387_s2, leafS3_of_sq c2387_s3,
   c2387_iso, leafR8_of_sq c2387_nof2 c2387_nof3 c2387_nof4z⟩
theorem not_tile'_2387 (D : CongruentDissection 2387) : False :=
  not_tile_of_conditions' 2387 C'_2387 D

private theorem c2390_sqf   : LeafSqf 2390   := by decide +kernel
private theorem c2390_range : LeafRange 2390  := by decide +kernel
private theorem c2390_ell   : LeafEll 2390    := by decide +kernel
private theorem c2390_nsq   : NSqChkSq 2390   := by decide +kernel
private theorem c2390_har   : HArithChkSq 2390 := by decide +kernel
private theorem c2390_r     : LeafR 2390      := by decide +kernel
private theorem c2390_e'    : LeafE' 2390     := by decide +kernel
private theorem c2390_f1    : LeafF1 2390     := Or.inl (by decide)
private theorem c2390_s2    : S2ChkSq 2390    := by decide +kernel
private theorem c2390_s3    : S3ChkSq 2390    := by decide +kernel
private theorem c2390_iso   : LeafIso 2390    := by decide +kernel
private theorem c2390_nof2  : NoF2ChkSq 2390  := by decide +kernel
private theorem c2390_nof3  : NoF3ChkSq 2390  := by decide +kernel
private theorem c2390_nof4z : NoF4zChkSq 2390 := by decide +kernel
theorem C'_2390 : C' 2390 :=
  ⟨c2390_sqf, c2390_range, c2390_ell, leafNSq_of_sq c2390_nsq, leafHAr_of_sq c2390_har,
   c2390_r, c2390_e', c2390_f1, leafS2_of_sq c2390_s2, leafS3_of_sq c2390_s3,
   c2390_iso, leafR8_of_sq c2390_nof2 c2390_nof3 c2390_nof4z⟩
theorem not_tile'_2390 (D : CongruentDissection 2390) : False :=
  not_tile_of_conditions' 2390 C'_2390 D

private theorem c2391_sqf   : LeafSqf 2391   := by decide +kernel
private theorem c2391_range : LeafRange 2391  := by decide +kernel
private theorem c2391_ell   : LeafEll 2391    := by decide +kernel
private theorem c2391_nsq   : NSqChkSq 2391   := by decide +kernel
private theorem c2391_har   : HArithChkSq 2391 := by decide +kernel
private theorem c2391_r     : LeafR 2391      := by decide +kernel
private theorem c2391_e'    : LeafE' 2391     := by decide +kernel
private theorem c2391_f1    : LeafF1 2391     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2391_s2    : S2ChkSq 2391    := by decide +kernel
private theorem c2391_s3    : S3ChkSq 2391    := by decide +kernel
private theorem c2391_iso   : LeafIso 2391    := by decide +kernel
private theorem c2391_nof2  : NoF2ChkSq 2391  := by decide +kernel
private theorem c2391_nof3  : NoF3ChkSq 2391  := by decide +kernel
private theorem c2391_nof4z : NoF4zChkSq 2391 := by decide +kernel
theorem C'_2391 : C' 2391 :=
  ⟨c2391_sqf, c2391_range, c2391_ell, leafNSq_of_sq c2391_nsq, leafHAr_of_sq c2391_har,
   c2391_r, c2391_e', c2391_f1, leafS2_of_sq c2391_s2, leafS3_of_sq c2391_s3,
   c2391_iso, leafR8_of_sq c2391_nof2 c2391_nof3 c2391_nof4z⟩
theorem not_tile'_2391 (D : CongruentDissection 2391) : False :=
  not_tile_of_conditions' 2391 C'_2391 D

private theorem c2395_sqf   : LeafSqf 2395   := by decide +kernel
private theorem c2395_range : LeafRange 2395  := by decide +kernel
private theorem c2395_ell   : LeafEll 2395    := by decide +kernel
private theorem c2395_nsq   : NSqChkSq 2395   := by decide +kernel
private theorem c2395_har   : HArithChkSq 2395 := by decide +kernel
private theorem c2395_r     : LeafR 2395      := by decide +kernel
private theorem c2395_e'    : LeafE' 2395     := by decide +kernel
private theorem c2395_f1    : LeafF1 2395     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2395_s2    : S2ChkSq 2395    := by decide +kernel
private theorem c2395_s3    : S3ChkSq 2395    := by decide +kernel
private theorem c2395_iso   : LeafIso 2395    := by decide +kernel
private theorem c2395_nof2  : NoF2ChkSq 2395  := by decide +kernel
private theorem c2395_nof3  : NoF3ChkSq 2395  := by decide +kernel
private theorem c2395_nof4z : NoF4zChkSq 2395 := by decide +kernel
theorem C'_2395 : C' 2395 :=
  ⟨c2395_sqf, c2395_range, c2395_ell, leafNSq_of_sq c2395_nsq, leafHAr_of_sq c2395_har,
   c2395_r, c2395_e', c2395_f1, leafS2_of_sq c2395_s2, leafS3_of_sq c2395_s3,
   c2395_iso, leafR8_of_sq c2395_nof2 c2395_nof3 c2395_nof4z⟩
theorem not_tile'_2395 (D : CongruentDissection 2395) : False :=
  not_tile_of_conditions' 2395 C'_2395 D

private theorem c2397_sqf   : LeafSqf 2397   := by decide +kernel
private theorem c2397_range : LeafRange 2397  := by decide +kernel
private theorem c2397_ell   : LeafEll 2397    := by decide +kernel
private theorem c2397_nsq   : NSqChkSq 2397   := by decide +kernel
private theorem c2397_har   : HArithChkSq 2397 := by decide +kernel
private theorem c2397_r     : LeafR 2397      := by decide +kernel
private theorem c2397_e'    : LeafE' 2397     := by decide +kernel
private theorem c2397_f1    : LeafF1 2397     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2397_s2    : S2ChkSq 2397    := by decide +kernel
private theorem c2397_s3    : S3ChkSq 2397    := by decide +kernel
private theorem c2397_iso   : LeafIso 2397    := by decide +kernel
private theorem c2397_nof2  : NoF2ChkSq 2397  := by decide +kernel
private theorem c2397_nof3  : NoF3ChkSq 2397  := by decide +kernel
private theorem c2397_nof4z : NoF4zChkSq 2397 := by decide +kernel
theorem C'_2397 : C' 2397 :=
  ⟨c2397_sqf, c2397_range, c2397_ell, leafNSq_of_sq c2397_nsq, leafHAr_of_sq c2397_har,
   c2397_r, c2397_e', c2397_f1, leafS2_of_sq c2397_s2, leafS3_of_sq c2397_s3,
   c2397_iso, leafR8_of_sq c2397_nof2 c2397_nof3 c2397_nof4z⟩
theorem not_tile'_2397 (D : CongruentDissection 2397) : False :=
  not_tile_of_conditions' 2397 C'_2397 D

end Erdos634.Draft.AllN2

/- AllN2Check80: N = 2370, 2371, 2374, 2382, 2383
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2370_sqf   : LeafSqf 2370   := by decide +kernel
private theorem c2370_range : LeafRange 2370  := by decide +kernel
private theorem c2370_ell   : LeafEll 2370    := by decide +kernel
private theorem c2370_nsq   : NSqChkSq 2370   := by decide +kernel
private theorem c2370_har   : HArithChkSq 2370 := by decide +kernel
private theorem c2370_r     : LeafR 2370      := by decide +kernel
private theorem c2370_e'    : LeafE' 2370     := by decide +kernel
private theorem c2370_f1    : LeafF1 2370     := Or.inl (by decide)
private theorem c2370_s2    : S2ChkSq 2370    := by decide +kernel
private theorem c2370_s3    : S3ChkSq 2370    := by decide +kernel
private theorem c2370_iso   : LeafIso 2370    := by decide +kernel
private theorem c2370_nof2  : NoF2ChkSq 2370  := by decide +kernel
private theorem c2370_nof3  : NoF3ChkSq 2370  := by decide +kernel
private theorem c2370_nof4z : NoF4zChkSq 2370 := by decide +kernel
theorem C'_2370 : C' 2370 :=
  ⟨c2370_sqf, c2370_range, c2370_ell, leafNSq_of_sq c2370_nsq, leafHAr_of_sq c2370_har,
   c2370_r, c2370_e', c2370_f1, leafS2_of_sq c2370_s2, leafS3_of_sq c2370_s3,
   c2370_iso, leafR8_of_sq c2370_nof2 c2370_nof3 c2370_nof4z⟩
theorem not_tile'_2370 (D : CongruentDissection 2370) : False :=
  not_tile_of_conditions' 2370 C'_2370 D

private theorem c2371_sqf   : LeafSqf 2371   := by decide +kernel
private theorem c2371_range : LeafRange 2371  := by decide +kernel
private theorem c2371_ell   : LeafEll 2371    := by decide +kernel
private theorem c2371_nsq   : NSqChkSq 2371   := by decide +kernel
private theorem c2371_har   : HArithChkSq 2371 := by decide +kernel
private theorem c2371_r     : LeafR 2371      := by decide +kernel
private theorem c2371_e'    : LeafE' 2371     := by decide +kernel
private theorem c2371_f1    : LeafF1 2371     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2371_s2    : S2ChkSq 2371    := by decide +kernel
private theorem c2371_s3    : S3ChkSq 2371    := by decide +kernel
private theorem c2371_iso   : LeafIso 2371    := by decide +kernel
private theorem c2371_nof2  : NoF2ChkSq 2371  := by decide +kernel
private theorem c2371_nof3  : NoF3ChkSq 2371  := by decide +kernel
private theorem c2371_nof4z : NoF4zChkSq 2371 := by decide +kernel
theorem C'_2371 : C' 2371 :=
  ⟨c2371_sqf, c2371_range, c2371_ell, leafNSq_of_sq c2371_nsq, leafHAr_of_sq c2371_har,
   c2371_r, c2371_e', c2371_f1, leafS2_of_sq c2371_s2, leafS3_of_sq c2371_s3,
   c2371_iso, leafR8_of_sq c2371_nof2 c2371_nof3 c2371_nof4z⟩
theorem not_tile'_2371 (D : CongruentDissection 2371) : False :=
  not_tile_of_conditions' 2371 C'_2371 D

private theorem c2374_sqf   : LeafSqf 2374   := by decide +kernel
private theorem c2374_range : LeafRange 2374  := by decide +kernel
private theorem c2374_ell   : LeafEll 2374    := by decide +kernel
private theorem c2374_nsq   : NSqChkSq 2374   := by decide +kernel
private theorem c2374_har   : HArithChkSq 2374 := by decide +kernel
private theorem c2374_r     : LeafR 2374      := by decide +kernel
private theorem c2374_e'    : LeafE' 2374     := by decide +kernel
private theorem c2374_f1    : LeafF1 2374     := Or.inl (by decide)
private theorem c2374_s2    : S2ChkSq 2374    := by decide +kernel
private theorem c2374_s3    : S3ChkSq 2374    := by decide +kernel
private theorem c2374_iso   : LeafIso 2374    := by decide +kernel
private theorem c2374_nof2  : NoF2ChkSq 2374  := by decide +kernel
private theorem c2374_nof3  : NoF3ChkSq 2374  := by decide +kernel
private theorem c2374_nof4z : NoF4zChkSq 2374 := by decide +kernel
theorem C'_2374 : C' 2374 :=
  ⟨c2374_sqf, c2374_range, c2374_ell, leafNSq_of_sq c2374_nsq, leafHAr_of_sq c2374_har,
   c2374_r, c2374_e', c2374_f1, leafS2_of_sq c2374_s2, leafS3_of_sq c2374_s3,
   c2374_iso, leafR8_of_sq c2374_nof2 c2374_nof3 c2374_nof4z⟩
theorem not_tile'_2374 (D : CongruentDissection 2374) : False :=
  not_tile_of_conditions' 2374 C'_2374 D

private theorem c2382_sqf   : LeafSqf 2382   := by decide +kernel
private theorem c2382_range : LeafRange 2382  := by decide +kernel
private theorem c2382_ell   : LeafEll 2382    := by decide +kernel
private theorem c2382_nsq   : NSqChkSq 2382   := by decide +kernel
private theorem c2382_har   : HArithChkSq 2382 := by decide +kernel
private theorem c2382_r     : LeafR 2382      := by decide +kernel
private theorem c2382_e'    : LeafE' 2382     := by decide +kernel
private theorem c2382_f1    : LeafF1 2382     := Or.inl (by decide)
private theorem c2382_s2    : S2ChkSq 2382    := by decide +kernel
private theorem c2382_s3    : S3ChkSq 2382    := by decide +kernel
private theorem c2382_iso   : LeafIso 2382    := by decide +kernel
private theorem c2382_nof2  : NoF2ChkSq 2382  := by decide +kernel
private theorem c2382_nof3  : NoF3ChkSq 2382  := by decide +kernel
private theorem c2382_nof4z : NoF4zChkSq 2382 := by decide +kernel
theorem C'_2382 : C' 2382 :=
  ⟨c2382_sqf, c2382_range, c2382_ell, leafNSq_of_sq c2382_nsq, leafHAr_of_sq c2382_har,
   c2382_r, c2382_e', c2382_f1, leafS2_of_sq c2382_s2, leafS3_of_sq c2382_s3,
   c2382_iso, leafR8_of_sq c2382_nof2 c2382_nof3 c2382_nof4z⟩
theorem not_tile'_2382 (D : CongruentDissection 2382) : False :=
  not_tile_of_conditions' 2382 C'_2382 D

private theorem c2383_sqf   : LeafSqf 2383   := by decide +kernel
private theorem c2383_range : LeafRange 2383  := by decide +kernel
private theorem c2383_ell   : LeafEll 2383    := by decide +kernel
private theorem c2383_nsq   : NSqChkSq 2383   := by decide +kernel
private theorem c2383_har   : HArithChkSq 2383 := by decide +kernel
private theorem c2383_r     : LeafR 2383      := by decide +kernel
private theorem c2383_e'    : LeafE' 2383     := by decide +kernel
private theorem c2383_f1    : LeafF1 2383     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2383_s2    : S2ChkSq 2383    := by decide +kernel
private theorem c2383_s3    : S3ChkSq 2383    := by decide +kernel
private theorem c2383_iso   : LeafIso 2383    := by decide +kernel
private theorem c2383_nof2  : NoF2ChkSq 2383  := by decide +kernel
private theorem c2383_nof3  : NoF3ChkSq 2383  := by decide +kernel
private theorem c2383_nof4z : NoF4zChkSq 2383 := by decide +kernel
theorem C'_2383 : C' 2383 :=
  ⟨c2383_sqf, c2383_range, c2383_ell, leafNSq_of_sq c2383_nsq, leafHAr_of_sq c2383_har,
   c2383_r, c2383_e', c2383_f1, leafS2_of_sq c2383_s2, leafS3_of_sq c2383_s3,
   c2383_iso, leafR8_of_sq c2383_nof2 c2383_nof3 c2383_nof4z⟩
theorem not_tile'_2383 (D : CongruentDissection 2383) : False :=
  not_tile_of_conditions' 2383 C'_2383 D

end Erdos634.Draft.AllN2

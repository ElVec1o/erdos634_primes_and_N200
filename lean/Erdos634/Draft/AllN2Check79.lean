/- AllN2Check79: N = 2359, 2361, 2363, 2365, 2369
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2359_sqf   : LeafSqf 2359   := by decide +kernel
private theorem c2359_range : LeafRange 2359  := by decide +kernel
private theorem c2359_ell   : LeafEll 2359    := by decide +kernel
private theorem c2359_nsq   : NSqChkSq 2359   := by decide +kernel
private theorem c2359_har   : HArithChkSq 2359 := by decide +kernel
private theorem c2359_r     : LeafR 2359      := by decide +kernel
private theorem c2359_e'    : LeafE' 2359     := by decide +kernel
private theorem c2359_f1    : LeafF1 2359     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2359_s2    : S2ChkSq 2359    := by decide +kernel
private theorem c2359_s3    : S3ChkSq 2359    := by decide +kernel
private theorem c2359_iso   : LeafIso 2359    := by decide +kernel
private theorem c2359_nof2  : NoF2ChkSq 2359  := by decide +kernel
private theorem c2359_nof3  : NoF3ChkSq 2359  := by decide +kernel
private theorem c2359_nof4z : NoF4zChkSq 2359 := by decide +kernel
theorem C'_2359 : C' 2359 :=
  ⟨c2359_sqf, c2359_range, c2359_ell, leafNSq_of_sq c2359_nsq, leafHAr_of_sq c2359_har,
   c2359_r, c2359_e', c2359_f1, leafS2_of_sq c2359_s2, leafS3_of_sq c2359_s3,
   c2359_iso, leafR8_of_sq c2359_nof2 c2359_nof3 c2359_nof4z⟩
theorem not_tile'_2359 (D : CongruentDissection 2359) : False :=
  not_tile_of_conditions' 2359 C'_2359 D

private theorem c2361_sqf   : LeafSqf 2361   := by decide +kernel
private theorem c2361_range : LeafRange 2361  := by decide +kernel
private theorem c2361_ell   : LeafEll 2361    := by decide +kernel
private theorem c2361_nsq   : NSqChkSq 2361   := by decide +kernel
private theorem c2361_har   : HArithChkSq 2361 := by decide +kernel
private theorem c2361_r     : LeafR 2361      := by decide +kernel
private theorem c2361_e'    : LeafE' 2361     := by decide +kernel
private theorem c2361_f1    : LeafF1 2361     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2361_s2    : S2ChkSq 2361    := by decide +kernel
private theorem c2361_s3    : S3ChkSq 2361    := by decide +kernel
private theorem c2361_iso   : LeafIso 2361    := by decide +kernel
private theorem c2361_nof2  : NoF2ChkSq 2361  := by decide +kernel
private theorem c2361_nof3  : NoF3ChkSq 2361  := by decide +kernel
private theorem c2361_nof4z : NoF4zChkSq 2361 := by decide +kernel
theorem C'_2361 : C' 2361 :=
  ⟨c2361_sqf, c2361_range, c2361_ell, leafNSq_of_sq c2361_nsq, leafHAr_of_sq c2361_har,
   c2361_r, c2361_e', c2361_f1, leafS2_of_sq c2361_s2, leafS3_of_sq c2361_s3,
   c2361_iso, leafR8_of_sq c2361_nof2 c2361_nof3 c2361_nof4z⟩
theorem not_tile'_2361 (D : CongruentDissection 2361) : False :=
  not_tile_of_conditions' 2361 C'_2361 D

private theorem c2363_sqf   : LeafSqf 2363   := by decide +kernel
private theorem c2363_range : LeafRange 2363  := by decide +kernel
private theorem c2363_ell   : LeafEll 2363    := by decide +kernel
private theorem c2363_nsq   : NSqChkSq 2363   := by decide +kernel
private theorem c2363_har   : HArithChkSq 2363 := by decide +kernel
private theorem c2363_r     : LeafR 2363      := by decide +kernel
private theorem c2363_e'    : LeafE' 2363     := by decide +kernel
private theorem c2363_f1    : LeafF1 2363     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2363_s2    : S2ChkSq 2363    := by decide +kernel
private theorem c2363_s3    : S3ChkSq 2363    := by decide +kernel
private theorem c2363_iso   : LeafIso 2363    := by decide +kernel
private theorem c2363_nof2  : NoF2ChkSq 2363  := by decide +kernel
private theorem c2363_nof3  : NoF3ChkSq 2363  := by decide +kernel
private theorem c2363_nof4z : NoF4zChkSq 2363 := by decide +kernel
theorem C'_2363 : C' 2363 :=
  ⟨c2363_sqf, c2363_range, c2363_ell, leafNSq_of_sq c2363_nsq, leafHAr_of_sq c2363_har,
   c2363_r, c2363_e', c2363_f1, leafS2_of_sq c2363_s2, leafS3_of_sq c2363_s3,
   c2363_iso, leafR8_of_sq c2363_nof2 c2363_nof3 c2363_nof4z⟩
theorem not_tile'_2363 (D : CongruentDissection 2363) : False :=
  not_tile_of_conditions' 2363 C'_2363 D

private theorem c2365_sqf   : LeafSqf 2365   := by decide +kernel
private theorem c2365_range : LeafRange 2365  := by decide +kernel
private theorem c2365_ell   : LeafEll 2365    := by decide +kernel
private theorem c2365_nsq   : NSqChkSq 2365   := by decide +kernel
private theorem c2365_har   : HArithChkSq 2365 := by decide +kernel
private theorem c2365_r     : LeafR 2365      := by decide +kernel
private theorem c2365_e'    : LeafE' 2365     := by decide +kernel
private theorem c2365_f1    : LeafF1 2365     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2365_s2    : S2ChkSq 2365    := by decide +kernel
private theorem c2365_s3    : S3ChkSq 2365    := by decide +kernel
private theorem c2365_iso   : LeafIso 2365    := by decide +kernel
private theorem c2365_nof2  : NoF2ChkSq 2365  := by decide +kernel
private theorem c2365_nof3  : NoF3ChkSq 2365  := by decide +kernel
private theorem c2365_nof4z : NoF4zChkSq 2365 := by decide +kernel
theorem C'_2365 : C' 2365 :=
  ⟨c2365_sqf, c2365_range, c2365_ell, leafNSq_of_sq c2365_nsq, leafHAr_of_sq c2365_har,
   c2365_r, c2365_e', c2365_f1, leafS2_of_sq c2365_s2, leafS3_of_sq c2365_s3,
   c2365_iso, leafR8_of_sq c2365_nof2 c2365_nof3 c2365_nof4z⟩
theorem not_tile'_2365 (D : CongruentDissection 2365) : False :=
  not_tile_of_conditions' 2365 C'_2365 D

private theorem c2369_sqf   : LeafSqf 2369   := by decide +kernel
private theorem c2369_range : LeafRange 2369  := by decide +kernel
private theorem c2369_ell   : LeafEll 2369    := by decide +kernel
private theorem c2369_nsq   : NSqChkSq 2369   := by decide +kernel
private theorem c2369_har   : HArithChkSq 2369 := by decide +kernel
private theorem c2369_r     : LeafR 2369      := by decide +kernel
private theorem c2369_e'    : LeafE' 2369     := by decide +kernel
private theorem c2369_f1    : LeafF1 2369     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2369_s2    : S2ChkSq 2369    := by decide +kernel
private theorem c2369_s3    : S3ChkSq 2369    := by decide +kernel
private theorem c2369_iso   : LeafIso 2369    := by decide +kernel
private theorem c2369_nof2  : NoF2ChkSq 2369  := by decide +kernel
private theorem c2369_nof3  : NoF3ChkSq 2369  := by decide +kernel
private theorem c2369_nof4z : NoF4zChkSq 2369 := by decide +kernel
theorem C'_2369 : C' 2369 :=
  ⟨c2369_sqf, c2369_range, c2369_ell, leafNSq_of_sq c2369_nsq, leafHAr_of_sq c2369_har,
   c2369_r, c2369_e', c2369_f1, leafS2_of_sq c2369_s2, leafS3_of_sq c2369_s3,
   c2369_iso, leafR8_of_sq c2369_nof2 c2369_nof3 c2369_nof4z⟩
theorem not_tile'_2369 (D : CongruentDissection 2369) : False :=
  not_tile_of_conditions' 2369 C'_2369 D

end Erdos634.Draft.AllN2

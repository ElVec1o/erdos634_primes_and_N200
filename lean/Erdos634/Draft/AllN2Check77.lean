/- AllN2Check77: N = 2334, 2335, 2337, 2338, 2339
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2334_sqf   : LeafSqf 2334   := by decide +kernel
private theorem c2334_range : LeafRange 2334  := by decide +kernel
private theorem c2334_ell   : LeafEll 2334    := by decide +kernel
private theorem c2334_nsq   : NSqChkSq 2334   := by decide +kernel
private theorem c2334_har   : HArithChkSq 2334 := by decide +kernel
private theorem c2334_r     : LeafR 2334      := by decide +kernel
private theorem c2334_e'    : LeafE' 2334     := by decide +kernel
private theorem c2334_f1    : LeafF1 2334     := Or.inl (by decide)
private theorem c2334_s2    : S2ChkSq 2334    := by decide +kernel
private theorem c2334_s3    : S3ChkSq 2334    := by decide +kernel
private theorem c2334_iso   : LeafIso 2334    := by decide +kernel
private theorem c2334_nof2  : NoF2ChkSq 2334  := by decide +kernel
private theorem c2334_nof3  : NoF3ChkSq 2334  := by decide +kernel
private theorem c2334_nof4z : NoF4zChkSq 2334 := by decide +kernel
theorem C'_2334 : C' 2334 :=
  ⟨c2334_sqf, c2334_range, c2334_ell, leafNSq_of_sq c2334_nsq, leafHAr_of_sq c2334_har,
   c2334_r, c2334_e', c2334_f1, leafS2_of_sq c2334_s2, leafS3_of_sq c2334_s3,
   c2334_iso, leafR8_of_sq c2334_nof2 c2334_nof3 c2334_nof4z⟩
theorem not_tile'_2334 (D : CongruentDissection 2334) : False :=
  not_tile_of_conditions' 2334 C'_2334 D

private theorem c2335_sqf   : LeafSqf 2335   := by decide +kernel
private theorem c2335_range : LeafRange 2335  := by decide +kernel
private theorem c2335_ell   : LeafEll 2335    := by decide +kernel
private theorem c2335_nsq   : NSqChkSq 2335   := by decide +kernel
private theorem c2335_har   : HArithChkSq 2335 := by decide +kernel
private theorem c2335_r     : LeafR 2335      := by decide +kernel
private theorem c2335_e'    : LeafE' 2335     := by decide +kernel
private theorem c2335_f1    : LeafF1 2335     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2335_s2    : S2ChkSq 2335    := by decide +kernel
private theorem c2335_s3    : S3ChkSq 2335    := by decide +kernel
private theorem c2335_iso   : LeafIso 2335    := by decide +kernel
private theorem c2335_nof2  : NoF2ChkSq 2335  := by decide +kernel
private theorem c2335_nof3  : NoF3ChkSq 2335  := by decide +kernel
private theorem c2335_nof4z : NoF4zChkSq 2335 := by decide +kernel
theorem C'_2335 : C' 2335 :=
  ⟨c2335_sqf, c2335_range, c2335_ell, leafNSq_of_sq c2335_nsq, leafHAr_of_sq c2335_har,
   c2335_r, c2335_e', c2335_f1, leafS2_of_sq c2335_s2, leafS3_of_sq c2335_s3,
   c2335_iso, leafR8_of_sq c2335_nof2 c2335_nof3 c2335_nof4z⟩
theorem not_tile'_2335 (D : CongruentDissection 2335) : False :=
  not_tile_of_conditions' 2335 C'_2335 D

private theorem c2337_sqf   : LeafSqf 2337   := by decide +kernel
private theorem c2337_range : LeafRange 2337  := by decide +kernel
private theorem c2337_ell   : LeafEll 2337    := by decide +kernel
private theorem c2337_nsq   : NSqChkSq 2337   := by decide +kernel
private theorem c2337_har   : HArithChkSq 2337 := by decide +kernel
private theorem c2337_r     : LeafR 2337      := by decide +kernel
private theorem c2337_e'    : LeafE' 2337     := by decide +kernel
private theorem c2337_f1    : LeafF1 2337     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2337_s2    : S2ChkSq 2337    := by decide +kernel
private theorem c2337_s3    : S3ChkSq 2337    := by decide +kernel
private theorem c2337_iso   : LeafIso 2337    := by decide +kernel
private theorem c2337_nof2  : NoF2ChkSq 2337  := by decide +kernel
private theorem c2337_nof3  : NoF3ChkSq 2337  := by decide +kernel
private theorem c2337_nof4z : NoF4zChkSq 2337 := by decide +kernel
theorem C'_2337 : C' 2337 :=
  ⟨c2337_sqf, c2337_range, c2337_ell, leafNSq_of_sq c2337_nsq, leafHAr_of_sq c2337_har,
   c2337_r, c2337_e', c2337_f1, leafS2_of_sq c2337_s2, leafS3_of_sq c2337_s3,
   c2337_iso, leafR8_of_sq c2337_nof2 c2337_nof3 c2337_nof4z⟩
theorem not_tile'_2337 (D : CongruentDissection 2337) : False :=
  not_tile_of_conditions' 2337 C'_2337 D

private theorem c2338_sqf   : LeafSqf 2338   := by decide +kernel
private theorem c2338_range : LeafRange 2338  := by decide +kernel
private theorem c2338_ell   : LeafEll 2338    := by decide +kernel
private theorem c2338_nsq   : NSqChkSq 2338   := by decide +kernel
private theorem c2338_har   : HArithChkSq 2338 := by decide +kernel
private theorem c2338_r     : LeafR 2338      := by decide +kernel
private theorem c2338_e'    : LeafE' 2338     := by decide +kernel
private theorem c2338_f1    : LeafF1 2338     := Or.inl (by decide)
private theorem c2338_s2    : S2ChkSq 2338    := by decide +kernel
private theorem c2338_s3    : S3ChkSq 2338    := by decide +kernel
private theorem c2338_iso   : LeafIso 2338    := by decide +kernel
private theorem c2338_nof2  : NoF2ChkSq 2338  := by decide +kernel
private theorem c2338_nof3  : NoF3ChkSq 2338  := by decide +kernel
private theorem c2338_nof4z : NoF4zChkSq 2338 := by decide +kernel
theorem C'_2338 : C' 2338 :=
  ⟨c2338_sqf, c2338_range, c2338_ell, leafNSq_of_sq c2338_nsq, leafHAr_of_sq c2338_har,
   c2338_r, c2338_e', c2338_f1, leafS2_of_sq c2338_s2, leafS3_of_sq c2338_s3,
   c2338_iso, leafR8_of_sq c2338_nof2 c2338_nof3 c2338_nof4z⟩
theorem not_tile'_2338 (D : CongruentDissection 2338) : False :=
  not_tile_of_conditions' 2338 C'_2338 D

private theorem c2339_sqf   : LeafSqf 2339   := by decide +kernel
private theorem c2339_range : LeafRange 2339  := by decide +kernel
private theorem c2339_ell   : LeafEll 2339    := by decide +kernel
private theorem c2339_nsq   : NSqChkSq 2339   := by decide +kernel
private theorem c2339_har   : HArithChkSq 2339 := by decide +kernel
private theorem c2339_r     : LeafR 2339      := by decide +kernel
private theorem c2339_e'    : LeafE' 2339     := by decide +kernel
private theorem c2339_f1    : LeafF1 2339     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2339_s2    : S2ChkSq 2339    := by decide +kernel
private theorem c2339_s3    : S3ChkSq 2339    := by decide +kernel
private theorem c2339_iso   : LeafIso 2339    := by decide +kernel
private theorem c2339_nof2  : NoF2ChkSq 2339  := by decide +kernel
private theorem c2339_nof3  : NoF3ChkSq 2339  := by decide +kernel
private theorem c2339_nof4z : NoF4zChkSq 2339 := by decide +kernel
theorem C'_2339 : C' 2339 :=
  ⟨c2339_sqf, c2339_range, c2339_ell, leafNSq_of_sq c2339_nsq, leafHAr_of_sq c2339_har,
   c2339_r, c2339_e', c2339_f1, leafS2_of_sq c2339_s2, leafS3_of_sq c2339_s3,
   c2339_iso, leafR8_of_sq c2339_nof2 c2339_nof3 c2339_nof4z⟩
theorem not_tile'_2339 (D : CongruentDissection 2339) : False :=
  not_tile_of_conditions' 2339 C'_2339 D

end Erdos634.Draft.AllN2

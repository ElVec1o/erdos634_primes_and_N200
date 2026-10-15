/- AllN2Check231: N = 4310, 4313, 4314, 4315, 4317
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4310_sqf   : LeafSqf 4310   := by decide +kernel
private theorem c4310_range : LeafRange 4310  := by decide +kernel
private theorem c4310_ell   : LeafEll 4310    := by decide +kernel
private theorem c4310_nsq   : NSqChkSq 4310   := by decide +kernel
private theorem c4310_har   : HArithChkSq 4310 := by decide +kernel
private theorem c4310_r     : LeafR 4310      := by decide +kernel
private theorem c4310_e'    : LeafE' 4310     := by decide +kernel
private theorem c4310_f1    : LeafF1 4310     := Or.inl (by decide)
private theorem c4310_s2    : S2ChkSq 4310    := by decide +kernel
private theorem c4310_s3    : S3ChkSq 4310    := by decide +kernel
private theorem c4310_iso   : LeafIso 4310    := by decide +kernel
private theorem c4310_nof2  : NoF2ChkSq 4310  := by decide +kernel
private theorem c4310_nof3  : NoF3ChkSq 4310  := by decide +kernel
private theorem c4310_nof4z : NoF4zChkSq 4310 := by decide +kernel
theorem C'_4310 : C' 4310 :=
  ⟨c4310_sqf, c4310_range, c4310_ell, leafNSq_of_sq c4310_nsq, leafHAr_of_sq c4310_har,
   c4310_r, c4310_e', c4310_f1, leafS2_of_sq c4310_s2, leafS3_of_sq c4310_s3,
   c4310_iso, leafR8_of_sq c4310_nof2 c4310_nof3 c4310_nof4z⟩
theorem not_tile'_4310 (D : CongruentDissection 4310) : False :=
  not_tile_of_conditions' 4310 C'_4310 D

private theorem c4313_sqf   : LeafSqf 4313   := by decide +kernel
private theorem c4313_range : LeafRange 4313  := by decide +kernel
private theorem c4313_ell   : LeafEll 4313    := by decide +kernel
private theorem c4313_nsq   : NSqChkSq 4313   := by decide +kernel
private theorem c4313_har   : HArithChkSq 4313 := by decide +kernel
private theorem c4313_r     : LeafR 4313      := by decide +kernel
private theorem c4313_e'    : LeafE' 4313     := by decide +kernel
private theorem c4313_f1    : LeafF1 4313     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4313_s2    : S2ChkSq 4313    := by decide +kernel
private theorem c4313_s3    : S3ChkSq 4313    := by decide +kernel
private theorem c4313_iso   : LeafIso 4313    := by decide +kernel
private theorem c4313_nof2  : NoF2ChkSq 4313  := by decide +kernel
private theorem c4313_nof3  : NoF3ChkSq 4313  := by decide +kernel
private theorem c4313_nof4z : NoF4zChkSq 4313 := by decide +kernel
theorem C'_4313 : C' 4313 :=
  ⟨c4313_sqf, c4313_range, c4313_ell, leafNSq_of_sq c4313_nsq, leafHAr_of_sq c4313_har,
   c4313_r, c4313_e', c4313_f1, leafS2_of_sq c4313_s2, leafS3_of_sq c4313_s3,
   c4313_iso, leafR8_of_sq c4313_nof2 c4313_nof3 c4313_nof4z⟩
theorem not_tile'_4313 (D : CongruentDissection 4313) : False :=
  not_tile_of_conditions' 4313 C'_4313 D

private theorem c4314_sqf   : LeafSqf 4314   := by decide +kernel
private theorem c4314_range : LeafRange 4314  := by decide +kernel
private theorem c4314_ell   : LeafEll 4314    := by decide +kernel
private theorem c4314_nsq   : NSqChkSq 4314   := by decide +kernel
private theorem c4314_har   : HArithChkSq 4314 := by decide +kernel
private theorem c4314_r     : LeafR 4314      := by decide +kernel
private theorem c4314_e'    : LeafE' 4314     := by decide +kernel
private theorem c4314_f1    : LeafF1 4314     := Or.inl (by decide)
private theorem c4314_s2    : S2ChkSq 4314    := by decide +kernel
private theorem c4314_s3    : S3ChkSq 4314    := by decide +kernel
private theorem c4314_iso   : LeafIso 4314    := by decide +kernel
private theorem c4314_nof2  : NoF2ChkSq 4314  := by decide +kernel
private theorem c4314_nof3  : NoF3ChkSq 4314  := by decide +kernel
private theorem c4314_nof4z : NoF4zChkSq 4314 := by decide +kernel
theorem C'_4314 : C' 4314 :=
  ⟨c4314_sqf, c4314_range, c4314_ell, leafNSq_of_sq c4314_nsq, leafHAr_of_sq c4314_har,
   c4314_r, c4314_e', c4314_f1, leafS2_of_sq c4314_s2, leafS3_of_sq c4314_s3,
   c4314_iso, leafR8_of_sq c4314_nof2 c4314_nof3 c4314_nof4z⟩
theorem not_tile'_4314 (D : CongruentDissection 4314) : False :=
  not_tile_of_conditions' 4314 C'_4314 D

private theorem c4315_sqf   : LeafSqf 4315   := by decide +kernel
private theorem c4315_range : LeafRange 4315  := by decide +kernel
private theorem c4315_ell   : LeafEll 4315    := by decide +kernel
private theorem c4315_nsq   : NSqChkSq 4315   := by decide +kernel
private theorem c4315_har   : HArithChkSq 4315 := by decide +kernel
private theorem c4315_r     : LeafR 4315      := by decide +kernel
private theorem c4315_e'    : LeafE' 4315     := by decide +kernel
private theorem c4315_f1    : LeafF1 4315     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4315_s2    : S2ChkSq 4315    := by decide +kernel
private theorem c4315_s3    : S3ChkSq 4315    := by decide +kernel
private theorem c4315_iso   : LeafIso 4315    := by decide +kernel
private theorem c4315_nof2  : NoF2ChkSq 4315  := by decide +kernel
private theorem c4315_nof3  : NoF3ChkSq 4315  := by decide +kernel
private theorem c4315_nof4z : NoF4zChkSq 4315 := by decide +kernel
theorem C'_4315 : C' 4315 :=
  ⟨c4315_sqf, c4315_range, c4315_ell, leafNSq_of_sq c4315_nsq, leafHAr_of_sq c4315_har,
   c4315_r, c4315_e', c4315_f1, leafS2_of_sq c4315_s2, leafS3_of_sq c4315_s3,
   c4315_iso, leafR8_of_sq c4315_nof2 c4315_nof3 c4315_nof4z⟩
theorem not_tile'_4315 (D : CongruentDissection 4315) : False :=
  not_tile_of_conditions' 4315 C'_4315 D

private theorem c4317_sqf   : LeafSqf 4317   := by decide +kernel
private theorem c4317_range : LeafRange 4317  := by decide +kernel
private theorem c4317_ell   : LeafEll 4317    := by decide +kernel
private theorem c4317_nsq   : NSqChkSq 4317   := by decide +kernel
private theorem c4317_har   : HArithChkSq 4317 := by decide +kernel
private theorem c4317_r     : LeafR 4317      := by decide +kernel
private theorem c4317_e'    : LeafE' 4317     := by decide +kernel
private theorem c4317_f1    : LeafF1 4317     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4317_s2    : S2ChkSq 4317    := by decide +kernel
private theorem c4317_s3    : S3ChkSq 4317    := by decide +kernel
private theorem c4317_iso   : LeafIso 4317    := by decide +kernel
private theorem c4317_nof2  : NoF2ChkSq 4317  := by decide +kernel
private theorem c4317_nof3  : NoF3ChkSq 4317  := by decide +kernel
private theorem c4317_nof4z : NoF4zChkSq 4317 := by decide +kernel
theorem C'_4317 : C' 4317 :=
  ⟨c4317_sqf, c4317_range, c4317_ell, leafNSq_of_sq c4317_nsq, leafHAr_of_sq c4317_har,
   c4317_r, c4317_e', c4317_f1, leafS2_of_sq c4317_s2, leafS3_of_sq c4317_s3,
   c4317_iso, leafR8_of_sq c4317_nof2 c4317_nof3 c4317_nof4z⟩
theorem not_tile'_4317 (D : CongruentDissection 4317) : False :=
  not_tile_of_conditions' 4317 C'_4317 D

end Erdos634.Draft.AllN2

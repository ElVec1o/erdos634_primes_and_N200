/- AllN2Check227: N = 4267, 4269, 4270, 4271, 4277
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4267_sqf   : LeafSqf 4267   := by decide +kernel
private theorem c4267_range : LeafRange 4267  := by decide +kernel
private theorem c4267_ell   : LeafEll 4267    := by decide +kernel
private theorem c4267_nsq   : NSqChkSq 4267   := by decide +kernel
private theorem c4267_har   : HArithChkSq 4267 := by decide +kernel
private theorem c4267_r     : LeafR 4267      := by decide +kernel
private theorem c4267_e'    : LeafE' 4267     := by decide +kernel
private theorem c4267_f1    : LeafF1 4267     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4267_s2    : S2ChkSq 4267    := by decide +kernel
private theorem c4267_s3    : S3ChkSq 4267    := by decide +kernel
private theorem c4267_iso   : LeafIso 4267    := by decide +kernel
private theorem c4267_nof2  : NoF2ChkSq 4267  := by decide +kernel
private theorem c4267_nof3  : NoF3ChkSq 4267  := by decide +kernel
private theorem c4267_nof4z : NoF4zChkSq 4267 := by decide +kernel
theorem C'_4267 : C' 4267 :=
  ⟨c4267_sqf, c4267_range, c4267_ell, leafNSq_of_sq c4267_nsq, leafHAr_of_sq c4267_har,
   c4267_r, c4267_e', c4267_f1, leafS2_of_sq c4267_s2, leafS3_of_sq c4267_s3,
   c4267_iso, leafR8_of_sq c4267_nof2 c4267_nof3 c4267_nof4z⟩
theorem not_tile'_4267 (D : CongruentDissection 4267) : False :=
  not_tile_of_conditions' 4267 C'_4267 D

private theorem c4269_sqf   : LeafSqf 4269   := by decide +kernel
private theorem c4269_range : LeafRange 4269  := by decide +kernel
private theorem c4269_ell   : LeafEll 4269    := by decide +kernel
private theorem c4269_nsq   : NSqChkSq 4269   := by decide +kernel
private theorem c4269_har   : HArithChkSq 4269 := by decide +kernel
private theorem c4269_r     : LeafR 4269      := by decide +kernel
private theorem c4269_e'    : LeafE' 4269     := by decide +kernel
private theorem c4269_f1    : LeafF1 4269     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4269_s2    : S2ChkSq 4269    := by decide +kernel
private theorem c4269_s3    : S3ChkSq 4269    := by decide +kernel
private theorem c4269_iso   : LeafIso 4269    := by decide +kernel
private theorem c4269_nof2  : NoF2ChkSq 4269  := by decide +kernel
private theorem c4269_nof3  : NoF3ChkSq 4269  := by decide +kernel
private theorem c4269_nof4z : NoF4zChkSq 4269 := by decide +kernel
theorem C'_4269 : C' 4269 :=
  ⟨c4269_sqf, c4269_range, c4269_ell, leafNSq_of_sq c4269_nsq, leafHAr_of_sq c4269_har,
   c4269_r, c4269_e', c4269_f1, leafS2_of_sq c4269_s2, leafS3_of_sq c4269_s3,
   c4269_iso, leafR8_of_sq c4269_nof2 c4269_nof3 c4269_nof4z⟩
theorem not_tile'_4269 (D : CongruentDissection 4269) : False :=
  not_tile_of_conditions' 4269 C'_4269 D

private theorem c4270_sqf   : LeafSqf 4270   := by decide +kernel
private theorem c4270_range : LeafRange 4270  := by decide +kernel
private theorem c4270_ell   : LeafEll 4270    := by decide +kernel
private theorem c4270_nsq   : NSqChkSq 4270   := by decide +kernel
private theorem c4270_har   : HArithChkSq 4270 := by decide +kernel
private theorem c4270_r     : LeafR 4270      := by decide +kernel
private theorem c4270_e'    : LeafE' 4270     := by decide +kernel
private theorem c4270_f1    : LeafF1 4270     := Or.inl (by decide)
private theorem c4270_s2    : S2ChkSq 4270    := by decide +kernel
private theorem c4270_s3    : S3ChkSq 4270    := by decide +kernel
private theorem c4270_iso   : LeafIso 4270    := by decide +kernel
private theorem c4270_nof2  : NoF2ChkSq 4270  := by decide +kernel
private theorem c4270_nof3  : NoF3ChkSq 4270  := by decide +kernel
private theorem c4270_nof4z : NoF4zChkSq 4270 := by decide +kernel
theorem C'_4270 : C' 4270 :=
  ⟨c4270_sqf, c4270_range, c4270_ell, leafNSq_of_sq c4270_nsq, leafHAr_of_sq c4270_har,
   c4270_r, c4270_e', c4270_f1, leafS2_of_sq c4270_s2, leafS3_of_sq c4270_s3,
   c4270_iso, leafR8_of_sq c4270_nof2 c4270_nof3 c4270_nof4z⟩
theorem not_tile'_4270 (D : CongruentDissection 4270) : False :=
  not_tile_of_conditions' 4270 C'_4270 D

private theorem c4271_sqf   : LeafSqf 4271   := by decide +kernel
private theorem c4271_range : LeafRange 4271  := by decide +kernel
private theorem c4271_ell   : LeafEll 4271    := by decide +kernel
private theorem c4271_nsq   : NSqChkSq 4271   := by decide +kernel
private theorem c4271_har   : HArithChkSq 4271 := by decide +kernel
private theorem c4271_r     : LeafR 4271      := by decide +kernel
private theorem c4271_e'    : LeafE' 4271     := by decide +kernel
private theorem c4271_f1    : LeafF1 4271     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4271_s2    : S2ChkSq 4271    := by decide +kernel
private theorem c4271_s3    : S3ChkSq 4271    := by decide +kernel
private theorem c4271_iso   : LeafIso 4271    := by decide +kernel
private theorem c4271_nof2  : NoF2ChkSq 4271  := by decide +kernel
private theorem c4271_nof3  : NoF3ChkSq 4271  := by decide +kernel
private theorem c4271_nof4z : NoF4zChkSq 4271 := by decide +kernel
theorem C'_4271 : C' 4271 :=
  ⟨c4271_sqf, c4271_range, c4271_ell, leafNSq_of_sq c4271_nsq, leafHAr_of_sq c4271_har,
   c4271_r, c4271_e', c4271_f1, leafS2_of_sq c4271_s2, leafS3_of_sq c4271_s3,
   c4271_iso, leafR8_of_sq c4271_nof2 c4271_nof3 c4271_nof4z⟩
theorem not_tile'_4271 (D : CongruentDissection 4271) : False :=
  not_tile_of_conditions' 4271 C'_4271 D

private theorem c4277_sqf   : LeafSqf 4277   := by decide +kernel
private theorem c4277_range : LeafRange 4277  := by decide +kernel
private theorem c4277_ell   : LeafEll 4277    := by decide +kernel
private theorem c4277_nsq   : NSqChkSq 4277   := by decide +kernel
private theorem c4277_har   : HArithChkSq 4277 := by decide +kernel
private theorem c4277_r     : LeafR 4277      := by decide +kernel
private theorem c4277_e'    : LeafE' 4277     := by decide +kernel
private theorem c4277_f1    : LeafF1 4277     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4277_s2    : S2ChkSq 4277    := by decide +kernel
private theorem c4277_s3    : S3ChkSq 4277    := by decide +kernel
private theorem c4277_iso   : LeafIso 4277    := by decide +kernel
private theorem c4277_nof2  : NoF2ChkSq 4277  := by decide +kernel
private theorem c4277_nof3  : NoF3ChkSq 4277  := by decide +kernel
private theorem c4277_nof4z : NoF4zChkSq 4277 := by decide +kernel
theorem C'_4277 : C' 4277 :=
  ⟨c4277_sqf, c4277_range, c4277_ell, leafNSq_of_sq c4277_nsq, leafHAr_of_sq c4277_har,
   c4277_r, c4277_e', c4277_f1, leafS2_of_sq c4277_s2, leafS3_of_sq c4277_s3,
   c4277_iso, leafR8_of_sq c4277_nof2 c4277_nof3 c4277_nof4z⟩
theorem not_tile'_4277 (D : CongruentDissection 4277) : False :=
  not_tile_of_conditions' 4277 C'_4277 D

end Erdos634.Draft.AllN2

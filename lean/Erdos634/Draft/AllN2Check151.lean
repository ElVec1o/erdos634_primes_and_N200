/- AllN2Check151: N = 3263, 3269, 3270, 3271, 3273
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3263_sqf   : LeafSqf 3263   := by decide +kernel
private theorem c3263_range : LeafRange 3263  := by decide +kernel
private theorem c3263_ell   : LeafEll 3263    := by decide +kernel
private theorem c3263_nsq   : NSqChkSq 3263   := by decide +kernel
private theorem c3263_har   : HArithChkSq 3263 := by decide +kernel
private theorem c3263_r     : LeafR 3263      := by decide +kernel
private theorem c3263_e'    : LeafE' 3263     := by decide +kernel
private theorem c3263_f1    : LeafF1 3263     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3263_s2    : S2ChkSq 3263    := by decide +kernel
private theorem c3263_s3    : S3ChkSq 3263    := by decide +kernel
private theorem c3263_iso   : LeafIso 3263    := by decide +kernel
private theorem c3263_nof2  : NoF2ChkSq 3263  := by decide +kernel
private theorem c3263_nof3  : NoF3ChkSq 3263  := by decide +kernel
private theorem c3263_nof4z : NoF4zChkSq 3263 := by decide +kernel
theorem C'_3263 : C' 3263 :=
  ⟨c3263_sqf, c3263_range, c3263_ell, leafNSq_of_sq c3263_nsq, leafHAr_of_sq c3263_har,
   c3263_r, c3263_e', c3263_f1, leafS2_of_sq c3263_s2, leafS3_of_sq c3263_s3,
   c3263_iso, leafR8_of_sq c3263_nof2 c3263_nof3 c3263_nof4z⟩
theorem not_tile'_3263 (D : CongruentDissection 3263) : False :=
  not_tile_of_conditions' 3263 C'_3263 D

private theorem c3269_sqf   : LeafSqf 3269   := by decide +kernel
private theorem c3269_range : LeafRange 3269  := by decide +kernel
private theorem c3269_ell   : LeafEll 3269    := by decide +kernel
private theorem c3269_nsq   : NSqChkSq 3269   := by decide +kernel
private theorem c3269_har   : HArithChkSq 3269 := by decide +kernel
private theorem c3269_r     : LeafR 3269      := by decide +kernel
private theorem c3269_e'    : LeafE' 3269     := by decide +kernel
private theorem c3269_f1    : LeafF1 3269     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3269_s2    : S2ChkSq 3269    := by decide +kernel
private theorem c3269_s3    : S3ChkSq 3269    := by decide +kernel
private theorem c3269_iso   : LeafIso 3269    := by decide +kernel
private theorem c3269_nof2  : NoF2ChkSq 3269  := by decide +kernel
private theorem c3269_nof3  : NoF3ChkSq 3269  := by decide +kernel
private theorem c3269_nof4z : NoF4zChkSq 3269 := by decide +kernel
theorem C'_3269 : C' 3269 :=
  ⟨c3269_sqf, c3269_range, c3269_ell, leafNSq_of_sq c3269_nsq, leafHAr_of_sq c3269_har,
   c3269_r, c3269_e', c3269_f1, leafS2_of_sq c3269_s2, leafS3_of_sq c3269_s3,
   c3269_iso, leafR8_of_sq c3269_nof2 c3269_nof3 c3269_nof4z⟩
theorem not_tile'_3269 (D : CongruentDissection 3269) : False :=
  not_tile_of_conditions' 3269 C'_3269 D

private theorem c3270_sqf   : LeafSqf 3270   := by decide +kernel
private theorem c3270_range : LeafRange 3270  := by decide +kernel
private theorem c3270_ell   : LeafEll 3270    := by decide +kernel
private theorem c3270_nsq   : NSqChkSq 3270   := by decide +kernel
private theorem c3270_har   : HArithChkSq 3270 := by decide +kernel
private theorem c3270_r     : LeafR 3270      := by decide +kernel
private theorem c3270_e'    : LeafE' 3270     := by decide +kernel
private theorem c3270_f1    : LeafF1 3270     := Or.inl (by decide)
private theorem c3270_s2    : S2ChkSq 3270    := by decide +kernel
private theorem c3270_s3    : S3ChkSq 3270    := by decide +kernel
private theorem c3270_iso   : LeafIso 3270    := by decide +kernel
private theorem c3270_nof2  : NoF2ChkSq 3270  := by decide +kernel
private theorem c3270_nof3  : NoF3ChkSq 3270  := by decide +kernel
private theorem c3270_nof4z : NoF4zChkSq 3270 := by decide +kernel
theorem C'_3270 : C' 3270 :=
  ⟨c3270_sqf, c3270_range, c3270_ell, leafNSq_of_sq c3270_nsq, leafHAr_of_sq c3270_har,
   c3270_r, c3270_e', c3270_f1, leafS2_of_sq c3270_s2, leafS3_of_sq c3270_s3,
   c3270_iso, leafR8_of_sq c3270_nof2 c3270_nof3 c3270_nof4z⟩
theorem not_tile'_3270 (D : CongruentDissection 3270) : False :=
  not_tile_of_conditions' 3270 C'_3270 D

private theorem c3271_sqf   : LeafSqf 3271   := by decide +kernel
private theorem c3271_range : LeafRange 3271  := by decide +kernel
private theorem c3271_ell   : LeafEll 3271    := by decide +kernel
private theorem c3271_nsq   : NSqChkSq 3271   := by decide +kernel
private theorem c3271_har   : HArithChkSq 3271 := by decide +kernel
private theorem c3271_r     : LeafR 3271      := by decide +kernel
private theorem c3271_e'    : LeafE' 3271     := by decide +kernel
private theorem c3271_f1    : LeafF1 3271     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3271_s2    : S2ChkSq 3271    := by decide +kernel
private theorem c3271_s3    : S3ChkSq 3271    := by decide +kernel
private theorem c3271_iso   : LeafIso 3271    := by decide +kernel
private theorem c3271_nof2  : NoF2ChkSq 3271  := by decide +kernel
private theorem c3271_nof3  : NoF3ChkSq 3271  := by decide +kernel
private theorem c3271_nof4z : NoF4zChkSq 3271 := by decide +kernel
theorem C'_3271 : C' 3271 :=
  ⟨c3271_sqf, c3271_range, c3271_ell, leafNSq_of_sq c3271_nsq, leafHAr_of_sq c3271_har,
   c3271_r, c3271_e', c3271_f1, leafS2_of_sq c3271_s2, leafS3_of_sq c3271_s3,
   c3271_iso, leafR8_of_sq c3271_nof2 c3271_nof3 c3271_nof4z⟩
theorem not_tile'_3271 (D : CongruentDissection 3271) : False :=
  not_tile_of_conditions' 3271 C'_3271 D

private theorem c3273_sqf   : LeafSqf 3273   := by decide +kernel
private theorem c3273_range : LeafRange 3273  := by decide +kernel
private theorem c3273_ell   : LeafEll 3273    := by decide +kernel
private theorem c3273_nsq   : NSqChkSq 3273   := by decide +kernel
private theorem c3273_har   : HArithChkSq 3273 := by decide +kernel
private theorem c3273_r     : LeafR 3273      := by decide +kernel
private theorem c3273_e'    : LeafE' 3273     := by decide +kernel
private theorem c3273_f1    : LeafF1 3273     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3273_s2    : S2ChkSq 3273    := by decide +kernel
private theorem c3273_s3    : S3ChkSq 3273    := by decide +kernel
private theorem c3273_iso   : LeafIso 3273    := by decide +kernel
private theorem c3273_nof2  : NoF2ChkSq 3273  := by decide +kernel
private theorem c3273_nof3  : NoF3ChkSq 3273  := by decide +kernel
private theorem c3273_nof4z : NoF4zChkSq 3273 := by decide +kernel
theorem C'_3273 : C' 3273 :=
  ⟨c3273_sqf, c3273_range, c3273_ell, leafNSq_of_sq c3273_nsq, leafHAr_of_sq c3273_har,
   c3273_r, c3273_e', c3273_f1, leafS2_of_sq c3273_s2, leafS3_of_sq c3273_s3,
   c3273_iso, leafR8_of_sq c3273_nof2 c3273_nof3 c3273_nof4z⟩
theorem not_tile'_3273 (D : CongruentDissection 3273) : False :=
  not_tile_of_conditions' 3273 C'_3273 D

end Erdos634.Draft.AllN2

/- AllN2Check72: N = 2263, 2266, 2267, 2270, 2271
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2263_sqf   : LeafSqf 2263   := by decide +kernel
private theorem c2263_range : LeafRange 2263  := by decide +kernel
private theorem c2263_ell   : LeafEll 2263    := by decide +kernel
private theorem c2263_nsq   : NSqChkSq 2263   := by decide +kernel
private theorem c2263_har   : HArithChkSq 2263 := by decide +kernel
private theorem c2263_r     : LeafR 2263      := by decide +kernel
private theorem c2263_e'    : LeafE' 2263     := by decide +kernel
private theorem c2263_f1    : LeafF1 2263     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2263_s2    : S2ChkSq 2263    := by decide +kernel
private theorem c2263_s3    : S3ChkSq 2263    := by decide +kernel
private theorem c2263_iso   : LeafIso 2263    := by decide +kernel
private theorem c2263_nof2  : NoF2ChkSq 2263  := by decide +kernel
private theorem c2263_nof3  : NoF3ChkSq 2263  := by decide +kernel
private theorem c2263_nof4z : NoF4zChkSq 2263 := by decide +kernel
theorem C'_2263 : C' 2263 :=
  ⟨c2263_sqf, c2263_range, c2263_ell, leafNSq_of_sq c2263_nsq, leafHAr_of_sq c2263_har,
   c2263_r, c2263_e', c2263_f1, leafS2_of_sq c2263_s2, leafS3_of_sq c2263_s3,
   c2263_iso, leafR8_of_sq c2263_nof2 c2263_nof3 c2263_nof4z⟩
theorem not_tile'_2263 (D : CongruentDissection 2263) : False :=
  not_tile_of_conditions' 2263 C'_2263 D

private theorem c2266_sqf   : LeafSqf 2266   := by decide +kernel
private theorem c2266_range : LeafRange 2266  := by decide +kernel
private theorem c2266_ell   : LeafEll 2266    := by decide +kernel
private theorem c2266_nsq   : NSqChkSq 2266   := by decide +kernel
private theorem c2266_har   : HArithChkSq 2266 := by decide +kernel
private theorem c2266_r     : LeafR 2266      := by decide +kernel
private theorem c2266_e'    : LeafE' 2266     := by decide +kernel
private theorem c2266_f1    : LeafF1 2266     := Or.inl (by decide)
private theorem c2266_s2    : S2ChkSq 2266    := by decide +kernel
private theorem c2266_s3    : S3ChkSq 2266    := by decide +kernel
private theorem c2266_iso   : LeafIso 2266    := by decide +kernel
private theorem c2266_nof2  : NoF2ChkSq 2266  := by decide +kernel
private theorem c2266_nof3  : NoF3ChkSq 2266  := by decide +kernel
private theorem c2266_nof4z : NoF4zChkSq 2266 := by decide +kernel
theorem C'_2266 : C' 2266 :=
  ⟨c2266_sqf, c2266_range, c2266_ell, leafNSq_of_sq c2266_nsq, leafHAr_of_sq c2266_har,
   c2266_r, c2266_e', c2266_f1, leafS2_of_sq c2266_s2, leafS3_of_sq c2266_s3,
   c2266_iso, leafR8_of_sq c2266_nof2 c2266_nof3 c2266_nof4z⟩
theorem not_tile'_2266 (D : CongruentDissection 2266) : False :=
  not_tile_of_conditions' 2266 C'_2266 D

private theorem c2267_sqf   : LeafSqf 2267   := by decide +kernel
private theorem c2267_range : LeafRange 2267  := by decide +kernel
private theorem c2267_ell   : LeafEll 2267    := by decide +kernel
private theorem c2267_nsq   : NSqChkSq 2267   := by decide +kernel
private theorem c2267_har   : HArithChkSq 2267 := by decide +kernel
private theorem c2267_r     : LeafR 2267      := by decide +kernel
private theorem c2267_e'    : LeafE' 2267     := by decide +kernel
private theorem c2267_f1    : LeafF1 2267     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2267_s2    : S2ChkSq 2267    := by decide +kernel
private theorem c2267_s3    : S3ChkSq 2267    := by decide +kernel
private theorem c2267_iso   : LeafIso 2267    := by decide +kernel
private theorem c2267_nof2  : NoF2ChkSq 2267  := by decide +kernel
private theorem c2267_nof3  : NoF3ChkSq 2267  := by decide +kernel
private theorem c2267_nof4z : NoF4zChkSq 2267 := by decide +kernel
theorem C'_2267 : C' 2267 :=
  ⟨c2267_sqf, c2267_range, c2267_ell, leafNSq_of_sq c2267_nsq, leafHAr_of_sq c2267_har,
   c2267_r, c2267_e', c2267_f1, leafS2_of_sq c2267_s2, leafS3_of_sq c2267_s3,
   c2267_iso, leafR8_of_sq c2267_nof2 c2267_nof3 c2267_nof4z⟩
theorem not_tile'_2267 (D : CongruentDissection 2267) : False :=
  not_tile_of_conditions' 2267 C'_2267 D

private theorem c2270_sqf   : LeafSqf 2270   := by decide +kernel
private theorem c2270_range : LeafRange 2270  := by decide +kernel
private theorem c2270_ell   : LeafEll 2270    := by decide +kernel
private theorem c2270_nsq   : NSqChkSq 2270   := by decide +kernel
private theorem c2270_har   : HArithChkSq 2270 := by decide +kernel
private theorem c2270_r     : LeafR 2270      := by decide +kernel
private theorem c2270_e'    : LeafE' 2270     := by decide +kernel
private theorem c2270_f1    : LeafF1 2270     := Or.inl (by decide)
private theorem c2270_s2    : S2ChkSq 2270    := by decide +kernel
private theorem c2270_s3    : S3ChkSq 2270    := by decide +kernel
private theorem c2270_iso   : LeafIso 2270    := by decide +kernel
private theorem c2270_nof2  : NoF2ChkSq 2270  := by decide +kernel
private theorem c2270_nof3  : NoF3ChkSq 2270  := by decide +kernel
private theorem c2270_nof4z : NoF4zChkSq 2270 := by decide +kernel
theorem C'_2270 : C' 2270 :=
  ⟨c2270_sqf, c2270_range, c2270_ell, leafNSq_of_sq c2270_nsq, leafHAr_of_sq c2270_har,
   c2270_r, c2270_e', c2270_f1, leafS2_of_sq c2270_s2, leafS3_of_sq c2270_s3,
   c2270_iso, leafR8_of_sq c2270_nof2 c2270_nof3 c2270_nof4z⟩
theorem not_tile'_2270 (D : CongruentDissection 2270) : False :=
  not_tile_of_conditions' 2270 C'_2270 D

private theorem c2271_sqf   : LeafSqf 2271   := by decide +kernel
private theorem c2271_range : LeafRange 2271  := by decide +kernel
private theorem c2271_ell   : LeafEll 2271    := by decide +kernel
private theorem c2271_nsq   : NSqChkSq 2271   := by decide +kernel
private theorem c2271_har   : HArithChkSq 2271 := by decide +kernel
private theorem c2271_r     : LeafR 2271      := by decide +kernel
private theorem c2271_e'    : LeafE' 2271     := by decide +kernel
private theorem c2271_f1    : LeafF1 2271     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2271_s2    : S2ChkSq 2271    := by decide +kernel
private theorem c2271_s3    : S3ChkSq 2271    := by decide +kernel
private theorem c2271_iso   : LeafIso 2271    := by decide +kernel
private theorem c2271_nof2  : NoF2ChkSq 2271  := by decide +kernel
private theorem c2271_nof3  : NoF3ChkSq 2271  := by decide +kernel
private theorem c2271_nof4z : NoF4zChkSq 2271 := by decide +kernel
theorem C'_2271 : C' 2271 :=
  ⟨c2271_sqf, c2271_range, c2271_ell, leafNSq_of_sq c2271_nsq, leafHAr_of_sq c2271_har,
   c2271_r, c2271_e', c2271_f1, leafS2_of_sq c2271_s2, leafS3_of_sq c2271_s3,
   c2271_iso, leafR8_of_sq c2271_nof2 c2271_nof3 c2271_nof4z⟩
theorem not_tile'_2271 (D : CongruentDissection 2271) : False :=
  not_tile_of_conditions' 2271 C'_2271 D

end Erdos634.Draft.AllN2

/- AllN2Check144: N = 3163, 3166, 3167, 3173, 3182
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3163_sqf   : LeafSqf 3163   := by decide +kernel
private theorem c3163_range : LeafRange 3163  := by decide +kernel
private theorem c3163_ell   : LeafEll 3163    := by decide +kernel
private theorem c3163_nsq   : NSqChkSq 3163   := by decide +kernel
private theorem c3163_har   : HArithChkSq 3163 := by decide +kernel
private theorem c3163_r     : LeafR 3163      := by decide +kernel
private theorem c3163_e'    : LeafE' 3163     := by decide +kernel
private theorem c3163_f1    : LeafF1 3163     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3163_s2    : S2ChkSq 3163    := by decide +kernel
private theorem c3163_s3    : S3ChkSq 3163    := by decide +kernel
private theorem c3163_iso   : LeafIso 3163    := by decide +kernel
private theorem c3163_nof2  : NoF2ChkSq 3163  := by decide +kernel
private theorem c3163_nof3  : NoF3ChkSq 3163  := by decide +kernel
private theorem c3163_nof4z : NoF4zChkSq 3163 := by decide +kernel
theorem C'_3163 : C' 3163 :=
  ⟨c3163_sqf, c3163_range, c3163_ell, leafNSq_of_sq c3163_nsq, leafHAr_of_sq c3163_har,
   c3163_r, c3163_e', c3163_f1, leafS2_of_sq c3163_s2, leafS3_of_sq c3163_s3,
   c3163_iso, leafR8_of_sq c3163_nof2 c3163_nof3 c3163_nof4z⟩
theorem not_tile'_3163 (D : CongruentDissection 3163) : False :=
  not_tile_of_conditions' 3163 C'_3163 D

private theorem c3166_sqf   : LeafSqf 3166   := by decide +kernel
private theorem c3166_range : LeafRange 3166  := by decide +kernel
private theorem c3166_ell   : LeafEll 3166    := by decide +kernel
private theorem c3166_nsq   : NSqChkSq 3166   := by decide +kernel
private theorem c3166_har   : HArithChkSq 3166 := by decide +kernel
private theorem c3166_r     : LeafR 3166      := by decide +kernel
private theorem c3166_e'    : LeafE' 3166     := by decide +kernel
private theorem c3166_f1    : LeafF1 3166     := Or.inl (by decide)
private theorem c3166_s2    : S2ChkSq 3166    := by decide +kernel
private theorem c3166_s3    : S3ChkSq 3166    := by decide +kernel
private theorem c3166_iso   : LeafIso 3166    := by decide +kernel
private theorem c3166_nof2  : NoF2ChkSq 3166  := by decide +kernel
private theorem c3166_nof3  : NoF3ChkSq 3166  := by decide +kernel
private theorem c3166_nof4z : NoF4zChkSq 3166 := by decide +kernel
theorem C'_3166 : C' 3166 :=
  ⟨c3166_sqf, c3166_range, c3166_ell, leafNSq_of_sq c3166_nsq, leafHAr_of_sq c3166_har,
   c3166_r, c3166_e', c3166_f1, leafS2_of_sq c3166_s2, leafS3_of_sq c3166_s3,
   c3166_iso, leafR8_of_sq c3166_nof2 c3166_nof3 c3166_nof4z⟩
theorem not_tile'_3166 (D : CongruentDissection 3166) : False :=
  not_tile_of_conditions' 3166 C'_3166 D

private theorem c3167_sqf   : LeafSqf 3167   := by decide +kernel
private theorem c3167_range : LeafRange 3167  := by decide +kernel
private theorem c3167_ell   : LeafEll 3167    := by decide +kernel
private theorem c3167_nsq   : NSqChkSq 3167   := by decide +kernel
private theorem c3167_har   : HArithChkSq 3167 := by decide +kernel
private theorem c3167_r     : LeafR 3167      := by decide +kernel
private theorem c3167_e'    : LeafE' 3167     := by decide +kernel
private theorem c3167_f1    : LeafF1 3167     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3167_s2    : S2ChkSq 3167    := by decide +kernel
private theorem c3167_s3    : S3ChkSq 3167    := by decide +kernel
private theorem c3167_iso   : LeafIso 3167    := by decide +kernel
private theorem c3167_nof2  : NoF2ChkSq 3167  := by decide +kernel
private theorem c3167_nof3  : NoF3ChkSq 3167  := by decide +kernel
private theorem c3167_nof4z : NoF4zChkSq 3167 := by decide +kernel
theorem C'_3167 : C' 3167 :=
  ⟨c3167_sqf, c3167_range, c3167_ell, leafNSq_of_sq c3167_nsq, leafHAr_of_sq c3167_har,
   c3167_r, c3167_e', c3167_f1, leafS2_of_sq c3167_s2, leafS3_of_sq c3167_s3,
   c3167_iso, leafR8_of_sq c3167_nof2 c3167_nof3 c3167_nof4z⟩
theorem not_tile'_3167 (D : CongruentDissection 3167) : False :=
  not_tile_of_conditions' 3167 C'_3167 D

private theorem c3173_sqf   : LeafSqf 3173   := by decide +kernel
private theorem c3173_range : LeafRange 3173  := by decide +kernel
private theorem c3173_ell   : LeafEll 3173    := by decide +kernel
private theorem c3173_nsq   : NSqChkSq 3173   := by decide +kernel
private theorem c3173_har   : HArithChkSq 3173 := by decide +kernel
private theorem c3173_r     : LeafR 3173      := by decide +kernel
private theorem c3173_e'    : LeafE' 3173     := by decide +kernel
private theorem c3173_f1    : LeafF1 3173     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3173_s2    : S2ChkSq 3173    := by decide +kernel
private theorem c3173_s3    : S3ChkSq 3173    := by decide +kernel
private theorem c3173_iso   : LeafIso 3173    := by decide +kernel
private theorem c3173_nof2  : NoF2ChkSq 3173  := by decide +kernel
private theorem c3173_nof3  : NoF3ChkSq 3173  := by decide +kernel
private theorem c3173_nof4z : NoF4zChkSq 3173 := by decide +kernel
theorem C'_3173 : C' 3173 :=
  ⟨c3173_sqf, c3173_range, c3173_ell, leafNSq_of_sq c3173_nsq, leafHAr_of_sq c3173_har,
   c3173_r, c3173_e', c3173_f1, leafS2_of_sq c3173_s2, leafS3_of_sq c3173_s3,
   c3173_iso, leafR8_of_sq c3173_nof2 c3173_nof3 c3173_nof4z⟩
theorem not_tile'_3173 (D : CongruentDissection 3173) : False :=
  not_tile_of_conditions' 3173 C'_3173 D

private theorem c3182_sqf   : LeafSqf 3182   := by decide +kernel
private theorem c3182_range : LeafRange 3182  := by decide +kernel
private theorem c3182_ell   : LeafEll 3182    := by decide +kernel
private theorem c3182_nsq   : NSqChkSq 3182   := by decide +kernel
private theorem c3182_har   : HArithChkSq 3182 := by decide +kernel
private theorem c3182_r     : LeafR 3182      := by decide +kernel
private theorem c3182_e'    : LeafE' 3182     := by decide +kernel
private theorem c3182_f1    : LeafF1 3182     := Or.inl (by decide)
private theorem c3182_s2    : S2ChkSq 3182    := by decide +kernel
private theorem c3182_s3    : S3ChkSq 3182    := by decide +kernel
private theorem c3182_iso   : LeafIso 3182    := by decide +kernel
private theorem c3182_nof2  : NoF2ChkSq 3182  := by decide +kernel
private theorem c3182_nof3  : NoF3ChkSq 3182  := by decide +kernel
private theorem c3182_nof4z : NoF4zChkSq 3182 := by decide +kernel
theorem C'_3182 : C' 3182 :=
  ⟨c3182_sqf, c3182_range, c3182_ell, leafNSq_of_sq c3182_nsq, leafHAr_of_sq c3182_har,
   c3182_r, c3182_e', c3182_f1, leafS2_of_sq c3182_s2, leafS3_of_sq c3182_s3,
   c3182_iso, leafR8_of_sq c3182_nof2 c3182_nof3 c3182_nof4z⟩
theorem not_tile'_3182 (D : CongruentDissection 3182) : False :=
  not_tile_of_conditions' 3182 C'_3182 D

end Erdos634.Draft.AllN2

/- AllN2Check68: N = 2203, 2206, 2207, 2215, 2217
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2203_sqf   : LeafSqf 2203   := by decide +kernel
private theorem c2203_range : LeafRange 2203  := by decide +kernel
private theorem c2203_ell   : LeafEll 2203    := by decide +kernel
private theorem c2203_nsq   : NSqChkSq 2203   := by decide +kernel
private theorem c2203_har   : HArithChkSq 2203 := by decide +kernel
private theorem c2203_r     : LeafR 2203      := by decide +kernel
private theorem c2203_e'    : LeafE' 2203     := by decide +kernel
private theorem c2203_f1    : LeafF1 2203     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2203_s2    : S2ChkSq 2203    := by decide +kernel
private theorem c2203_s3    : S3ChkSq 2203    := by decide +kernel
private theorem c2203_iso   : LeafIso 2203    := by decide +kernel
private theorem c2203_nof2  : NoF2ChkSq 2203  := by decide +kernel
private theorem c2203_nof3  : NoF3ChkSq 2203  := by decide +kernel
private theorem c2203_nof4z : NoF4zChkSq 2203 := by decide +kernel
theorem C'_2203 : C' 2203 :=
  ⟨c2203_sqf, c2203_range, c2203_ell, leafNSq_of_sq c2203_nsq, leafHAr_of_sq c2203_har,
   c2203_r, c2203_e', c2203_f1, leafS2_of_sq c2203_s2, leafS3_of_sq c2203_s3,
   c2203_iso, leafR8_of_sq c2203_nof2 c2203_nof3 c2203_nof4z⟩
theorem not_tile'_2203 (D : CongruentDissection 2203) : False :=
  not_tile_of_conditions' 2203 C'_2203 D

private theorem c2206_sqf   : LeafSqf 2206   := by decide +kernel
private theorem c2206_range : LeafRange 2206  := by decide +kernel
private theorem c2206_ell   : LeafEll 2206    := by decide +kernel
private theorem c2206_nsq   : NSqChkSq 2206   := by decide +kernel
private theorem c2206_har   : HArithChkSq 2206 := by decide +kernel
private theorem c2206_r     : LeafR 2206      := by decide +kernel
private theorem c2206_e'    : LeafE' 2206     := by decide +kernel
private theorem c2206_f1    : LeafF1 2206     := Or.inl (by decide)
private theorem c2206_s2    : S2ChkSq 2206    := by decide +kernel
private theorem c2206_s3    : S3ChkSq 2206    := by decide +kernel
private theorem c2206_iso   : LeafIso 2206    := by decide +kernel
private theorem c2206_nof2  : NoF2ChkSq 2206  := by decide +kernel
private theorem c2206_nof3  : NoF3ChkSq 2206  := by decide +kernel
private theorem c2206_nof4z : NoF4zChkSq 2206 := by decide +kernel
theorem C'_2206 : C' 2206 :=
  ⟨c2206_sqf, c2206_range, c2206_ell, leafNSq_of_sq c2206_nsq, leafHAr_of_sq c2206_har,
   c2206_r, c2206_e', c2206_f1, leafS2_of_sq c2206_s2, leafS3_of_sq c2206_s3,
   c2206_iso, leafR8_of_sq c2206_nof2 c2206_nof3 c2206_nof4z⟩
theorem not_tile'_2206 (D : CongruentDissection 2206) : False :=
  not_tile_of_conditions' 2206 C'_2206 D

private theorem c2207_sqf   : LeafSqf 2207   := by decide +kernel
private theorem c2207_range : LeafRange 2207  := by decide +kernel
private theorem c2207_ell   : LeafEll 2207    := by decide +kernel
private theorem c2207_nsq   : NSqChkSq 2207   := by decide +kernel
private theorem c2207_har   : HArithChkSq 2207 := by decide +kernel
private theorem c2207_r     : LeafR 2207      := by decide +kernel
private theorem c2207_e'    : LeafE' 2207     := by decide +kernel
private theorem c2207_f1    : LeafF1 2207     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2207_s2    : S2ChkSq 2207    := by decide +kernel
private theorem c2207_s3    : S3ChkSq 2207    := by decide +kernel
private theorem c2207_iso   : LeafIso 2207    := by decide +kernel
private theorem c2207_nof2  : NoF2ChkSq 2207  := by decide +kernel
private theorem c2207_nof3  : NoF3ChkSq 2207  := by decide +kernel
private theorem c2207_nof4z : NoF4zChkSq 2207 := by decide +kernel
theorem C'_2207 : C' 2207 :=
  ⟨c2207_sqf, c2207_range, c2207_ell, leafNSq_of_sq c2207_nsq, leafHAr_of_sq c2207_har,
   c2207_r, c2207_e', c2207_f1, leafS2_of_sq c2207_s2, leafS3_of_sq c2207_s3,
   c2207_iso, leafR8_of_sq c2207_nof2 c2207_nof3 c2207_nof4z⟩
theorem not_tile'_2207 (D : CongruentDissection 2207) : False :=
  not_tile_of_conditions' 2207 C'_2207 D

private theorem c2215_sqf   : LeafSqf 2215   := by decide +kernel
private theorem c2215_range : LeafRange 2215  := by decide +kernel
private theorem c2215_ell   : LeafEll 2215    := by decide +kernel
private theorem c2215_nsq   : NSqChkSq 2215   := by decide +kernel
private theorem c2215_har   : HArithChkSq 2215 := by decide +kernel
private theorem c2215_r     : LeafR 2215      := by decide +kernel
private theorem c2215_e'    : LeafE' 2215     := by decide +kernel
private theorem c2215_f1    : LeafF1 2215     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2215_s2    : S2ChkSq 2215    := by decide +kernel
private theorem c2215_s3    : S3ChkSq 2215    := by decide +kernel
private theorem c2215_iso   : LeafIso 2215    := by decide +kernel
private theorem c2215_nof2  : NoF2ChkSq 2215  := by decide +kernel
private theorem c2215_nof3  : NoF3ChkSq 2215  := by decide +kernel
private theorem c2215_nof4z : NoF4zChkSq 2215 := by decide +kernel
theorem C'_2215 : C' 2215 :=
  ⟨c2215_sqf, c2215_range, c2215_ell, leafNSq_of_sq c2215_nsq, leafHAr_of_sq c2215_har,
   c2215_r, c2215_e', c2215_f1, leafS2_of_sq c2215_s2, leafS3_of_sq c2215_s3,
   c2215_iso, leafR8_of_sq c2215_nof2 c2215_nof3 c2215_nof4z⟩
theorem not_tile'_2215 (D : CongruentDissection 2215) : False :=
  not_tile_of_conditions' 2215 C'_2215 D

private theorem c2217_sqf   : LeafSqf 2217   := by decide +kernel
private theorem c2217_range : LeafRange 2217  := by decide +kernel
private theorem c2217_ell   : LeafEll 2217    := by decide +kernel
private theorem c2217_nsq   : NSqChkSq 2217   := by decide +kernel
private theorem c2217_har   : HArithChkSq 2217 := by decide +kernel
private theorem c2217_r     : LeafR 2217      := by decide +kernel
private theorem c2217_e'    : LeafE' 2217     := by decide +kernel
private theorem c2217_f1    : LeafF1 2217     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2217_s2    : S2ChkSq 2217    := by decide +kernel
private theorem c2217_s3    : S3ChkSq 2217    := by decide +kernel
private theorem c2217_iso   : LeafIso 2217    := by decide +kernel
private theorem c2217_nof2  : NoF2ChkSq 2217  := by decide +kernel
private theorem c2217_nof3  : NoF3ChkSq 2217  := by decide +kernel
private theorem c2217_nof4z : NoF4zChkSq 2217 := by decide +kernel
theorem C'_2217 : C' 2217 :=
  ⟨c2217_sqf, c2217_range, c2217_ell, leafNSq_of_sq c2217_nsq, leafHAr_of_sq c2217_har,
   c2217_r, c2217_e', c2217_f1, leafS2_of_sq c2217_s2, leafS3_of_sq c2217_s3,
   c2217_iso, leafR8_of_sq c2217_nof2 c2217_nof3 c2217_nof4z⟩
theorem not_tile'_2217 (D : CongruentDissection 2217) : False :=
  not_tile_of_conditions' 2217 C'_2217 D

end Erdos634.Draft.AllN2

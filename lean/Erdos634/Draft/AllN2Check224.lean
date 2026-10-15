/- AllN2Check224: N = 4222, 4223, 4227, 4231, 4237
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4222_sqf   : LeafSqf 4222   := by decide +kernel
private theorem c4222_range : LeafRange 4222  := by decide +kernel
private theorem c4222_ell   : LeafEll 4222    := by decide +kernel
private theorem c4222_nsq   : NSqChkSq 4222   := by decide +kernel
private theorem c4222_har   : HArithChkSq 4222 := by decide +kernel
private theorem c4222_r     : LeafR 4222      := by decide +kernel
private theorem c4222_e'    : LeafE' 4222     := by decide +kernel
private theorem c4222_f1    : LeafF1 4222     := Or.inl (by decide)
private theorem c4222_s2    : S2ChkSq 4222    := by decide +kernel
private theorem c4222_s3    : S3ChkSq 4222    := by decide +kernel
private theorem c4222_iso   : LeafIso 4222    := by decide +kernel
private theorem c4222_nof2  : NoF2ChkSq 4222  := by decide +kernel
private theorem c4222_nof3  : NoF3ChkSq 4222  := by decide +kernel
private theorem c4222_nof4z : NoF4zChkSq 4222 := by decide +kernel
theorem C'_4222 : C' 4222 :=
  ⟨c4222_sqf, c4222_range, c4222_ell, leafNSq_of_sq c4222_nsq, leafHAr_of_sq c4222_har,
   c4222_r, c4222_e', c4222_f1, leafS2_of_sq c4222_s2, leafS3_of_sq c4222_s3,
   c4222_iso, leafR8_of_sq c4222_nof2 c4222_nof3 c4222_nof4z⟩
theorem not_tile'_4222 (D : CongruentDissection 4222) : False :=
  not_tile_of_conditions' 4222 C'_4222 D

private theorem c4223_sqf   : LeafSqf 4223   := by decide +kernel
private theorem c4223_range : LeafRange 4223  := by decide +kernel
private theorem c4223_ell   : LeafEll 4223    := by decide +kernel
private theorem c4223_nsq   : NSqChkSq 4223   := by decide +kernel
private theorem c4223_har   : HArithChkSq 4223 := by decide +kernel
private theorem c4223_r     : LeafR 4223      := by decide +kernel
private theorem c4223_e'    : LeafE' 4223     := by decide +kernel
private theorem c4223_f1    : LeafF1 4223     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4223_s2    : S2ChkSq 4223    := by decide +kernel
private theorem c4223_s3    : S3ChkSq 4223    := by decide +kernel
private theorem c4223_iso   : LeafIso 4223    := by decide +kernel
private theorem c4223_nof2  : NoF2ChkSq 4223  := by decide +kernel
private theorem c4223_nof3  : NoF3ChkSq 4223  := by decide +kernel
private theorem c4223_nof4z : NoF4zChkSq 4223 := by decide +kernel
theorem C'_4223 : C' 4223 :=
  ⟨c4223_sqf, c4223_range, c4223_ell, leafNSq_of_sq c4223_nsq, leafHAr_of_sq c4223_har,
   c4223_r, c4223_e', c4223_f1, leafS2_of_sq c4223_s2, leafS3_of_sq c4223_s3,
   c4223_iso, leafR8_of_sq c4223_nof2 c4223_nof3 c4223_nof4z⟩
theorem not_tile'_4223 (D : CongruentDissection 4223) : False :=
  not_tile_of_conditions' 4223 C'_4223 D

private theorem c4227_sqf   : LeafSqf 4227   := by decide +kernel
private theorem c4227_range : LeafRange 4227  := by decide +kernel
private theorem c4227_ell   : LeafEll 4227    := by decide +kernel
private theorem c4227_nsq   : NSqChkSq 4227   := by decide +kernel
private theorem c4227_har   : HArithChkSq 4227 := by decide +kernel
private theorem c4227_r     : LeafR 4227      := by decide +kernel
private theorem c4227_e'    : LeafE' 4227     := by decide +kernel
private theorem c4227_f1    : LeafF1 4227     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4227_s2    : S2ChkSq 4227    := by decide +kernel
private theorem c4227_s3    : S3ChkSq 4227    := by decide +kernel
private theorem c4227_iso   : LeafIso 4227    := by decide +kernel
private theorem c4227_nof2  : NoF2ChkSq 4227  := by decide +kernel
private theorem c4227_nof3  : NoF3ChkSq 4227  := by decide +kernel
private theorem c4227_nof4z : NoF4zChkSq 4227 := by decide +kernel
theorem C'_4227 : C' 4227 :=
  ⟨c4227_sqf, c4227_range, c4227_ell, leafNSq_of_sq c4227_nsq, leafHAr_of_sq c4227_har,
   c4227_r, c4227_e', c4227_f1, leafS2_of_sq c4227_s2, leafS3_of_sq c4227_s3,
   c4227_iso, leafR8_of_sq c4227_nof2 c4227_nof3 c4227_nof4z⟩
theorem not_tile'_4227 (D : CongruentDissection 4227) : False :=
  not_tile_of_conditions' 4227 C'_4227 D

private theorem c4231_sqf   : LeafSqf 4231   := by decide +kernel
private theorem c4231_range : LeafRange 4231  := by decide +kernel
private theorem c4231_ell   : LeafEll 4231    := by decide +kernel
private theorem c4231_nsq   : NSqChkSq 4231   := by decide +kernel
private theorem c4231_har   : HArithChkSq 4231 := by decide +kernel
private theorem c4231_r     : LeafR 4231      := by decide +kernel
private theorem c4231_e'    : LeafE' 4231     := by decide +kernel
private theorem c4231_f1    : LeafF1 4231     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4231_s2    : S2ChkSq 4231    := by decide +kernel
private theorem c4231_s3    : S3ChkSq 4231    := by decide +kernel
private theorem c4231_iso   : LeafIso 4231    := by decide +kernel
private theorem c4231_nof2  : NoF2ChkSq 4231  := by decide +kernel
private theorem c4231_nof3  : NoF3ChkSq 4231  := by decide +kernel
private theorem c4231_nof4z : NoF4zChkSq 4231 := by decide +kernel
theorem C'_4231 : C' 4231 :=
  ⟨c4231_sqf, c4231_range, c4231_ell, leafNSq_of_sq c4231_nsq, leafHAr_of_sq c4231_har,
   c4231_r, c4231_e', c4231_f1, leafS2_of_sq c4231_s2, leafS3_of_sq c4231_s3,
   c4231_iso, leafR8_of_sq c4231_nof2 c4231_nof3 c4231_nof4z⟩
theorem not_tile'_4231 (D : CongruentDissection 4231) : False :=
  not_tile_of_conditions' 4231 C'_4231 D

private theorem c4237_sqf   : LeafSqf 4237   := by decide +kernel
private theorem c4237_range : LeafRange 4237  := by decide +kernel
private theorem c4237_ell   : LeafEll 4237    := by decide +kernel
private theorem c4237_nsq   : NSqChkSq 4237   := by decide +kernel
private theorem c4237_har   : HArithChkSq 4237 := by decide +kernel
private theorem c4237_r     : LeafR 4237      := by decide +kernel
private theorem c4237_e'    : LeafE' 4237     := by decide +kernel
private theorem c4237_f1    : LeafF1 4237     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4237_s2    : S2ChkSq 4237    := by decide +kernel
private theorem c4237_s3    : S3ChkSq 4237    := by decide +kernel
private theorem c4237_iso   : LeafIso 4237    := by decide +kernel
private theorem c4237_nof2  : NoF2ChkSq 4237  := by decide +kernel
private theorem c4237_nof3  : NoF3ChkSq 4237  := by decide +kernel
private theorem c4237_nof4z : NoF4zChkSq 4237 := by decide +kernel
theorem C'_4237 : C' 4237 :=
  ⟨c4237_sqf, c4237_range, c4237_ell, leafNSq_of_sq c4237_nsq, leafHAr_of_sq c4237_har,
   c4237_r, c4237_e', c4237_f1, leafS2_of_sq c4237_s2, leafS3_of_sq c4237_s3,
   c4237_iso, leafR8_of_sq c4237_nof2 c4237_nof3 c4237_nof4z⟩
theorem not_tile'_4237 (D : CongruentDissection 4237) : False :=
  not_tile_of_conditions' 4237 C'_4237 D

end Erdos634.Draft.AllN2

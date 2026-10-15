/- AllN2Check74: N = 2287, 2291, 2294, 2298, 2302
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2287_sqf   : LeafSqf 2287   := by decide +kernel
private theorem c2287_range : LeafRange 2287  := by decide +kernel
private theorem c2287_ell   : LeafEll 2287    := by decide +kernel
private theorem c2287_nsq   : NSqChkSq 2287   := by decide +kernel
private theorem c2287_har   : HArithChkSq 2287 := by decide +kernel
private theorem c2287_r     : LeafR 2287      := by decide +kernel
private theorem c2287_e'    : LeafE' 2287     := by decide +kernel
private theorem c2287_f1    : LeafF1 2287     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2287_s2    : S2ChkSq 2287    := by decide +kernel
private theorem c2287_s3    : S3ChkSq 2287    := by decide +kernel
private theorem c2287_iso   : LeafIso 2287    := by decide +kernel
private theorem c2287_nof2  : NoF2ChkSq 2287  := by decide +kernel
private theorem c2287_nof3  : NoF3ChkSq 2287  := by decide +kernel
private theorem c2287_nof4z : NoF4zChkSq 2287 := by decide +kernel
theorem C'_2287 : C' 2287 :=
  ⟨c2287_sqf, c2287_range, c2287_ell, leafNSq_of_sq c2287_nsq, leafHAr_of_sq c2287_har,
   c2287_r, c2287_e', c2287_f1, leafS2_of_sq c2287_s2, leafS3_of_sq c2287_s3,
   c2287_iso, leafR8_of_sq c2287_nof2 c2287_nof3 c2287_nof4z⟩
theorem not_tile'_2287 (D : CongruentDissection 2287) : False :=
  not_tile_of_conditions' 2287 C'_2287 D

private theorem c2291_sqf   : LeafSqf 2291   := by decide +kernel
private theorem c2291_range : LeafRange 2291  := by decide +kernel
private theorem c2291_ell   : LeafEll 2291    := by decide +kernel
private theorem c2291_nsq   : NSqChkSq 2291   := by decide +kernel
private theorem c2291_har   : HArithChkSq 2291 := by decide +kernel
private theorem c2291_r     : LeafR 2291      := by decide +kernel
private theorem c2291_e'    : LeafE' 2291     := by decide +kernel
private theorem c2291_f1    : LeafF1 2291     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2291_s2    : S2ChkSq 2291    := by decide +kernel
private theorem c2291_s3    : S3ChkSq 2291    := by decide +kernel
private theorem c2291_iso   : LeafIso 2291    := by decide +kernel
private theorem c2291_nof2  : NoF2ChkSq 2291  := by decide +kernel
private theorem c2291_nof3  : NoF3ChkSq 2291  := by decide +kernel
private theorem c2291_nof4z : NoF4zChkSq 2291 := by decide +kernel
theorem C'_2291 : C' 2291 :=
  ⟨c2291_sqf, c2291_range, c2291_ell, leafNSq_of_sq c2291_nsq, leafHAr_of_sq c2291_har,
   c2291_r, c2291_e', c2291_f1, leafS2_of_sq c2291_s2, leafS3_of_sq c2291_s3,
   c2291_iso, leafR8_of_sq c2291_nof2 c2291_nof3 c2291_nof4z⟩
theorem not_tile'_2291 (D : CongruentDissection 2291) : False :=
  not_tile_of_conditions' 2291 C'_2291 D

private theorem c2294_sqf   : LeafSqf 2294   := by decide +kernel
private theorem c2294_range : LeafRange 2294  := by decide +kernel
private theorem c2294_ell   : LeafEll 2294    := by decide +kernel
private theorem c2294_nsq   : NSqChkSq 2294   := by decide +kernel
private theorem c2294_har   : HArithChkSq 2294 := by decide +kernel
private theorem c2294_r     : LeafR 2294      := by decide +kernel
private theorem c2294_e'    : LeafE' 2294     := by decide +kernel
private theorem c2294_f1    : LeafF1 2294     := Or.inl (by decide)
private theorem c2294_s2    : S2ChkSq 2294    := by decide +kernel
private theorem c2294_s3    : S3ChkSq 2294    := by decide +kernel
private theorem c2294_iso   : LeafIso 2294    := by decide +kernel
private theorem c2294_nof2  : NoF2ChkSq 2294  := by decide +kernel
private theorem c2294_nof3  : NoF3ChkSq 2294  := by decide +kernel
private theorem c2294_nof4z : NoF4zChkSq 2294 := by decide +kernel
theorem C'_2294 : C' 2294 :=
  ⟨c2294_sqf, c2294_range, c2294_ell, leafNSq_of_sq c2294_nsq, leafHAr_of_sq c2294_har,
   c2294_r, c2294_e', c2294_f1, leafS2_of_sq c2294_s2, leafS3_of_sq c2294_s3,
   c2294_iso, leafR8_of_sq c2294_nof2 c2294_nof3 c2294_nof4z⟩
theorem not_tile'_2294 (D : CongruentDissection 2294) : False :=
  not_tile_of_conditions' 2294 C'_2294 D

private theorem c2298_sqf   : LeafSqf 2298   := by decide +kernel
private theorem c2298_range : LeafRange 2298  := by decide +kernel
private theorem c2298_ell   : LeafEll 2298    := by decide +kernel
private theorem c2298_nsq   : NSqChkSq 2298   := by decide +kernel
private theorem c2298_har   : HArithChkSq 2298 := by decide +kernel
private theorem c2298_r     : LeafR 2298      := by decide +kernel
private theorem c2298_e'    : LeafE' 2298     := by decide +kernel
private theorem c2298_f1    : LeafF1 2298     := Or.inl (by decide)
private theorem c2298_s2    : S2ChkSq 2298    := by decide +kernel
private theorem c2298_s3    : S3ChkSq 2298    := by decide +kernel
private theorem c2298_iso   : LeafIso 2298    := by decide +kernel
private theorem c2298_nof2  : NoF2ChkSq 2298  := by decide +kernel
private theorem c2298_nof3  : NoF3ChkSq 2298  := by decide +kernel
private theorem c2298_nof4z : NoF4zChkSq 2298 := by decide +kernel
theorem C'_2298 : C' 2298 :=
  ⟨c2298_sqf, c2298_range, c2298_ell, leafNSq_of_sq c2298_nsq, leafHAr_of_sq c2298_har,
   c2298_r, c2298_e', c2298_f1, leafS2_of_sq c2298_s2, leafS3_of_sq c2298_s3,
   c2298_iso, leafR8_of_sq c2298_nof2 c2298_nof3 c2298_nof4z⟩
theorem not_tile'_2298 (D : CongruentDissection 2298) : False :=
  not_tile_of_conditions' 2298 C'_2298 D

private theorem c2302_sqf   : LeafSqf 2302   := by decide +kernel
private theorem c2302_range : LeafRange 2302  := by decide +kernel
private theorem c2302_ell   : LeafEll 2302    := by decide +kernel
private theorem c2302_nsq   : NSqChkSq 2302   := by decide +kernel
private theorem c2302_har   : HArithChkSq 2302 := by decide +kernel
private theorem c2302_r     : LeafR 2302      := by decide +kernel
private theorem c2302_e'    : LeafE' 2302     := by decide +kernel
private theorem c2302_f1    : LeafF1 2302     := Or.inl (by decide)
private theorem c2302_s2    : S2ChkSq 2302    := by decide +kernel
private theorem c2302_s3    : S3ChkSq 2302    := by decide +kernel
private theorem c2302_iso   : LeafIso 2302    := by decide +kernel
private theorem c2302_nof2  : NoF2ChkSq 2302  := by decide +kernel
private theorem c2302_nof3  : NoF3ChkSq 2302  := by decide +kernel
private theorem c2302_nof4z : NoF4zChkSq 2302 := by decide +kernel
theorem C'_2302 : C' 2302 :=
  ⟨c2302_sqf, c2302_range, c2302_ell, leafNSq_of_sq c2302_nsq, leafHAr_of_sq c2302_har,
   c2302_r, c2302_e', c2302_f1, leafS2_of_sq c2302_s2, leafS3_of_sq c2302_s3,
   c2302_iso, leafR8_of_sq c2302_nof2 c2302_nof3 c2302_nof4z⟩
theorem not_tile'_2302 (D : CongruentDissection 2302) : False :=
  not_tile_of_conditions' 2302 C'_2302 D

end Erdos634.Draft.AllN2

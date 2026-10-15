/- AllN2Check228: N = 4279, 4281, 4283, 4286, 4287
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4279_sqf   : LeafSqf 4279   := by decide +kernel
private theorem c4279_range : LeafRange 4279  := by decide +kernel
private theorem c4279_ell   : LeafEll 4279    := by decide +kernel
private theorem c4279_nsq   : NSqChkSq 4279   := by decide +kernel
private theorem c4279_har   : HArithChkSq 4279 := by decide +kernel
private theorem c4279_r     : LeafR 4279      := by decide +kernel
private theorem c4279_e'    : LeafE' 4279     := by decide +kernel
private theorem c4279_f1    : LeafF1 4279     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4279_s2    : S2ChkSq 4279    := by decide +kernel
private theorem c4279_s3    : S3ChkSq 4279    := by decide +kernel
private theorem c4279_iso   : LeafIso 4279    := by decide +kernel
private theorem c4279_nof2  : NoF2ChkSq 4279  := by decide +kernel
private theorem c4279_nof3  : NoF3ChkSq 4279  := by decide +kernel
private theorem c4279_nof4z : NoF4zChkSq 4279 := by decide +kernel
theorem C'_4279 : C' 4279 :=
  ⟨c4279_sqf, c4279_range, c4279_ell, leafNSq_of_sq c4279_nsq, leafHAr_of_sq c4279_har,
   c4279_r, c4279_e', c4279_f1, leafS2_of_sq c4279_s2, leafS3_of_sq c4279_s3,
   c4279_iso, leafR8_of_sq c4279_nof2 c4279_nof3 c4279_nof4z⟩
theorem not_tile'_4279 (D : CongruentDissection 4279) : False :=
  not_tile_of_conditions' 4279 C'_4279 D

private theorem c4281_sqf   : LeafSqf 4281   := by decide +kernel
private theorem c4281_range : LeafRange 4281  := by decide +kernel
private theorem c4281_ell   : LeafEll 4281    := by decide +kernel
private theorem c4281_nsq   : NSqChkSq 4281   := by decide +kernel
private theorem c4281_har   : HArithChkSq 4281 := by decide +kernel
private theorem c4281_r     : LeafR 4281      := by decide +kernel
private theorem c4281_e'    : LeafE' 4281     := by decide +kernel
private theorem c4281_f1    : LeafF1 4281     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4281_s2    : S2ChkSq 4281    := by decide +kernel
private theorem c4281_s3    : S3ChkSq 4281    := by decide +kernel
private theorem c4281_iso   : LeafIso 4281    := by decide +kernel
private theorem c4281_nof2  : NoF2ChkSq 4281  := by decide +kernel
private theorem c4281_nof3  : NoF3ChkSq 4281  := by decide +kernel
private theorem c4281_nof4z : NoF4zChkSq 4281 := by decide +kernel
theorem C'_4281 : C' 4281 :=
  ⟨c4281_sqf, c4281_range, c4281_ell, leafNSq_of_sq c4281_nsq, leafHAr_of_sq c4281_har,
   c4281_r, c4281_e', c4281_f1, leafS2_of_sq c4281_s2, leafS3_of_sq c4281_s3,
   c4281_iso, leafR8_of_sq c4281_nof2 c4281_nof3 c4281_nof4z⟩
theorem not_tile'_4281 (D : CongruentDissection 4281) : False :=
  not_tile_of_conditions' 4281 C'_4281 D

private theorem c4283_sqf   : LeafSqf 4283   := by decide +kernel
private theorem c4283_range : LeafRange 4283  := by decide +kernel
private theorem c4283_ell   : LeafEll 4283    := by decide +kernel
private theorem c4283_nsq   : NSqChkSq 4283   := by decide +kernel
private theorem c4283_har   : HArithChkSq 4283 := by decide +kernel
private theorem c4283_r     : LeafR 4283      := by decide +kernel
private theorem c4283_e'    : LeafE' 4283     := by decide +kernel
private theorem c4283_f1    : LeafF1 4283     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4283_s2    : S2ChkSq 4283    := by decide +kernel
private theorem c4283_s3    : S3ChkSq 4283    := by decide +kernel
private theorem c4283_iso   : LeafIso 4283    := by decide +kernel
private theorem c4283_nof2  : NoF2ChkSq 4283  := by decide +kernel
private theorem c4283_nof3  : NoF3ChkSq 4283  := by decide +kernel
private theorem c4283_nof4z : NoF4zChkSq 4283 := by decide +kernel
theorem C'_4283 : C' 4283 :=
  ⟨c4283_sqf, c4283_range, c4283_ell, leafNSq_of_sq c4283_nsq, leafHAr_of_sq c4283_har,
   c4283_r, c4283_e', c4283_f1, leafS2_of_sq c4283_s2, leafS3_of_sq c4283_s3,
   c4283_iso, leafR8_of_sq c4283_nof2 c4283_nof3 c4283_nof4z⟩
theorem not_tile'_4283 (D : CongruentDissection 4283) : False :=
  not_tile_of_conditions' 4283 C'_4283 D

private theorem c4286_sqf   : LeafSqf 4286   := by decide +kernel
private theorem c4286_range : LeafRange 4286  := by decide +kernel
private theorem c4286_ell   : LeafEll 4286    := by decide +kernel
private theorem c4286_nsq   : NSqChkSq 4286   := by decide +kernel
private theorem c4286_har   : HArithChkSq 4286 := by decide +kernel
private theorem c4286_r     : LeafR 4286      := by decide +kernel
private theorem c4286_e'    : LeafE' 4286     := by decide +kernel
private theorem c4286_f1    : LeafF1 4286     := Or.inl (by decide)
private theorem c4286_s2    : S2ChkSq 4286    := by decide +kernel
private theorem c4286_s3    : S3ChkSq 4286    := by decide +kernel
private theorem c4286_iso   : LeafIso 4286    := by decide +kernel
private theorem c4286_nof2  : NoF2ChkSq 4286  := by decide +kernel
private theorem c4286_nof3  : NoF3ChkSq 4286  := by decide +kernel
private theorem c4286_nof4z : NoF4zChkSq 4286 := by decide +kernel
theorem C'_4286 : C' 4286 :=
  ⟨c4286_sqf, c4286_range, c4286_ell, leafNSq_of_sq c4286_nsq, leafHAr_of_sq c4286_har,
   c4286_r, c4286_e', c4286_f1, leafS2_of_sq c4286_s2, leafS3_of_sq c4286_s3,
   c4286_iso, leafR8_of_sq c4286_nof2 c4286_nof3 c4286_nof4z⟩
theorem not_tile'_4286 (D : CongruentDissection 4286) : False :=
  not_tile_of_conditions' 4286 C'_4286 D

private theorem c4287_sqf   : LeafSqf 4287   := by decide +kernel
private theorem c4287_range : LeafRange 4287  := by decide +kernel
private theorem c4287_ell   : LeafEll 4287    := by decide +kernel
private theorem c4287_nsq   : NSqChkSq 4287   := by decide +kernel
private theorem c4287_har   : HArithChkSq 4287 := by decide +kernel
private theorem c4287_r     : LeafR 4287      := by decide +kernel
private theorem c4287_e'    : LeafE' 4287     := by decide +kernel
private theorem c4287_f1    : LeafF1 4287     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4287_s2    : S2ChkSq 4287    := by decide +kernel
private theorem c4287_s3    : S3ChkSq 4287    := by decide +kernel
private theorem c4287_iso   : LeafIso 4287    := by decide +kernel
private theorem c4287_nof2  : NoF2ChkSq 4287  := by decide +kernel
private theorem c4287_nof3  : NoF3ChkSq 4287  := by decide +kernel
private theorem c4287_nof4z : NoF4zChkSq 4287 := by decide +kernel
theorem C'_4287 : C' 4287 :=
  ⟨c4287_sqf, c4287_range, c4287_ell, leafNSq_of_sq c4287_nsq, leafHAr_of_sq c4287_har,
   c4287_r, c4287_e', c4287_f1, leafS2_of_sq c4287_s2, leafS3_of_sq c4287_s3,
   c4287_iso, leafR8_of_sq c4287_nof2 c4287_nof3 c4287_nof4z⟩
theorem not_tile'_4287 (D : CongruentDissection 4287) : False :=
  not_tile_of_conditions' 4287 C'_4287 D

end Erdos634.Draft.AllN2

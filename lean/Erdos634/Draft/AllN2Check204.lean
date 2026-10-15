/- AllN2Check204: N = 3955, 3957, 3958, 3959, 3962
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3955_sqf   : LeafSqf 3955   := by decide +kernel
private theorem c3955_range : LeafRange 3955  := by decide +kernel
private theorem c3955_ell   : LeafEll 3955    := by decide +kernel
private theorem c3955_nsq   : NSqChkSq 3955   := by decide +kernel
private theorem c3955_har   : HArithChkSq 3955 := by decide +kernel
private theorem c3955_r     : LeafR 3955      := by decide +kernel
private theorem c3955_e'    : LeafE' 3955     := by decide +kernel
private theorem c3955_f1    : LeafF1 3955     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3955_s2    : S2ChkSq 3955    := by decide +kernel
private theorem c3955_s3    : S3ChkSq 3955    := by decide +kernel
private theorem c3955_iso   : LeafIso 3955    := by decide +kernel
private theorem c3955_nof2  : NoF2ChkSq 3955  := by decide +kernel
private theorem c3955_nof3  : NoF3ChkSq 3955  := by decide +kernel
private theorem c3955_nof4z : NoF4zChkSq 3955 := by decide +kernel
theorem C'_3955 : C' 3955 :=
  ⟨c3955_sqf, c3955_range, c3955_ell, leafNSq_of_sq c3955_nsq, leafHAr_of_sq c3955_har,
   c3955_r, c3955_e', c3955_f1, leafS2_of_sq c3955_s2, leafS3_of_sq c3955_s3,
   c3955_iso, leafR8_of_sq c3955_nof2 c3955_nof3 c3955_nof4z⟩
theorem not_tile'_3955 (D : CongruentDissection 3955) : False :=
  not_tile_of_conditions' 3955 C'_3955 D

private theorem c3957_sqf   : LeafSqf 3957   := by decide +kernel
private theorem c3957_range : LeafRange 3957  := by decide +kernel
private theorem c3957_ell   : LeafEll 3957    := by decide +kernel
private theorem c3957_nsq   : NSqChkSq 3957   := by decide +kernel
private theorem c3957_har   : HArithChkSq 3957 := by decide +kernel
private theorem c3957_r     : LeafR 3957      := by decide +kernel
private theorem c3957_e'    : LeafE' 3957     := by decide +kernel
private theorem c3957_f1    : LeafF1 3957     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3957_s2    : S2ChkSq 3957    := by decide +kernel
private theorem c3957_s3    : S3ChkSq 3957    := by decide +kernel
private theorem c3957_iso   : LeafIso 3957    := by decide +kernel
private theorem c3957_nof2  : NoF2ChkSq 3957  := by decide +kernel
private theorem c3957_nof3  : NoF3ChkSq 3957  := by decide +kernel
private theorem c3957_nof4z : NoF4zChkSq 3957 := by decide +kernel
theorem C'_3957 : C' 3957 :=
  ⟨c3957_sqf, c3957_range, c3957_ell, leafNSq_of_sq c3957_nsq, leafHAr_of_sq c3957_har,
   c3957_r, c3957_e', c3957_f1, leafS2_of_sq c3957_s2, leafS3_of_sq c3957_s3,
   c3957_iso, leafR8_of_sq c3957_nof2 c3957_nof3 c3957_nof4z⟩
theorem not_tile'_3957 (D : CongruentDissection 3957) : False :=
  not_tile_of_conditions' 3957 C'_3957 D

private theorem c3958_sqf   : LeafSqf 3958   := by decide +kernel
private theorem c3958_range : LeafRange 3958  := by decide +kernel
private theorem c3958_ell   : LeafEll 3958    := by decide +kernel
private theorem c3958_nsq   : NSqChkSq 3958   := by decide +kernel
private theorem c3958_har   : HArithChkSq 3958 := by decide +kernel
private theorem c3958_r     : LeafR 3958      := by decide +kernel
private theorem c3958_e'    : LeafE' 3958     := by decide +kernel
private theorem c3958_f1    : LeafF1 3958     := Or.inl (by decide)
private theorem c3958_s2    : S2ChkSq 3958    := by decide +kernel
private theorem c3958_s3    : S3ChkSq 3958    := by decide +kernel
private theorem c3958_iso   : LeafIso 3958    := by decide +kernel
private theorem c3958_nof2  : NoF2ChkSq 3958  := by decide +kernel
private theorem c3958_nof3  : NoF3ChkSq 3958  := by decide +kernel
private theorem c3958_nof4z : NoF4zChkSq 3958 := by decide +kernel
theorem C'_3958 : C' 3958 :=
  ⟨c3958_sqf, c3958_range, c3958_ell, leafNSq_of_sq c3958_nsq, leafHAr_of_sq c3958_har,
   c3958_r, c3958_e', c3958_f1, leafS2_of_sq c3958_s2, leafS3_of_sq c3958_s3,
   c3958_iso, leafR8_of_sq c3958_nof2 c3958_nof3 c3958_nof4z⟩
theorem not_tile'_3958 (D : CongruentDissection 3958) : False :=
  not_tile_of_conditions' 3958 C'_3958 D

private theorem c3959_sqf   : LeafSqf 3959   := by decide +kernel
private theorem c3959_range : LeafRange 3959  := by decide +kernel
private theorem c3959_ell   : LeafEll 3959    := by decide +kernel
private theorem c3959_nsq   : NSqChkSq 3959   := by decide +kernel
private theorem c3959_har   : HArithChkSq 3959 := by decide +kernel
private theorem c3959_r     : LeafR 3959      := by decide +kernel
private theorem c3959_e'    : LeafE' 3959     := by decide +kernel
private theorem c3959_f1    : LeafF1 3959     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3959_s2    : S2ChkSq 3959    := by decide +kernel
private theorem c3959_s3    : S3ChkSq 3959    := by decide +kernel
private theorem c3959_iso   : LeafIso 3959    := by decide +kernel
private theorem c3959_nof2  : NoF2ChkSq 3959  := by decide +kernel
private theorem c3959_nof3  : NoF3ChkSq 3959  := by decide +kernel
private theorem c3959_nof4z : NoF4zChkSq 3959 := by decide +kernel
theorem C'_3959 : C' 3959 :=
  ⟨c3959_sqf, c3959_range, c3959_ell, leafNSq_of_sq c3959_nsq, leafHAr_of_sq c3959_har,
   c3959_r, c3959_e', c3959_f1, leafS2_of_sq c3959_s2, leafS3_of_sq c3959_s3,
   c3959_iso, leafR8_of_sq c3959_nof2 c3959_nof3 c3959_nof4z⟩
theorem not_tile'_3959 (D : CongruentDissection 3959) : False :=
  not_tile_of_conditions' 3959 C'_3959 D

private theorem c3962_sqf   : LeafSqf 3962   := by decide +kernel
private theorem c3962_range : LeafRange 3962  := by decide +kernel
private theorem c3962_ell   : LeafEll 3962    := by decide +kernel
private theorem c3962_nsq   : NSqChkSq 3962   := by decide +kernel
private theorem c3962_har   : HArithChkSq 3962 := by decide +kernel
private theorem c3962_r     : LeafR 3962      := by decide +kernel
private theorem c3962_e'    : LeafE' 3962     := by decide +kernel
private theorem c3962_f1    : LeafF1 3962     := Or.inl (by decide)
private theorem c3962_s2    : S2ChkSq 3962    := by decide +kernel
private theorem c3962_s3    : S3ChkSq 3962    := by decide +kernel
private theorem c3962_iso   : LeafIso 3962    := by decide +kernel
private theorem c3962_nof2  : NoF2ChkSq 3962  := by decide +kernel
private theorem c3962_nof3  : NoF3ChkSq 3962  := by decide +kernel
private theorem c3962_nof4z : NoF4zChkSq 3962 := by decide +kernel
theorem C'_3962 : C' 3962 :=
  ⟨c3962_sqf, c3962_range, c3962_ell, leafNSq_of_sq c3962_nsq, leafHAr_of_sq c3962_har,
   c3962_r, c3962_e', c3962_f1, leafS2_of_sq c3962_s2, leafS3_of_sq c3962_s3,
   c3962_iso, leafR8_of_sq c3962_nof2 c3962_nof3 c3962_nof4z⟩
theorem not_tile'_3962 (D : CongruentDissection 3962) : False :=
  not_tile_of_conditions' 3962 C'_3962 D

end Erdos634.Draft.AllN2

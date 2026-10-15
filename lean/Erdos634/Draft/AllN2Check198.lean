/- AllN2Check198: N = 3883, 3886, 3891, 3894, 3895
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3883_sqf   : LeafSqf 3883   := by decide +kernel
private theorem c3883_range : LeafRange 3883  := by decide +kernel
private theorem c3883_ell   : LeafEll 3883    := by decide +kernel
private theorem c3883_nsq   : NSqChkSq 3883   := by decide +kernel
private theorem c3883_har   : HArithChkSq 3883 := by decide +kernel
private theorem c3883_r     : LeafR 3883      := by decide +kernel
private theorem c3883_e'    : LeafE' 3883     := by decide +kernel
private theorem c3883_f1    : LeafF1 3883     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3883_s2    : S2ChkSq 3883    := by decide +kernel
private theorem c3883_s3    : S3ChkSq 3883    := by decide +kernel
private theorem c3883_iso   : LeafIso 3883    := by decide +kernel
private theorem c3883_nof2  : NoF2ChkSq 3883  := by decide +kernel
private theorem c3883_nof3  : NoF3ChkSq 3883  := by decide +kernel
private theorem c3883_nof4z : NoF4zChkSq 3883 := by decide +kernel
theorem C'_3883 : C' 3883 :=
  ⟨c3883_sqf, c3883_range, c3883_ell, leafNSq_of_sq c3883_nsq, leafHAr_of_sq c3883_har,
   c3883_r, c3883_e', c3883_f1, leafS2_of_sq c3883_s2, leafS3_of_sq c3883_s3,
   c3883_iso, leafR8_of_sq c3883_nof2 c3883_nof3 c3883_nof4z⟩
theorem not_tile'_3883 (D : CongruentDissection 3883) : False :=
  not_tile_of_conditions' 3883 C'_3883 D

private theorem c3886_sqf   : LeafSqf 3886   := by decide +kernel
private theorem c3886_range : LeafRange 3886  := by decide +kernel
private theorem c3886_ell   : LeafEll 3886    := by decide +kernel
private theorem c3886_nsq   : NSqChkSq 3886   := by decide +kernel
private theorem c3886_har   : HArithChkSq 3886 := by decide +kernel
private theorem c3886_r     : LeafR 3886      := by decide +kernel
private theorem c3886_e'    : LeafE' 3886     := by decide +kernel
private theorem c3886_f1    : LeafF1 3886     := Or.inl (by decide)
private theorem c3886_s2    : S2ChkSq 3886    := by decide +kernel
private theorem c3886_s3    : S3ChkSq 3886    := by decide +kernel
private theorem c3886_iso   : LeafIso 3886    := by decide +kernel
private theorem c3886_nof2  : NoF2ChkSq 3886  := by decide +kernel
private theorem c3886_nof3  : NoF3ChkSq 3886  := by decide +kernel
private theorem c3886_nof4z : NoF4zChkSq 3886 := by decide +kernel
theorem C'_3886 : C' 3886 :=
  ⟨c3886_sqf, c3886_range, c3886_ell, leafNSq_of_sq c3886_nsq, leafHAr_of_sq c3886_har,
   c3886_r, c3886_e', c3886_f1, leafS2_of_sq c3886_s2, leafS3_of_sq c3886_s3,
   c3886_iso, leafR8_of_sq c3886_nof2 c3886_nof3 c3886_nof4z⟩
theorem not_tile'_3886 (D : CongruentDissection 3886) : False :=
  not_tile_of_conditions' 3886 C'_3886 D

private theorem c3891_sqf   : LeafSqf 3891   := by decide +kernel
private theorem c3891_range : LeafRange 3891  := by decide +kernel
private theorem c3891_ell   : LeafEll 3891    := by decide +kernel
private theorem c3891_nsq   : NSqChkSq 3891   := by decide +kernel
private theorem c3891_har   : HArithChkSq 3891 := by decide +kernel
private theorem c3891_r     : LeafR 3891      := by decide +kernel
private theorem c3891_e'    : LeafE' 3891     := by decide +kernel
private theorem c3891_f1    : LeafF1 3891     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3891_s2    : S2ChkSq 3891    := by decide +kernel
private theorem c3891_s3    : S3ChkSq 3891    := by decide +kernel
private theorem c3891_iso   : LeafIso 3891    := by decide +kernel
private theorem c3891_nof2  : NoF2ChkSq 3891  := by decide +kernel
private theorem c3891_nof3  : NoF3ChkSq 3891  := by decide +kernel
private theorem c3891_nof4z : NoF4zChkSq 3891 := by decide +kernel
theorem C'_3891 : C' 3891 :=
  ⟨c3891_sqf, c3891_range, c3891_ell, leafNSq_of_sq c3891_nsq, leafHAr_of_sq c3891_har,
   c3891_r, c3891_e', c3891_f1, leafS2_of_sq c3891_s2, leafS3_of_sq c3891_s3,
   c3891_iso, leafR8_of_sq c3891_nof2 c3891_nof3 c3891_nof4z⟩
theorem not_tile'_3891 (D : CongruentDissection 3891) : False :=
  not_tile_of_conditions' 3891 C'_3891 D

private theorem c3894_sqf   : LeafSqf 3894   := by decide +kernel
private theorem c3894_range : LeafRange 3894  := by decide +kernel
private theorem c3894_ell   : LeafEll 3894    := by decide +kernel
private theorem c3894_nsq   : NSqChkSq 3894   := by decide +kernel
private theorem c3894_har   : HArithChkSq 3894 := by decide +kernel
private theorem c3894_r     : LeafR 3894      := by decide +kernel
private theorem c3894_e'    : LeafE' 3894     := by decide +kernel
private theorem c3894_f1    : LeafF1 3894     := Or.inl (by decide)
private theorem c3894_s2    : S2ChkSq 3894    := by decide +kernel
private theorem c3894_s3    : S3ChkSq 3894    := by decide +kernel
private theorem c3894_iso   : LeafIso 3894    := by decide +kernel
private theorem c3894_nof2  : NoF2ChkSq 3894  := by decide +kernel
private theorem c3894_nof3  : NoF3ChkSq 3894  := by decide +kernel
private theorem c3894_nof4z : NoF4zChkSq 3894 := by decide +kernel
theorem C'_3894 : C' 3894 :=
  ⟨c3894_sqf, c3894_range, c3894_ell, leafNSq_of_sq c3894_nsq, leafHAr_of_sq c3894_har,
   c3894_r, c3894_e', c3894_f1, leafS2_of_sq c3894_s2, leafS3_of_sq c3894_s3,
   c3894_iso, leafR8_of_sq c3894_nof2 c3894_nof3 c3894_nof4z⟩
theorem not_tile'_3894 (D : CongruentDissection 3894) : False :=
  not_tile_of_conditions' 3894 C'_3894 D

private theorem c3895_sqf   : LeafSqf 3895   := by decide +kernel
private theorem c3895_range : LeafRange 3895  := by decide +kernel
private theorem c3895_ell   : LeafEll 3895    := by decide +kernel
private theorem c3895_nsq   : NSqChkSq 3895   := by decide +kernel
private theorem c3895_har   : HArithChkSq 3895 := by decide +kernel
private theorem c3895_r     : LeafR 3895      := by decide +kernel
private theorem c3895_e'    : LeafE' 3895     := by decide +kernel
private theorem c3895_f1    : LeafF1 3895     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3895_s2    : S2ChkSq 3895    := by decide +kernel
private theorem c3895_s3    : S3ChkSq 3895    := by decide +kernel
private theorem c3895_iso   : LeafIso 3895    := by decide +kernel
private theorem c3895_nof2  : NoF2ChkSq 3895  := by decide +kernel
private theorem c3895_nof3  : NoF3ChkSq 3895  := by decide +kernel
private theorem c3895_nof4z : NoF4zChkSq 3895 := by decide +kernel
theorem C'_3895 : C' 3895 :=
  ⟨c3895_sqf, c3895_range, c3895_ell, leafNSq_of_sq c3895_nsq, leafHAr_of_sq c3895_har,
   c3895_r, c3895_e', c3895_f1, leafS2_of_sq c3895_s2, leafS3_of_sq c3895_s3,
   c3895_iso, leafR8_of_sq c3895_nof2 c3895_nof3 c3895_nof4z⟩
theorem not_tile'_3895 (D : CongruentDissection 3895) : False :=
  not_tile_of_conditions' 3895 C'_3895 D

end Erdos634.Draft.AllN2

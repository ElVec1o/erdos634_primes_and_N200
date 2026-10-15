/- AllN2Check174: N = 3566, 3569, 3571, 3574, 3579
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3566_sqf   : LeafSqf 3566   := by decide +kernel
private theorem c3566_range : LeafRange 3566  := by decide +kernel
private theorem c3566_ell   : LeafEll 3566    := by decide +kernel
private theorem c3566_nsq   : NSqChkSq 3566   := by decide +kernel
private theorem c3566_har   : HArithChkSq 3566 := by decide +kernel
private theorem c3566_r     : LeafR 3566      := by decide +kernel
private theorem c3566_e'    : LeafE' 3566     := by decide +kernel
private theorem c3566_f1    : LeafF1 3566     := Or.inl (by decide)
private theorem c3566_s2    : S2ChkSq 3566    := by decide +kernel
private theorem c3566_s3    : S3ChkSq 3566    := by decide +kernel
private theorem c3566_iso   : LeafIso 3566    := by decide +kernel
private theorem c3566_nof2  : NoF2ChkSq 3566  := by decide +kernel
private theorem c3566_nof3  : NoF3ChkSq 3566  := by decide +kernel
private theorem c3566_nof4z : NoF4zChkSq 3566 := by decide +kernel
theorem C'_3566 : C' 3566 :=
  ⟨c3566_sqf, c3566_range, c3566_ell, leafNSq_of_sq c3566_nsq, leafHAr_of_sq c3566_har,
   c3566_r, c3566_e', c3566_f1, leafS2_of_sq c3566_s2, leafS3_of_sq c3566_s3,
   c3566_iso, leafR8_of_sq c3566_nof2 c3566_nof3 c3566_nof4z⟩
theorem not_tile'_3566 (D : CongruentDissection 3566) : False :=
  not_tile_of_conditions' 3566 C'_3566 D

private theorem c3569_sqf   : LeafSqf 3569   := by decide +kernel
private theorem c3569_range : LeafRange 3569  := by decide +kernel
private theorem c3569_ell   : LeafEll 3569    := by decide +kernel
private theorem c3569_nsq   : NSqChkSq 3569   := by decide +kernel
private theorem c3569_har   : HArithChkSq 3569 := by decide +kernel
private theorem c3569_r     : LeafR 3569      := by decide +kernel
private theorem c3569_e'    : LeafE' 3569     := by decide +kernel
private theorem c3569_f1    : LeafF1 3569     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3569_s2    : S2ChkSq 3569    := by decide +kernel
private theorem c3569_s3    : S3ChkSq 3569    := by decide +kernel
private theorem c3569_iso   : LeafIso 3569    := by decide +kernel
private theorem c3569_nof2  : NoF2ChkSq 3569  := by decide +kernel
private theorem c3569_nof3  : NoF3ChkSq 3569  := by decide +kernel
private theorem c3569_nof4z : NoF4zChkSq 3569 := by decide +kernel
theorem C'_3569 : C' 3569 :=
  ⟨c3569_sqf, c3569_range, c3569_ell, leafNSq_of_sq c3569_nsq, leafHAr_of_sq c3569_har,
   c3569_r, c3569_e', c3569_f1, leafS2_of_sq c3569_s2, leafS3_of_sq c3569_s3,
   c3569_iso, leafR8_of_sq c3569_nof2 c3569_nof3 c3569_nof4z⟩
theorem not_tile'_3569 (D : CongruentDissection 3569) : False :=
  not_tile_of_conditions' 3569 C'_3569 D

private theorem c3571_sqf   : LeafSqf 3571   := by decide +kernel
private theorem c3571_range : LeafRange 3571  := by decide +kernel
private theorem c3571_ell   : LeafEll 3571    := by decide +kernel
private theorem c3571_nsq   : NSqChkSq 3571   := by decide +kernel
private theorem c3571_har   : HArithChkSq 3571 := by decide +kernel
private theorem c3571_r     : LeafR 3571      := by decide +kernel
private theorem c3571_e'    : LeafE' 3571     := by decide +kernel
private theorem c3571_f1    : LeafF1 3571     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3571_s2    : S2ChkSq 3571    := by decide +kernel
private theorem c3571_s3    : S3ChkSq 3571    := by decide +kernel
private theorem c3571_iso   : LeafIso 3571    := by decide +kernel
private theorem c3571_nof2  : NoF2ChkSq 3571  := by decide +kernel
private theorem c3571_nof3  : NoF3ChkSq 3571  := by decide +kernel
private theorem c3571_nof4z : NoF4zChkSq 3571 := by decide +kernel
theorem C'_3571 : C' 3571 :=
  ⟨c3571_sqf, c3571_range, c3571_ell, leafNSq_of_sq c3571_nsq, leafHAr_of_sq c3571_har,
   c3571_r, c3571_e', c3571_f1, leafS2_of_sq c3571_s2, leafS3_of_sq c3571_s3,
   c3571_iso, leafR8_of_sq c3571_nof2 c3571_nof3 c3571_nof4z⟩
theorem not_tile'_3571 (D : CongruentDissection 3571) : False :=
  not_tile_of_conditions' 3571 C'_3571 D

private theorem c3574_sqf   : LeafSqf 3574   := by decide +kernel
private theorem c3574_range : LeafRange 3574  := by decide +kernel
private theorem c3574_ell   : LeafEll 3574    := by decide +kernel
private theorem c3574_nsq   : NSqChkSq 3574   := by decide +kernel
private theorem c3574_har   : HArithChkSq 3574 := by decide +kernel
private theorem c3574_r     : LeafR 3574      := by decide +kernel
private theorem c3574_e'    : LeafE' 3574     := by decide +kernel
private theorem c3574_f1    : LeafF1 3574     := Or.inl (by decide)
private theorem c3574_s2    : S2ChkSq 3574    := by decide +kernel
private theorem c3574_s3    : S3ChkSq 3574    := by decide +kernel
private theorem c3574_iso   : LeafIso 3574    := by decide +kernel
private theorem c3574_nof2  : NoF2ChkSq 3574  := by decide +kernel
private theorem c3574_nof3  : NoF3ChkSq 3574  := by decide +kernel
private theorem c3574_nof4z : NoF4zChkSq 3574 := by decide +kernel
theorem C'_3574 : C' 3574 :=
  ⟨c3574_sqf, c3574_range, c3574_ell, leafNSq_of_sq c3574_nsq, leafHAr_of_sq c3574_har,
   c3574_r, c3574_e', c3574_f1, leafS2_of_sq c3574_s2, leafS3_of_sq c3574_s3,
   c3574_iso, leafR8_of_sq c3574_nof2 c3574_nof3 c3574_nof4z⟩
theorem not_tile'_3574 (D : CongruentDissection 3574) : False :=
  not_tile_of_conditions' 3574 C'_3574 D

private theorem c3579_sqf   : LeafSqf 3579   := by decide +kernel
private theorem c3579_range : LeafRange 3579  := by decide +kernel
private theorem c3579_ell   : LeafEll 3579    := by decide +kernel
private theorem c3579_nsq   : NSqChkSq 3579   := by decide +kernel
private theorem c3579_har   : HArithChkSq 3579 := by decide +kernel
private theorem c3579_r     : LeafR 3579      := by decide +kernel
private theorem c3579_e'    : LeafE' 3579     := by decide +kernel
private theorem c3579_f1    : LeafF1 3579     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3579_s2    : S2ChkSq 3579    := by decide +kernel
private theorem c3579_s3    : S3ChkSq 3579    := by decide +kernel
private theorem c3579_iso   : LeafIso 3579    := by decide +kernel
private theorem c3579_nof2  : NoF2ChkSq 3579  := by decide +kernel
private theorem c3579_nof3  : NoF3ChkSq 3579  := by decide +kernel
private theorem c3579_nof4z : NoF4zChkSq 3579 := by decide +kernel
theorem C'_3579 : C' 3579 :=
  ⟨c3579_sqf, c3579_range, c3579_ell, leafNSq_of_sq c3579_nsq, leafHAr_of_sq c3579_har,
   c3579_r, c3579_e', c3579_f1, leafS2_of_sq c3579_s2, leafS3_of_sq c3579_s3,
   c3579_iso, leafR8_of_sq c3579_nof2 c3579_nof3 c3579_nof4z⟩
theorem not_tile'_3579 (D : CongruentDissection 3579) : False :=
  not_tile_of_conditions' 3579 C'_3579 D

end Erdos634.Draft.AllN2

/- AllN2Check184: N = 3686, 3687, 3689, 3691, 3693
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3686_sqf   : LeafSqf 3686   := by decide +kernel
private theorem c3686_range : LeafRange 3686  := by decide +kernel
private theorem c3686_ell   : LeafEll 3686    := by decide +kernel
private theorem c3686_nsq   : NSqChkSq 3686   := by decide +kernel
private theorem c3686_har   : HArithChkSq 3686 := by decide +kernel
private theorem c3686_r     : LeafR 3686      := by decide +kernel
private theorem c3686_e'    : LeafE' 3686     := by decide +kernel
private theorem c3686_f1    : LeafF1 3686     := Or.inl (by decide)
private theorem c3686_s2    : S2ChkSq 3686    := by decide +kernel
private theorem c3686_s3    : S3ChkSq 3686    := by decide +kernel
private theorem c3686_iso   : LeafIso 3686    := by decide +kernel
private theorem c3686_nof2  : NoF2ChkSq 3686  := by decide +kernel
private theorem c3686_nof3  : NoF3ChkSq 3686  := by decide +kernel
private theorem c3686_nof4z : NoF4zChkSq 3686 := by decide +kernel
theorem C'_3686 : C' 3686 :=
  ⟨c3686_sqf, c3686_range, c3686_ell, leafNSq_of_sq c3686_nsq, leafHAr_of_sq c3686_har,
   c3686_r, c3686_e', c3686_f1, leafS2_of_sq c3686_s2, leafS3_of_sq c3686_s3,
   c3686_iso, leafR8_of_sq c3686_nof2 c3686_nof3 c3686_nof4z⟩
theorem not_tile'_3686 (D : CongruentDissection 3686) : False :=
  not_tile_of_conditions' 3686 C'_3686 D

private theorem c3687_sqf   : LeafSqf 3687   := by decide +kernel
private theorem c3687_range : LeafRange 3687  := by decide +kernel
private theorem c3687_ell   : LeafEll 3687    := by decide +kernel
private theorem c3687_nsq   : NSqChkSq 3687   := by decide +kernel
private theorem c3687_har   : HArithChkSq 3687 := by decide +kernel
private theorem c3687_r     : LeafR 3687      := by decide +kernel
private theorem c3687_e'    : LeafE' 3687     := by decide +kernel
private theorem c3687_f1    : LeafF1 3687     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3687_s2    : S2ChkSq 3687    := by decide +kernel
private theorem c3687_s3    : S3ChkSq 3687    := by decide +kernel
private theorem c3687_iso   : LeafIso 3687    := by decide +kernel
private theorem c3687_nof2  : NoF2ChkSq 3687  := by decide +kernel
private theorem c3687_nof3  : NoF3ChkSq 3687  := by decide +kernel
private theorem c3687_nof4z : NoF4zChkSq 3687 := by decide +kernel
theorem C'_3687 : C' 3687 :=
  ⟨c3687_sqf, c3687_range, c3687_ell, leafNSq_of_sq c3687_nsq, leafHAr_of_sq c3687_har,
   c3687_r, c3687_e', c3687_f1, leafS2_of_sq c3687_s2, leafS3_of_sq c3687_s3,
   c3687_iso, leafR8_of_sq c3687_nof2 c3687_nof3 c3687_nof4z⟩
theorem not_tile'_3687 (D : CongruentDissection 3687) : False :=
  not_tile_of_conditions' 3687 C'_3687 D

private theorem c3689_sqf   : LeafSqf 3689   := by decide +kernel
private theorem c3689_range : LeafRange 3689  := by decide +kernel
private theorem c3689_ell   : LeafEll 3689    := by decide +kernel
private theorem c3689_nsq   : NSqChkSq 3689   := by decide +kernel
private theorem c3689_har   : HArithChkSq 3689 := by decide +kernel
private theorem c3689_r     : LeafR 3689      := by decide +kernel
private theorem c3689_e'    : LeafE' 3689     := by decide +kernel
private theorem c3689_f1    : LeafF1 3689     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3689_s2    : S2ChkSq 3689    := by decide +kernel
private theorem c3689_s3    : S3ChkSq 3689    := by decide +kernel
private theorem c3689_iso   : LeafIso 3689    := by decide +kernel
private theorem c3689_nof2  : NoF2ChkSq 3689  := by decide +kernel
private theorem c3689_nof3  : NoF3ChkSq 3689  := by decide +kernel
private theorem c3689_nof4z : NoF4zChkSq 3689 := by decide +kernel
theorem C'_3689 : C' 3689 :=
  ⟨c3689_sqf, c3689_range, c3689_ell, leafNSq_of_sq c3689_nsq, leafHAr_of_sq c3689_har,
   c3689_r, c3689_e', c3689_f1, leafS2_of_sq c3689_s2, leafS3_of_sq c3689_s3,
   c3689_iso, leafR8_of_sq c3689_nof2 c3689_nof3 c3689_nof4z⟩
theorem not_tile'_3689 (D : CongruentDissection 3689) : False :=
  not_tile_of_conditions' 3689 C'_3689 D

private theorem c3691_sqf   : LeafSqf 3691   := by decide +kernel
private theorem c3691_range : LeafRange 3691  := by decide +kernel
private theorem c3691_ell   : LeafEll 3691    := by decide +kernel
private theorem c3691_nsq   : NSqChkSq 3691   := by decide +kernel
private theorem c3691_har   : HArithChkSq 3691 := by decide +kernel
private theorem c3691_r     : LeafR 3691      := by decide +kernel
private theorem c3691_e'    : LeafE' 3691     := by decide +kernel
private theorem c3691_f1    : LeafF1 3691     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3691_s2    : S2ChkSq 3691    := by decide +kernel
private theorem c3691_s3    : S3ChkSq 3691    := by decide +kernel
private theorem c3691_iso   : LeafIso 3691    := by decide +kernel
private theorem c3691_nof2  : NoF2ChkSq 3691  := by decide +kernel
private theorem c3691_nof3  : NoF3ChkSq 3691  := by decide +kernel
private theorem c3691_nof4z : NoF4zChkSq 3691 := by decide +kernel
theorem C'_3691 : C' 3691 :=
  ⟨c3691_sqf, c3691_range, c3691_ell, leafNSq_of_sq c3691_nsq, leafHAr_of_sq c3691_har,
   c3691_r, c3691_e', c3691_f1, leafS2_of_sq c3691_s2, leafS3_of_sq c3691_s3,
   c3691_iso, leafR8_of_sq c3691_nof2 c3691_nof3 c3691_nof4z⟩
theorem not_tile'_3691 (D : CongruentDissection 3691) : False :=
  not_tile_of_conditions' 3691 C'_3691 D

private theorem c3693_sqf   : LeafSqf 3693   := by decide +kernel
private theorem c3693_range : LeafRange 3693  := by decide +kernel
private theorem c3693_ell   : LeafEll 3693    := by decide +kernel
private theorem c3693_nsq   : NSqChkSq 3693   := by decide +kernel
private theorem c3693_har   : HArithChkSq 3693 := by decide +kernel
private theorem c3693_r     : LeafR 3693      := by decide +kernel
private theorem c3693_e'    : LeafE' 3693     := by decide +kernel
private theorem c3693_f1    : LeafF1 3693     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3693_s2    : S2ChkSq 3693    := by decide +kernel
private theorem c3693_s3    : S3ChkSq 3693    := by decide +kernel
private theorem c3693_iso   : LeafIso 3693    := by decide +kernel
private theorem c3693_nof2  : NoF2ChkSq 3693  := by decide +kernel
private theorem c3693_nof3  : NoF3ChkSq 3693  := by decide +kernel
private theorem c3693_nof4z : NoF4zChkSq 3693 := by decide +kernel
theorem C'_3693 : C' 3693 :=
  ⟨c3693_sqf, c3693_range, c3693_ell, leafNSq_of_sq c3693_nsq, leafHAr_of_sq c3693_har,
   c3693_r, c3693_e', c3693_f1, leafS2_of_sq c3693_s2, leafS3_of_sq c3693_s3,
   c3693_iso, leafR8_of_sq c3693_nof2 c3693_nof3 c3693_nof4z⟩
theorem not_tile'_3693 (D : CongruentDissection 3693) : False :=
  not_tile_of_conditions' 3693 C'_3693 D

end Erdos634.Draft.AllN2

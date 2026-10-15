/- AllN2Check186: N = 3711, 3713, 3714, 3715, 3719
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3711_sqf   : LeafSqf 3711   := by decide +kernel
private theorem c3711_range : LeafRange 3711  := by decide +kernel
private theorem c3711_ell   : LeafEll 3711    := by decide +kernel
private theorem c3711_nsq   : NSqChkSq 3711   := by decide +kernel
private theorem c3711_har   : HArithChkSq 3711 := by decide +kernel
private theorem c3711_r     : LeafR 3711      := by decide +kernel
private theorem c3711_e'    : LeafE' 3711     := by decide +kernel
private theorem c3711_f1    : LeafF1 3711     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3711_s2    : S2ChkSq 3711    := by decide +kernel
private theorem c3711_s3    : S3ChkSq 3711    := by decide +kernel
private theorem c3711_iso   : LeafIso 3711    := by decide +kernel
private theorem c3711_nof2  : NoF2ChkSq 3711  := by decide +kernel
private theorem c3711_nof3  : NoF3ChkSq 3711  := by decide +kernel
private theorem c3711_nof4z : NoF4zChkSq 3711 := by decide +kernel
theorem C'_3711 : C' 3711 :=
  ⟨c3711_sqf, c3711_range, c3711_ell, leafNSq_of_sq c3711_nsq, leafHAr_of_sq c3711_har,
   c3711_r, c3711_e', c3711_f1, leafS2_of_sq c3711_s2, leafS3_of_sq c3711_s3,
   c3711_iso, leafR8_of_sq c3711_nof2 c3711_nof3 c3711_nof4z⟩
theorem not_tile'_3711 (D : CongruentDissection 3711) : False :=
  not_tile_of_conditions' 3711 C'_3711 D

private theorem c3713_sqf   : LeafSqf 3713   := by decide +kernel
private theorem c3713_range : LeafRange 3713  := by decide +kernel
private theorem c3713_ell   : LeafEll 3713    := by decide +kernel
private theorem c3713_nsq   : NSqChkSq 3713   := by decide +kernel
private theorem c3713_har   : HArithChkSq 3713 := by decide +kernel
private theorem c3713_r     : LeafR 3713      := by decide +kernel
private theorem c3713_e'    : LeafE' 3713     := by decide +kernel
private theorem c3713_f1    : LeafF1 3713     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3713_s2    : S2ChkSq 3713    := by decide +kernel
private theorem c3713_s3    : S3ChkSq 3713    := by decide +kernel
private theorem c3713_iso   : LeafIso 3713    := by decide +kernel
private theorem c3713_nof2  : NoF2ChkSq 3713  := by decide +kernel
private theorem c3713_nof3  : NoF3ChkSq 3713  := by decide +kernel
private theorem c3713_nof4z : NoF4zChkSq 3713 := by decide +kernel
theorem C'_3713 : C' 3713 :=
  ⟨c3713_sqf, c3713_range, c3713_ell, leafNSq_of_sq c3713_nsq, leafHAr_of_sq c3713_har,
   c3713_r, c3713_e', c3713_f1, leafS2_of_sq c3713_s2, leafS3_of_sq c3713_s3,
   c3713_iso, leafR8_of_sq c3713_nof2 c3713_nof3 c3713_nof4z⟩
theorem not_tile'_3713 (D : CongruentDissection 3713) : False :=
  not_tile_of_conditions' 3713 C'_3713 D

private theorem c3714_sqf   : LeafSqf 3714   := by decide +kernel
private theorem c3714_range : LeafRange 3714  := by decide +kernel
private theorem c3714_ell   : LeafEll 3714    := by decide +kernel
private theorem c3714_nsq   : NSqChkSq 3714   := by decide +kernel
private theorem c3714_har   : HArithChkSq 3714 := by decide +kernel
private theorem c3714_r     : LeafR 3714      := by decide +kernel
private theorem c3714_e'    : LeafE' 3714     := by decide +kernel
private theorem c3714_f1    : LeafF1 3714     := Or.inl (by decide)
private theorem c3714_s2    : S2ChkSq 3714    := by decide +kernel
private theorem c3714_s3    : S3ChkSq 3714    := by decide +kernel
private theorem c3714_iso   : LeafIso 3714    := by decide +kernel
private theorem c3714_nof2  : NoF2ChkSq 3714  := by decide +kernel
private theorem c3714_nof3  : NoF3ChkSq 3714  := by decide +kernel
private theorem c3714_nof4z : NoF4zChkSq 3714 := by decide +kernel
theorem C'_3714 : C' 3714 :=
  ⟨c3714_sqf, c3714_range, c3714_ell, leafNSq_of_sq c3714_nsq, leafHAr_of_sq c3714_har,
   c3714_r, c3714_e', c3714_f1, leafS2_of_sq c3714_s2, leafS3_of_sq c3714_s3,
   c3714_iso, leafR8_of_sq c3714_nof2 c3714_nof3 c3714_nof4z⟩
theorem not_tile'_3714 (D : CongruentDissection 3714) : False :=
  not_tile_of_conditions' 3714 C'_3714 D

private theorem c3715_sqf   : LeafSqf 3715   := by decide +kernel
private theorem c3715_range : LeafRange 3715  := by decide +kernel
private theorem c3715_ell   : LeafEll 3715    := by decide +kernel
private theorem c3715_nsq   : NSqChkSq 3715   := by decide +kernel
private theorem c3715_har   : HArithChkSq 3715 := by decide +kernel
private theorem c3715_r     : LeafR 3715      := by decide +kernel
private theorem c3715_e'    : LeafE' 3715     := by decide +kernel
private theorem c3715_f1    : LeafF1 3715     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3715_s2    : S2ChkSq 3715    := by decide +kernel
private theorem c3715_s3    : S3ChkSq 3715    := by decide +kernel
private theorem c3715_iso   : LeafIso 3715    := by decide +kernel
private theorem c3715_nof2  : NoF2ChkSq 3715  := by decide +kernel
private theorem c3715_nof3  : NoF3ChkSq 3715  := by decide +kernel
private theorem c3715_nof4z : NoF4zChkSq 3715 := by decide +kernel
theorem C'_3715 : C' 3715 :=
  ⟨c3715_sqf, c3715_range, c3715_ell, leafNSq_of_sq c3715_nsq, leafHAr_of_sq c3715_har,
   c3715_r, c3715_e', c3715_f1, leafS2_of_sq c3715_s2, leafS3_of_sq c3715_s3,
   c3715_iso, leafR8_of_sq c3715_nof2 c3715_nof3 c3715_nof4z⟩
theorem not_tile'_3715 (D : CongruentDissection 3715) : False :=
  not_tile_of_conditions' 3715 C'_3715 D

private theorem c3719_sqf   : LeafSqf 3719   := by decide +kernel
private theorem c3719_range : LeafRange 3719  := by decide +kernel
private theorem c3719_ell   : LeafEll 3719    := by decide +kernel
private theorem c3719_nsq   : NSqChkSq 3719   := by decide +kernel
private theorem c3719_har   : HArithChkSq 3719 := by decide +kernel
private theorem c3719_r     : LeafR 3719      := by decide +kernel
private theorem c3719_e'    : LeafE' 3719     := by decide +kernel
private theorem c3719_f1    : LeafF1 3719     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3719_s2    : S2ChkSq 3719    := by decide +kernel
private theorem c3719_s3    : S3ChkSq 3719    := by decide +kernel
private theorem c3719_iso   : LeafIso 3719    := by decide +kernel
private theorem c3719_nof2  : NoF2ChkSq 3719  := by decide +kernel
private theorem c3719_nof3  : NoF3ChkSq 3719  := by decide +kernel
private theorem c3719_nof4z : NoF4zChkSq 3719 := by decide +kernel
theorem C'_3719 : C' 3719 :=
  ⟨c3719_sqf, c3719_range, c3719_ell, leafNSq_of_sq c3719_nsq, leafHAr_of_sq c3719_har,
   c3719_r, c3719_e', c3719_f1, leafS2_of_sq c3719_s2, leafS3_of_sq c3719_s3,
   c3719_iso, leafR8_of_sq c3719_nof2 c3719_nof3 c3719_nof4z⟩
theorem not_tile'_3719 (D : CongruentDissection 3719) : False :=
  not_tile_of_conditions' 3719 C'_3719 D

end Erdos634.Draft.AllN2

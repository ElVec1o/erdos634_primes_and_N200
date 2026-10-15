/- AllN2Check278: N = 4883, 4886, 4890, 4891, 4894
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4883_sqf   : LeafSqf 4883   := by decide +kernel
private theorem c4883_range : LeafRange 4883  := by decide +kernel
private theorem c4883_ell   : LeafEll 4883    := by decide +kernel
private theorem c4883_nsq   : NSqChkSq 4883   := by decide +kernel
private theorem c4883_har   : HArithChkSq 4883 := by decide +kernel
private theorem c4883_r     : LeafR 4883      := by decide +kernel
private theorem c4883_e'    : LeafE' 4883     := by decide +kernel
private theorem c4883_f1    : LeafF1 4883     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4883_s2    : S2ChkSq 4883    := by decide +kernel
private theorem c4883_s3    : S3ChkSq 4883    := by decide +kernel
private theorem c4883_iso   : LeafIso 4883    := by decide +kernel
private theorem c4883_nof2  : NoF2ChkSq 4883  := by decide +kernel
private theorem c4883_nof3  : NoF3ChkSq 4883  := by decide +kernel
private theorem c4883_nof4z : NoF4zChkSq 4883 := by decide +kernel
theorem C'_4883 : C' 4883 :=
  ⟨c4883_sqf, c4883_range, c4883_ell, leafNSq_of_sq c4883_nsq, leafHAr_of_sq c4883_har,
   c4883_r, c4883_e', c4883_f1, leafS2_of_sq c4883_s2, leafS3_of_sq c4883_s3,
   c4883_iso, leafR8_of_sq c4883_nof2 c4883_nof3 c4883_nof4z⟩
theorem not_tile'_4883 (D : CongruentDissection 4883) : False :=
  not_tile_of_conditions' 4883 C'_4883 D

private theorem c4886_sqf   : LeafSqf 4886   := by decide +kernel
private theorem c4886_range : LeafRange 4886  := by decide +kernel
private theorem c4886_ell   : LeafEll 4886    := by decide +kernel
private theorem c4886_nsq   : NSqChkSq 4886   := by decide +kernel
private theorem c4886_har   : HArithChkSq 4886 := by decide +kernel
private theorem c4886_r     : LeafR 4886      := by decide +kernel
private theorem c4886_e'    : LeafE' 4886     := by decide +kernel
private theorem c4886_f1    : LeafF1 4886     := Or.inl (by decide)
private theorem c4886_s2    : S2ChkSq 4886    := by decide +kernel
private theorem c4886_s3    : S3ChkSq 4886    := by decide +kernel
private theorem c4886_iso   : LeafIso 4886    := by decide +kernel
private theorem c4886_nof2  : NoF2ChkSq 4886  := by decide +kernel
private theorem c4886_nof3  : NoF3ChkSq 4886  := by decide +kernel
private theorem c4886_nof4z : NoF4zChkSq 4886 := by decide +kernel
theorem C'_4886 : C' 4886 :=
  ⟨c4886_sqf, c4886_range, c4886_ell, leafNSq_of_sq c4886_nsq, leafHAr_of_sq c4886_har,
   c4886_r, c4886_e', c4886_f1, leafS2_of_sq c4886_s2, leafS3_of_sq c4886_s3,
   c4886_iso, leafR8_of_sq c4886_nof2 c4886_nof3 c4886_nof4z⟩
theorem not_tile'_4886 (D : CongruentDissection 4886) : False :=
  not_tile_of_conditions' 4886 C'_4886 D

private theorem c4890_sqf   : LeafSqf 4890   := by decide +kernel
private theorem c4890_range : LeafRange 4890  := by decide +kernel
private theorem c4890_ell   : LeafEll 4890    := by decide +kernel
private theorem c4890_nsq   : NSqChkSq 4890   := by decide +kernel
private theorem c4890_har   : HArithChkSq 4890 := by decide +kernel
private theorem c4890_r     : LeafR 4890      := by decide +kernel
private theorem c4890_e'    : LeafE' 4890     := by decide +kernel
private theorem c4890_f1    : LeafF1 4890     := Or.inl (by decide)
private theorem c4890_s2    : S2ChkSq 4890    := by decide +kernel
private theorem c4890_s3    : S3ChkSq 4890    := by decide +kernel
private theorem c4890_iso   : LeafIso 4890    := by decide +kernel
private theorem c4890_nof2  : NoF2ChkSq 4890  := by decide +kernel
private theorem c4890_nof3  : NoF3ChkSq 4890  := by decide +kernel
private theorem c4890_nof4z : NoF4zChkSq 4890 := by decide +kernel
theorem C'_4890 : C' 4890 :=
  ⟨c4890_sqf, c4890_range, c4890_ell, leafNSq_of_sq c4890_nsq, leafHAr_of_sq c4890_har,
   c4890_r, c4890_e', c4890_f1, leafS2_of_sq c4890_s2, leafS3_of_sq c4890_s3,
   c4890_iso, leafR8_of_sq c4890_nof2 c4890_nof3 c4890_nof4z⟩
theorem not_tile'_4890 (D : CongruentDissection 4890) : False :=
  not_tile_of_conditions' 4890 C'_4890 D

private theorem c4891_sqf   : LeafSqf 4891   := by decide +kernel
private theorem c4891_range : LeafRange 4891  := by decide +kernel
private theorem c4891_ell   : LeafEll 4891    := by decide +kernel
private theorem c4891_nsq   : NSqChkSq 4891   := by decide +kernel
private theorem c4891_har   : HArithChkSq 4891 := by decide +kernel
private theorem c4891_r     : LeafR 4891      := by decide +kernel
private theorem c4891_e'    : LeafE' 4891     := by decide +kernel
private theorem c4891_f1    : LeafF1 4891     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4891_s2    : S2ChkSq 4891    := by decide +kernel
private theorem c4891_s3    : S3ChkSq 4891    := by decide +kernel
private theorem c4891_iso   : LeafIso 4891    := by decide +kernel
private theorem c4891_nof2  : NoF2ChkSq 4891  := by decide +kernel
private theorem c4891_nof3  : NoF3ChkSq 4891  := by decide +kernel
private theorem c4891_nof4z : NoF4zChkSq 4891 := by decide +kernel
theorem C'_4891 : C' 4891 :=
  ⟨c4891_sqf, c4891_range, c4891_ell, leafNSq_of_sq c4891_nsq, leafHAr_of_sq c4891_har,
   c4891_r, c4891_e', c4891_f1, leafS2_of_sq c4891_s2, leafS3_of_sq c4891_s3,
   c4891_iso, leafR8_of_sq c4891_nof2 c4891_nof3 c4891_nof4z⟩
theorem not_tile'_4891 (D : CongruentDissection 4891) : False :=
  not_tile_of_conditions' 4891 C'_4891 D

private theorem c4894_sqf   : LeafSqf 4894   := by decide +kernel
private theorem c4894_range : LeafRange 4894  := by decide +kernel
private theorem c4894_ell   : LeafEll 4894    := by decide +kernel
private theorem c4894_nsq   : NSqChkSq 4894   := by decide +kernel
private theorem c4894_har   : HArithChkSq 4894 := by decide +kernel
private theorem c4894_r     : LeafR 4894      := by decide +kernel
private theorem c4894_e'    : LeafE' 4894     := by decide +kernel
private theorem c4894_f1    : LeafF1 4894     := Or.inl (by decide)
private theorem c4894_s2    : S2ChkSq 4894    := by decide +kernel
private theorem c4894_s3    : S3ChkSq 4894    := by decide +kernel
private theorem c4894_iso   : LeafIso 4894    := by decide +kernel
private theorem c4894_nof2  : NoF2ChkSq 4894  := by decide +kernel
private theorem c4894_nof3  : NoF3ChkSq 4894  := by decide +kernel
private theorem c4894_nof4z : NoF4zChkSq 4894 := by decide +kernel
theorem C'_4894 : C' 4894 :=
  ⟨c4894_sqf, c4894_range, c4894_ell, leafNSq_of_sq c4894_nsq, leafHAr_of_sq c4894_har,
   c4894_r, c4894_e', c4894_f1, leafS2_of_sq c4894_s2, leafS3_of_sq c4894_s3,
   c4894_iso, leafR8_of_sq c4894_nof2 c4894_nof3 c4894_nof4z⟩
theorem not_tile'_4894 (D : CongruentDissection 4894) : False :=
  not_tile_of_conditions' 4894 C'_4894 D

end Erdos634.Draft.AllN2

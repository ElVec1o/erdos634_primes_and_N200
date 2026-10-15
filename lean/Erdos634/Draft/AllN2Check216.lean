/- AllN2Check216: N = 4117, 4118, 4119, 4123, 4126
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4117_sqf   : LeafSqf 4117   := by decide +kernel
private theorem c4117_range : LeafRange 4117  := by decide +kernel
private theorem c4117_ell   : LeafEll 4117    := by decide +kernel
private theorem c4117_nsq   : NSqChkSq 4117   := by decide +kernel
private theorem c4117_har   : HArithChkSq 4117 := by decide +kernel
private theorem c4117_r     : LeafR 4117      := by decide +kernel
private theorem c4117_e'    : LeafE' 4117     := by decide +kernel
private theorem c4117_f1    : LeafF1 4117     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4117_s2    : S2ChkSq 4117    := by decide +kernel
private theorem c4117_s3    : S3ChkSq 4117    := by decide +kernel
private theorem c4117_iso   : LeafIso 4117    := by decide +kernel
private theorem c4117_nof2  : NoF2ChkSq 4117  := by decide +kernel
private theorem c4117_nof3  : NoF3ChkSq 4117  := by decide +kernel
private theorem c4117_nof4z : NoF4zChkSq 4117 := by decide +kernel
theorem C'_4117 : C' 4117 :=
  ⟨c4117_sqf, c4117_range, c4117_ell, leafNSq_of_sq c4117_nsq, leafHAr_of_sq c4117_har,
   c4117_r, c4117_e', c4117_f1, leafS2_of_sq c4117_s2, leafS3_of_sq c4117_s3,
   c4117_iso, leafR8_of_sq c4117_nof2 c4117_nof3 c4117_nof4z⟩
theorem not_tile'_4117 (D : CongruentDissection 4117) : False :=
  not_tile_of_conditions' 4117 C'_4117 D

private theorem c4118_sqf   : LeafSqf 4118   := by decide +kernel
private theorem c4118_range : LeafRange 4118  := by decide +kernel
private theorem c4118_ell   : LeafEll 4118    := by decide +kernel
private theorem c4118_nsq   : NSqChkSq 4118   := by decide +kernel
private theorem c4118_har   : HArithChkSq 4118 := by decide +kernel
private theorem c4118_r     : LeafR 4118      := by decide +kernel
private theorem c4118_e'    : LeafE' 4118     := by decide +kernel
private theorem c4118_f1    : LeafF1 4118     := Or.inl (by decide)
private theorem c4118_s2    : S2ChkSq 4118    := by decide +kernel
private theorem c4118_s3    : S3ChkSq 4118    := by decide +kernel
private theorem c4118_iso   : LeafIso 4118    := by decide +kernel
private theorem c4118_nof2  : NoF2ChkSq 4118  := by decide +kernel
private theorem c4118_nof3  : NoF3ChkSq 4118  := by decide +kernel
private theorem c4118_nof4z : NoF4zChkSq 4118 := by decide +kernel
theorem C'_4118 : C' 4118 :=
  ⟨c4118_sqf, c4118_range, c4118_ell, leafNSq_of_sq c4118_nsq, leafHAr_of_sq c4118_har,
   c4118_r, c4118_e', c4118_f1, leafS2_of_sq c4118_s2, leafS3_of_sq c4118_s3,
   c4118_iso, leafR8_of_sq c4118_nof2 c4118_nof3 c4118_nof4z⟩
theorem not_tile'_4118 (D : CongruentDissection 4118) : False :=
  not_tile_of_conditions' 4118 C'_4118 D

private theorem c4119_sqf   : LeafSqf 4119   := by decide +kernel
private theorem c4119_range : LeafRange 4119  := by decide +kernel
private theorem c4119_ell   : LeafEll 4119    := by decide +kernel
private theorem c4119_nsq   : NSqChkSq 4119   := by decide +kernel
private theorem c4119_har   : HArithChkSq 4119 := by decide +kernel
private theorem c4119_r     : LeafR 4119      := by decide +kernel
private theorem c4119_e'    : LeafE' 4119     := by decide +kernel
private theorem c4119_f1    : LeafF1 4119     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4119_s2    : S2ChkSq 4119    := by decide +kernel
private theorem c4119_s3    : S3ChkSq 4119    := by decide +kernel
private theorem c4119_iso   : LeafIso 4119    := by decide +kernel
private theorem c4119_nof2  : NoF2ChkSq 4119  := by decide +kernel
private theorem c4119_nof3  : NoF3ChkSq 4119  := by decide +kernel
private theorem c4119_nof4z : NoF4zChkSq 4119 := by decide +kernel
theorem C'_4119 : C' 4119 :=
  ⟨c4119_sqf, c4119_range, c4119_ell, leafNSq_of_sq c4119_nsq, leafHAr_of_sq c4119_har,
   c4119_r, c4119_e', c4119_f1, leafS2_of_sq c4119_s2, leafS3_of_sq c4119_s3,
   c4119_iso, leafR8_of_sq c4119_nof2 c4119_nof3 c4119_nof4z⟩
theorem not_tile'_4119 (D : CongruentDissection 4119) : False :=
  not_tile_of_conditions' 4119 C'_4119 D

private theorem c4123_sqf   : LeafSqf 4123   := by decide +kernel
private theorem c4123_range : LeafRange 4123  := by decide +kernel
private theorem c4123_ell   : LeafEll 4123    := by decide +kernel
private theorem c4123_nsq   : NSqChkSq 4123   := by decide +kernel
private theorem c4123_har   : HArithChkSq 4123 := by decide +kernel
private theorem c4123_r     : LeafR 4123      := by decide +kernel
private theorem c4123_e'    : LeafE' 4123     := by decide +kernel
private theorem c4123_f1    : LeafF1 4123     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4123_s2    : S2ChkSq 4123    := by decide +kernel
private theorem c4123_s3    : S3ChkSq 4123    := by decide +kernel
private theorem c4123_iso   : LeafIso 4123    := by decide +kernel
private theorem c4123_nof2  : NoF2ChkSq 4123  := by decide +kernel
private theorem c4123_nof3  : NoF3ChkSq 4123  := by decide +kernel
private theorem c4123_nof4z : NoF4zChkSq 4123 := by decide +kernel
theorem C'_4123 : C' 4123 :=
  ⟨c4123_sqf, c4123_range, c4123_ell, leafNSq_of_sq c4123_nsq, leafHAr_of_sq c4123_har,
   c4123_r, c4123_e', c4123_f1, leafS2_of_sq c4123_s2, leafS3_of_sq c4123_s3,
   c4123_iso, leafR8_of_sq c4123_nof2 c4123_nof3 c4123_nof4z⟩
theorem not_tile'_4123 (D : CongruentDissection 4123) : False :=
  not_tile_of_conditions' 4123 C'_4123 D

private theorem c4126_sqf   : LeafSqf 4126   := by decide +kernel
private theorem c4126_range : LeafRange 4126  := by decide +kernel
private theorem c4126_ell   : LeafEll 4126    := by decide +kernel
private theorem c4126_nsq   : NSqChkSq 4126   := by decide +kernel
private theorem c4126_har   : HArithChkSq 4126 := by decide +kernel
private theorem c4126_r     : LeafR 4126      := by decide +kernel
private theorem c4126_e'    : LeafE' 4126     := by decide +kernel
private theorem c4126_f1    : LeafF1 4126     := Or.inl (by decide)
private theorem c4126_s2    : S2ChkSq 4126    := by decide +kernel
private theorem c4126_s3    : S3ChkSq 4126    := by decide +kernel
private theorem c4126_iso   : LeafIso 4126    := by decide +kernel
private theorem c4126_nof2  : NoF2ChkSq 4126  := by decide +kernel
private theorem c4126_nof3  : NoF3ChkSq 4126  := by decide +kernel
private theorem c4126_nof4z : NoF4zChkSq 4126 := by decide +kernel
theorem C'_4126 : C' 4126 :=
  ⟨c4126_sqf, c4126_range, c4126_ell, leafNSq_of_sq c4126_nsq, leafHAr_of_sq c4126_har,
   c4126_r, c4126_e', c4126_f1, leafS2_of_sq c4126_s2, leafS3_of_sq c4126_s3,
   c4126_iso, leafR8_of_sq c4126_nof2 c4126_nof3 c4126_nof4z⟩
theorem not_tile'_4126 (D : CongruentDissection 4126) : False :=
  not_tile_of_conditions' 4126 C'_4126 D

end Erdos634.Draft.AllN2

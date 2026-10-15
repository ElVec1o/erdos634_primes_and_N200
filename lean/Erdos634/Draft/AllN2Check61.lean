/- AllN2Check61: N = 2119, 2123, 2126, 2127, 2130
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2119_sqf   : LeafSqf 2119   := by decide +kernel
private theorem c2119_range : LeafRange 2119  := by decide +kernel
private theorem c2119_ell   : LeafEll 2119    := by decide +kernel
private theorem c2119_nsq   : NSqChkSq 2119   := by decide +kernel
private theorem c2119_har   : HArithChkSq 2119 := by decide +kernel
private theorem c2119_r     : LeafR 2119      := by decide +kernel
private theorem c2119_e'    : LeafE' 2119     := by decide +kernel
private theorem c2119_f1    : LeafF1 2119     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2119_s2    : S2ChkSq 2119    := by decide +kernel
private theorem c2119_s3    : S3ChkSq 2119    := by decide +kernel
private theorem c2119_iso   : LeafIso 2119    := by decide +kernel
private theorem c2119_nof2  : NoF2ChkSq 2119  := by decide +kernel
private theorem c2119_nof3  : NoF3ChkSq 2119  := by decide +kernel
private theorem c2119_nof4z : NoF4zChkSq 2119 := by decide +kernel
theorem C'_2119 : C' 2119 :=
  ⟨c2119_sqf, c2119_range, c2119_ell, leafNSq_of_sq c2119_nsq, leafHAr_of_sq c2119_har,
   c2119_r, c2119_e', c2119_f1, leafS2_of_sq c2119_s2, leafS3_of_sq c2119_s3,
   c2119_iso, leafR8_of_sq c2119_nof2 c2119_nof3 c2119_nof4z⟩
theorem not_tile'_2119 (D : CongruentDissection 2119) : False :=
  not_tile_of_conditions' 2119 C'_2119 D

private theorem c2123_sqf   : LeafSqf 2123   := by decide +kernel
private theorem c2123_range : LeafRange 2123  := by decide +kernel
private theorem c2123_ell   : LeafEll 2123    := by decide +kernel
private theorem c2123_nsq   : NSqChkSq 2123   := by decide +kernel
private theorem c2123_har   : HArithChkSq 2123 := by decide +kernel
private theorem c2123_r     : LeafR 2123      := by decide +kernel
private theorem c2123_e'    : LeafE' 2123     := by decide +kernel
private theorem c2123_f1    : LeafF1 2123     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2123_s2    : S2ChkSq 2123    := by decide +kernel
private theorem c2123_s3    : S3ChkSq 2123    := by decide +kernel
private theorem c2123_iso   : LeafIso 2123    := by decide +kernel
private theorem c2123_nof2  : NoF2ChkSq 2123  := by decide +kernel
private theorem c2123_nof3  : NoF3ChkSq 2123  := by decide +kernel
private theorem c2123_nof4z : NoF4zChkSq 2123 := by decide +kernel
theorem C'_2123 : C' 2123 :=
  ⟨c2123_sqf, c2123_range, c2123_ell, leafNSq_of_sq c2123_nsq, leafHAr_of_sq c2123_har,
   c2123_r, c2123_e', c2123_f1, leafS2_of_sq c2123_s2, leafS3_of_sq c2123_s3,
   c2123_iso, leafR8_of_sq c2123_nof2 c2123_nof3 c2123_nof4z⟩
theorem not_tile'_2123 (D : CongruentDissection 2123) : False :=
  not_tile_of_conditions' 2123 C'_2123 D

private theorem c2126_sqf   : LeafSqf 2126   := by decide +kernel
private theorem c2126_range : LeafRange 2126  := by decide +kernel
private theorem c2126_ell   : LeafEll 2126    := by decide +kernel
private theorem c2126_nsq   : NSqChkSq 2126   := by decide +kernel
private theorem c2126_har   : HArithChkSq 2126 := by decide +kernel
private theorem c2126_r     : LeafR 2126      := by decide +kernel
private theorem c2126_e'    : LeafE' 2126     := by decide +kernel
private theorem c2126_f1    : LeafF1 2126     := Or.inl (by decide)
private theorem c2126_s2    : S2ChkSq 2126    := by decide +kernel
private theorem c2126_s3    : S3ChkSq 2126    := by decide +kernel
private theorem c2126_iso   : LeafIso 2126    := by decide +kernel
private theorem c2126_nof2  : NoF2ChkSq 2126  := by decide +kernel
private theorem c2126_nof3  : NoF3ChkSq 2126  := by decide +kernel
private theorem c2126_nof4z : NoF4zChkSq 2126 := by decide +kernel
theorem C'_2126 : C' 2126 :=
  ⟨c2126_sqf, c2126_range, c2126_ell, leafNSq_of_sq c2126_nsq, leafHAr_of_sq c2126_har,
   c2126_r, c2126_e', c2126_f1, leafS2_of_sq c2126_s2, leafS3_of_sq c2126_s3,
   c2126_iso, leafR8_of_sq c2126_nof2 c2126_nof3 c2126_nof4z⟩
theorem not_tile'_2126 (D : CongruentDissection 2126) : False :=
  not_tile_of_conditions' 2126 C'_2126 D

private theorem c2127_sqf   : LeafSqf 2127   := by decide +kernel
private theorem c2127_range : LeafRange 2127  := by decide +kernel
private theorem c2127_ell   : LeafEll 2127    := by decide +kernel
private theorem c2127_nsq   : NSqChkSq 2127   := by decide +kernel
private theorem c2127_har   : HArithChkSq 2127 := by decide +kernel
private theorem c2127_r     : LeafR 2127      := by decide +kernel
private theorem c2127_e'    : LeafE' 2127     := by decide +kernel
private theorem c2127_f1    : LeafF1 2127     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2127_s2    : S2ChkSq 2127    := by decide +kernel
private theorem c2127_s3    : S3ChkSq 2127    := by decide +kernel
private theorem c2127_iso   : LeafIso 2127    := by decide +kernel
private theorem c2127_nof2  : NoF2ChkSq 2127  := by decide +kernel
private theorem c2127_nof3  : NoF3ChkSq 2127  := by decide +kernel
private theorem c2127_nof4z : NoF4zChkSq 2127 := by decide +kernel
theorem C'_2127 : C' 2127 :=
  ⟨c2127_sqf, c2127_range, c2127_ell, leafNSq_of_sq c2127_nsq, leafHAr_of_sq c2127_har,
   c2127_r, c2127_e', c2127_f1, leafS2_of_sq c2127_s2, leafS3_of_sq c2127_s3,
   c2127_iso, leafR8_of_sq c2127_nof2 c2127_nof3 c2127_nof4z⟩
theorem not_tile'_2127 (D : CongruentDissection 2127) : False :=
  not_tile_of_conditions' 2127 C'_2127 D

private theorem c2130_sqf   : LeafSqf 2130   := by decide +kernel
private theorem c2130_range : LeafRange 2130  := by decide +kernel
private theorem c2130_ell   : LeafEll 2130    := by decide +kernel
private theorem c2130_nsq   : NSqChkSq 2130   := by decide +kernel
private theorem c2130_har   : HArithChkSq 2130 := by decide +kernel
private theorem c2130_r     : LeafR 2130      := by decide +kernel
private theorem c2130_e'    : LeafE' 2130     := by decide +kernel
private theorem c2130_f1    : LeafF1 2130     := Or.inl (by decide)
private theorem c2130_s2    : S2ChkSq 2130    := by decide +kernel
private theorem c2130_s3    : S3ChkSq 2130    := by decide +kernel
private theorem c2130_iso   : LeafIso 2130    := by decide +kernel
private theorem c2130_nof2  : NoF2ChkSq 2130  := by decide +kernel
private theorem c2130_nof3  : NoF3ChkSq 2130  := by decide +kernel
private theorem c2130_nof4z : NoF4zChkSq 2130 := by decide +kernel
theorem C'_2130 : C' 2130 :=
  ⟨c2130_sqf, c2130_range, c2130_ell, leafNSq_of_sq c2130_nsq, leafHAr_of_sq c2130_har,
   c2130_r, c2130_e', c2130_f1, leafS2_of_sq c2130_s2, leafS3_of_sq c2130_s3,
   c2130_iso, leafR8_of_sq c2130_nof2 c2130_nof3 c2130_nof4z⟩
theorem not_tile'_2130 (D : CongruentDissection 2130) : False :=
  not_tile_of_conditions' 2130 C'_2130 D

end Erdos634.Draft.AllN2

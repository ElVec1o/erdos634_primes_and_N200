/- AllN2Check217: N = 4127, 4130, 4134, 4135, 4139
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4127_sqf   : LeafSqf 4127   := by decide +kernel
private theorem c4127_range : LeafRange 4127  := by decide +kernel
private theorem c4127_ell   : LeafEll 4127    := by decide +kernel
private theorem c4127_nsq   : NSqChkSq 4127   := by decide +kernel
private theorem c4127_har   : HArithChkSq 4127 := by decide +kernel
private theorem c4127_r     : LeafR 4127      := by decide +kernel
private theorem c4127_e'    : LeafE' 4127     := by decide +kernel
private theorem c4127_f1    : LeafF1 4127     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4127_s2    : S2ChkSq 4127    := by decide +kernel
private theorem c4127_s3    : S3ChkSq 4127    := by decide +kernel
private theorem c4127_iso   : LeafIso 4127    := by decide +kernel
private theorem c4127_nof2  : NoF2ChkSq 4127  := by decide +kernel
private theorem c4127_nof3  : NoF3ChkSq 4127  := by decide +kernel
private theorem c4127_nof4z : NoF4zChkSq 4127 := by decide +kernel
theorem C'_4127 : C' 4127 :=
  ⟨c4127_sqf, c4127_range, c4127_ell, leafNSq_of_sq c4127_nsq, leafHAr_of_sq c4127_har,
   c4127_r, c4127_e', c4127_f1, leafS2_of_sq c4127_s2, leafS3_of_sq c4127_s3,
   c4127_iso, leafR8_of_sq c4127_nof2 c4127_nof3 c4127_nof4z⟩
theorem not_tile'_4127 (D : CongruentDissection 4127) : False :=
  not_tile_of_conditions' 4127 C'_4127 D

private theorem c4130_sqf   : LeafSqf 4130   := by decide +kernel
private theorem c4130_range : LeafRange 4130  := by decide +kernel
private theorem c4130_ell   : LeafEll 4130    := by decide +kernel
private theorem c4130_nsq   : NSqChkSq 4130   := by decide +kernel
private theorem c4130_har   : HArithChkSq 4130 := by decide +kernel
private theorem c4130_r     : LeafR 4130      := by decide +kernel
private theorem c4130_e'    : LeafE' 4130     := by decide +kernel
private theorem c4130_f1    : LeafF1 4130     := Or.inl (by decide)
private theorem c4130_s2    : S2ChkSq 4130    := by decide +kernel
private theorem c4130_s3    : S3ChkSq 4130    := by decide +kernel
private theorem c4130_iso   : LeafIso 4130    := by decide +kernel
private theorem c4130_nof2  : NoF2ChkSq 4130  := by decide +kernel
private theorem c4130_nof3  : NoF3ChkSq 4130  := by decide +kernel
private theorem c4130_nof4z : NoF4zChkSq 4130 := by decide +kernel
theorem C'_4130 : C' 4130 :=
  ⟨c4130_sqf, c4130_range, c4130_ell, leafNSq_of_sq c4130_nsq, leafHAr_of_sq c4130_har,
   c4130_r, c4130_e', c4130_f1, leafS2_of_sq c4130_s2, leafS3_of_sq c4130_s3,
   c4130_iso, leafR8_of_sq c4130_nof2 c4130_nof3 c4130_nof4z⟩
theorem not_tile'_4130 (D : CongruentDissection 4130) : False :=
  not_tile_of_conditions' 4130 C'_4130 D

private theorem c4134_sqf   : LeafSqf 4134   := by decide +kernel
private theorem c4134_range : LeafRange 4134  := by decide +kernel
private theorem c4134_ell   : LeafEll 4134    := by decide +kernel
private theorem c4134_nsq   : NSqChkSq 4134   := by decide +kernel
private theorem c4134_har   : HArithChkSq 4134 := by decide +kernel
private theorem c4134_r     : LeafR 4134      := by decide +kernel
private theorem c4134_e'    : LeafE' 4134     := by decide +kernel
private theorem c4134_f1    : LeafF1 4134     := Or.inl (by decide)
private theorem c4134_s2    : S2ChkSq 4134    := by decide +kernel
private theorem c4134_s3    : S3ChkSq 4134    := by decide +kernel
private theorem c4134_iso   : LeafIso 4134    := by decide +kernel
private theorem c4134_nof2  : NoF2ChkSq 4134  := by decide +kernel
private theorem c4134_nof3  : NoF3ChkSq 4134  := by decide +kernel
private theorem c4134_nof4z : NoF4zChkSq 4134 := by decide +kernel
theorem C'_4134 : C' 4134 :=
  ⟨c4134_sqf, c4134_range, c4134_ell, leafNSq_of_sq c4134_nsq, leafHAr_of_sq c4134_har,
   c4134_r, c4134_e', c4134_f1, leafS2_of_sq c4134_s2, leafS3_of_sq c4134_s3,
   c4134_iso, leafR8_of_sq c4134_nof2 c4134_nof3 c4134_nof4z⟩
theorem not_tile'_4134 (D : CongruentDissection 4134) : False :=
  not_tile_of_conditions' 4134 C'_4134 D

private theorem c4135_sqf   : LeafSqf 4135   := by decide +kernel
private theorem c4135_range : LeafRange 4135  := by decide +kernel
private theorem c4135_ell   : LeafEll 4135    := by decide +kernel
private theorem c4135_nsq   : NSqChkSq 4135   := by decide +kernel
private theorem c4135_har   : HArithChkSq 4135 := by decide +kernel
private theorem c4135_r     : LeafR 4135      := by decide +kernel
private theorem c4135_e'    : LeafE' 4135     := by decide +kernel
private theorem c4135_f1    : LeafF1 4135     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4135_s2    : S2ChkSq 4135    := by decide +kernel
private theorem c4135_s3    : S3ChkSq 4135    := by decide +kernel
private theorem c4135_iso   : LeafIso 4135    := by decide +kernel
private theorem c4135_nof2  : NoF2ChkSq 4135  := by decide +kernel
private theorem c4135_nof3  : NoF3ChkSq 4135  := by decide +kernel
private theorem c4135_nof4z : NoF4zChkSq 4135 := by decide +kernel
theorem C'_4135 : C' 4135 :=
  ⟨c4135_sqf, c4135_range, c4135_ell, leafNSq_of_sq c4135_nsq, leafHAr_of_sq c4135_har,
   c4135_r, c4135_e', c4135_f1, leafS2_of_sq c4135_s2, leafS3_of_sq c4135_s3,
   c4135_iso, leafR8_of_sq c4135_nof2 c4135_nof3 c4135_nof4z⟩
theorem not_tile'_4135 (D : CongruentDissection 4135) : False :=
  not_tile_of_conditions' 4135 C'_4135 D

private theorem c4139_sqf   : LeafSqf 4139   := by decide +kernel
private theorem c4139_range : LeafRange 4139  := by decide +kernel
private theorem c4139_ell   : LeafEll 4139    := by decide +kernel
private theorem c4139_nsq   : NSqChkSq 4139   := by decide +kernel
private theorem c4139_har   : HArithChkSq 4139 := by decide +kernel
private theorem c4139_r     : LeafR 4139      := by decide +kernel
private theorem c4139_e'    : LeafE' 4139     := by decide +kernel
private theorem c4139_f1    : LeafF1 4139     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4139_s2    : S2ChkSq 4139    := by decide +kernel
private theorem c4139_s3    : S3ChkSq 4139    := by decide +kernel
private theorem c4139_iso   : LeafIso 4139    := by decide +kernel
private theorem c4139_nof2  : NoF2ChkSq 4139  := by decide +kernel
private theorem c4139_nof3  : NoF3ChkSq 4139  := by decide +kernel
private theorem c4139_nof4z : NoF4zChkSq 4139 := by decide +kernel
theorem C'_4139 : C' 4139 :=
  ⟨c4139_sqf, c4139_range, c4139_ell, leafNSq_of_sq c4139_nsq, leafHAr_of_sq c4139_har,
   c4139_r, c4139_e', c4139_f1, leafS2_of_sq c4139_s2, leafS3_of_sq c4139_s3,
   c4139_iso, leafR8_of_sq c4139_nof2 c4139_nof3 c4139_nof4z⟩
theorem not_tile'_4139 (D : CongruentDissection 4139) : False :=
  not_tile_of_conditions' 4139 C'_4139 D

end Erdos634.Draft.AllN2

/- AllN2Check141: N = 3127, 3131, 3134, 3138, 3139
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3127_sqf   : LeafSqf 3127   := by decide +kernel
private theorem c3127_range : LeafRange 3127  := by decide +kernel
private theorem c3127_ell   : LeafEll 3127    := by decide +kernel
private theorem c3127_nsq   : NSqChkSq 3127   := by decide +kernel
private theorem c3127_har   : HArithChkSq 3127 := by decide +kernel
private theorem c3127_r     : LeafR 3127      := by decide +kernel
private theorem c3127_e'    : LeafE' 3127     := by decide +kernel
private theorem c3127_f1    : LeafF1 3127     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3127_s2    : S2ChkSq 3127    := by decide +kernel
private theorem c3127_s3    : S3ChkSq 3127    := by decide +kernel
private theorem c3127_iso   : LeafIso 3127    := by decide +kernel
private theorem c3127_nof2  : NoF2ChkSq 3127  := by decide +kernel
private theorem c3127_nof3  : NoF3ChkSq 3127  := by decide +kernel
private theorem c3127_nof4z : NoF4zChkSq 3127 := by decide +kernel
theorem C'_3127 : C' 3127 :=
  ⟨c3127_sqf, c3127_range, c3127_ell, leafNSq_of_sq c3127_nsq, leafHAr_of_sq c3127_har,
   c3127_r, c3127_e', c3127_f1, leafS2_of_sq c3127_s2, leafS3_of_sq c3127_s3,
   c3127_iso, leafR8_of_sq c3127_nof2 c3127_nof3 c3127_nof4z⟩
theorem not_tile'_3127 (D : CongruentDissection 3127) : False :=
  not_tile_of_conditions' 3127 C'_3127 D

private theorem c3131_sqf   : LeafSqf 3131   := by decide +kernel
private theorem c3131_range : LeafRange 3131  := by decide +kernel
private theorem c3131_ell   : LeafEll 3131    := by decide +kernel
private theorem c3131_nsq   : NSqChkSq 3131   := by decide +kernel
private theorem c3131_har   : HArithChkSq 3131 := by decide +kernel
private theorem c3131_r     : LeafR 3131      := by decide +kernel
private theorem c3131_e'    : LeafE' 3131     := by decide +kernel
private theorem c3131_f1    : LeafF1 3131     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3131_s2    : S2ChkSq 3131    := by decide +kernel
private theorem c3131_s3    : S3ChkSq 3131    := by decide +kernel
private theorem c3131_iso   : LeafIso 3131    := by decide +kernel
private theorem c3131_nof2  : NoF2ChkSq 3131  := by decide +kernel
private theorem c3131_nof3  : NoF3ChkSq 3131  := by decide +kernel
private theorem c3131_nof4z : NoF4zChkSq 3131 := by decide +kernel
theorem C'_3131 : C' 3131 :=
  ⟨c3131_sqf, c3131_range, c3131_ell, leafNSq_of_sq c3131_nsq, leafHAr_of_sq c3131_har,
   c3131_r, c3131_e', c3131_f1, leafS2_of_sq c3131_s2, leafS3_of_sq c3131_s3,
   c3131_iso, leafR8_of_sq c3131_nof2 c3131_nof3 c3131_nof4z⟩
theorem not_tile'_3131 (D : CongruentDissection 3131) : False :=
  not_tile_of_conditions' 3131 C'_3131 D

private theorem c3134_sqf   : LeafSqf 3134   := by decide +kernel
private theorem c3134_range : LeafRange 3134  := by decide +kernel
private theorem c3134_ell   : LeafEll 3134    := by decide +kernel
private theorem c3134_nsq   : NSqChkSq 3134   := by decide +kernel
private theorem c3134_har   : HArithChkSq 3134 := by decide +kernel
private theorem c3134_r     : LeafR 3134      := by decide +kernel
private theorem c3134_e'    : LeafE' 3134     := by decide +kernel
private theorem c3134_f1    : LeafF1 3134     := Or.inl (by decide)
private theorem c3134_s2    : S2ChkSq 3134    := by decide +kernel
private theorem c3134_s3    : S3ChkSq 3134    := by decide +kernel
private theorem c3134_iso   : LeafIso 3134    := by decide +kernel
private theorem c3134_nof2  : NoF2ChkSq 3134  := by decide +kernel
private theorem c3134_nof3  : NoF3ChkSq 3134  := by decide +kernel
private theorem c3134_nof4z : NoF4zChkSq 3134 := by decide +kernel
theorem C'_3134 : C' 3134 :=
  ⟨c3134_sqf, c3134_range, c3134_ell, leafNSq_of_sq c3134_nsq, leafHAr_of_sq c3134_har,
   c3134_r, c3134_e', c3134_f1, leafS2_of_sq c3134_s2, leafS3_of_sq c3134_s3,
   c3134_iso, leafR8_of_sq c3134_nof2 c3134_nof3 c3134_nof4z⟩
theorem not_tile'_3134 (D : CongruentDissection 3134) : False :=
  not_tile_of_conditions' 3134 C'_3134 D

private theorem c3138_sqf   : LeafSqf 3138   := by decide +kernel
private theorem c3138_range : LeafRange 3138  := by decide +kernel
private theorem c3138_ell   : LeafEll 3138    := by decide +kernel
private theorem c3138_nsq   : NSqChkSq 3138   := by decide +kernel
private theorem c3138_har   : HArithChkSq 3138 := by decide +kernel
private theorem c3138_r     : LeafR 3138      := by decide +kernel
private theorem c3138_e'    : LeafE' 3138     := by decide +kernel
private theorem c3138_f1    : LeafF1 3138     := Or.inl (by decide)
private theorem c3138_s2    : S2ChkSq 3138    := by decide +kernel
private theorem c3138_s3    : S3ChkSq 3138    := by decide +kernel
private theorem c3138_iso   : LeafIso 3138    := by decide +kernel
private theorem c3138_nof2  : NoF2ChkSq 3138  := by decide +kernel
private theorem c3138_nof3  : NoF3ChkSq 3138  := by decide +kernel
private theorem c3138_nof4z : NoF4zChkSq 3138 := by decide +kernel
theorem C'_3138 : C' 3138 :=
  ⟨c3138_sqf, c3138_range, c3138_ell, leafNSq_of_sq c3138_nsq, leafHAr_of_sq c3138_har,
   c3138_r, c3138_e', c3138_f1, leafS2_of_sq c3138_s2, leafS3_of_sq c3138_s3,
   c3138_iso, leafR8_of_sq c3138_nof2 c3138_nof3 c3138_nof4z⟩
theorem not_tile'_3138 (D : CongruentDissection 3138) : False :=
  not_tile_of_conditions' 3138 C'_3138 D

private theorem c3139_sqf   : LeafSqf 3139   := by decide +kernel
private theorem c3139_range : LeafRange 3139  := by decide +kernel
private theorem c3139_ell   : LeafEll 3139    := by decide +kernel
private theorem c3139_nsq   : NSqChkSq 3139   := by decide +kernel
private theorem c3139_har   : HArithChkSq 3139 := by decide +kernel
private theorem c3139_r     : LeafR 3139      := by decide +kernel
private theorem c3139_e'    : LeafE' 3139     := by decide +kernel
private theorem c3139_f1    : LeafF1 3139     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3139_s2    : S2ChkSq 3139    := by decide +kernel
private theorem c3139_s3    : S3ChkSq 3139    := by decide +kernel
private theorem c3139_iso   : LeafIso 3139    := by decide +kernel
private theorem c3139_nof2  : NoF2ChkSq 3139  := by decide +kernel
private theorem c3139_nof3  : NoF3ChkSq 3139  := by decide +kernel
private theorem c3139_nof4z : NoF4zChkSq 3139 := by decide +kernel
theorem C'_3139 : C' 3139 :=
  ⟨c3139_sqf, c3139_range, c3139_ell, leafNSq_of_sq c3139_nsq, leafHAr_of_sq c3139_har,
   c3139_r, c3139_e', c3139_f1, leafS2_of_sq c3139_s2, leafS3_of_sq c3139_s3,
   c3139_iso, leafR8_of_sq c3139_nof2 c3139_nof3 c3139_nof4z⟩
theorem not_tile'_3139 (D : CongruentDissection 3139) : False :=
  not_tile_of_conditions' 3139 C'_3139 D

end Erdos634.Draft.AllN2

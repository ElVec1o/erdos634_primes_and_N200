/- AllN2Check63: N = 2149, 2154, 2155, 2157, 2158
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2149_sqf   : LeafSqf 2149   := by decide +kernel
private theorem c2149_range : LeafRange 2149  := by decide +kernel
private theorem c2149_ell   : LeafEll 2149    := by decide +kernel
private theorem c2149_nsq   : NSqChkSq 2149   := by decide +kernel
private theorem c2149_har   : HArithChkSq 2149 := by decide +kernel
private theorem c2149_r     : LeafR 2149      := by decide +kernel
private theorem c2149_e'    : LeafE' 2149     := by decide +kernel
private theorem c2149_f1    : LeafF1 2149     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2149_s2    : S2ChkSq 2149    := by decide +kernel
private theorem c2149_s3    : S3ChkSq 2149    := by decide +kernel
private theorem c2149_iso   : LeafIso 2149    := by decide +kernel
private theorem c2149_nof2  : NoF2ChkSq 2149  := by decide +kernel
private theorem c2149_nof3  : NoF3ChkSq 2149  := by decide +kernel
private theorem c2149_nof4z : NoF4zChkSq 2149 := by decide +kernel
theorem C'_2149 : C' 2149 :=
  ⟨c2149_sqf, c2149_range, c2149_ell, leafNSq_of_sq c2149_nsq, leafHAr_of_sq c2149_har,
   c2149_r, c2149_e', c2149_f1, leafS2_of_sq c2149_s2, leafS3_of_sq c2149_s3,
   c2149_iso, leafR8_of_sq c2149_nof2 c2149_nof3 c2149_nof4z⟩
theorem not_tile'_2149 (D : CongruentDissection 2149) : False :=
  not_tile_of_conditions' 2149 C'_2149 D

private theorem c2154_sqf   : LeafSqf 2154   := by decide +kernel
private theorem c2154_range : LeafRange 2154  := by decide +kernel
private theorem c2154_ell   : LeafEll 2154    := by decide +kernel
private theorem c2154_nsq   : NSqChkSq 2154   := by decide +kernel
private theorem c2154_har   : HArithChkSq 2154 := by decide +kernel
private theorem c2154_r     : LeafR 2154      := by decide +kernel
private theorem c2154_e'    : LeafE' 2154     := by decide +kernel
private theorem c2154_f1    : LeafF1 2154     := Or.inl (by decide)
private theorem c2154_s2    : S2ChkSq 2154    := by decide +kernel
private theorem c2154_s3    : S3ChkSq 2154    := by decide +kernel
private theorem c2154_iso   : LeafIso 2154    := by decide +kernel
private theorem c2154_nof2  : NoF2ChkSq 2154  := by decide +kernel
private theorem c2154_nof3  : NoF3ChkSq 2154  := by decide +kernel
private theorem c2154_nof4z : NoF4zChkSq 2154 := by decide +kernel
theorem C'_2154 : C' 2154 :=
  ⟨c2154_sqf, c2154_range, c2154_ell, leafNSq_of_sq c2154_nsq, leafHAr_of_sq c2154_har,
   c2154_r, c2154_e', c2154_f1, leafS2_of_sq c2154_s2, leafS3_of_sq c2154_s3,
   c2154_iso, leafR8_of_sq c2154_nof2 c2154_nof3 c2154_nof4z⟩
theorem not_tile'_2154 (D : CongruentDissection 2154) : False :=
  not_tile_of_conditions' 2154 C'_2154 D

private theorem c2155_sqf   : LeafSqf 2155   := by decide +kernel
private theorem c2155_range : LeafRange 2155  := by decide +kernel
private theorem c2155_ell   : LeafEll 2155    := by decide +kernel
private theorem c2155_nsq   : NSqChkSq 2155   := by decide +kernel
private theorem c2155_har   : HArithChkSq 2155 := by decide +kernel
private theorem c2155_r     : LeafR 2155      := by decide +kernel
private theorem c2155_e'    : LeafE' 2155     := by decide +kernel
private theorem c2155_f1    : LeafF1 2155     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2155_s2    : S2ChkSq 2155    := by decide +kernel
private theorem c2155_s3    : S3ChkSq 2155    := by decide +kernel
private theorem c2155_iso   : LeafIso 2155    := by decide +kernel
private theorem c2155_nof2  : NoF2ChkSq 2155  := by decide +kernel
private theorem c2155_nof3  : NoF3ChkSq 2155  := by decide +kernel
private theorem c2155_nof4z : NoF4zChkSq 2155 := by decide +kernel
theorem C'_2155 : C' 2155 :=
  ⟨c2155_sqf, c2155_range, c2155_ell, leafNSq_of_sq c2155_nsq, leafHAr_of_sq c2155_har,
   c2155_r, c2155_e', c2155_f1, leafS2_of_sq c2155_s2, leafS3_of_sq c2155_s3,
   c2155_iso, leafR8_of_sq c2155_nof2 c2155_nof3 c2155_nof4z⟩
theorem not_tile'_2155 (D : CongruentDissection 2155) : False :=
  not_tile_of_conditions' 2155 C'_2155 D

private theorem c2157_sqf   : LeafSqf 2157   := by decide +kernel
private theorem c2157_range : LeafRange 2157  := by decide +kernel
private theorem c2157_ell   : LeafEll 2157    := by decide +kernel
private theorem c2157_nsq   : NSqChkSq 2157   := by decide +kernel
private theorem c2157_har   : HArithChkSq 2157 := by decide +kernel
private theorem c2157_r     : LeafR 2157      := by decide +kernel
private theorem c2157_e'    : LeafE' 2157     := by decide +kernel
private theorem c2157_f1    : LeafF1 2157     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2157_s2    : S2ChkSq 2157    := by decide +kernel
private theorem c2157_s3    : S3ChkSq 2157    := by decide +kernel
private theorem c2157_iso   : LeafIso 2157    := by decide +kernel
private theorem c2157_nof2  : NoF2ChkSq 2157  := by decide +kernel
private theorem c2157_nof3  : NoF3ChkSq 2157  := by decide +kernel
private theorem c2157_nof4z : NoF4zChkSq 2157 := by decide +kernel
theorem C'_2157 : C' 2157 :=
  ⟨c2157_sqf, c2157_range, c2157_ell, leafNSq_of_sq c2157_nsq, leafHAr_of_sq c2157_har,
   c2157_r, c2157_e', c2157_f1, leafS2_of_sq c2157_s2, leafS3_of_sq c2157_s3,
   c2157_iso, leafR8_of_sq c2157_nof2 c2157_nof3 c2157_nof4z⟩
theorem not_tile'_2157 (D : CongruentDissection 2157) : False :=
  not_tile_of_conditions' 2157 C'_2157 D

private theorem c2158_sqf   : LeafSqf 2158   := by decide +kernel
private theorem c2158_range : LeafRange 2158  := by decide +kernel
private theorem c2158_ell   : LeafEll 2158    := by decide +kernel
private theorem c2158_nsq   : NSqChkSq 2158   := by decide +kernel
private theorem c2158_har   : HArithChkSq 2158 := by decide +kernel
private theorem c2158_r     : LeafR 2158      := by decide +kernel
private theorem c2158_e'    : LeafE' 2158     := by decide +kernel
private theorem c2158_f1    : LeafF1 2158     := Or.inl (by decide)
private theorem c2158_s2    : S2ChkSq 2158    := by decide +kernel
private theorem c2158_s3    : S3ChkSq 2158    := by decide +kernel
private theorem c2158_iso   : LeafIso 2158    := by decide +kernel
private theorem c2158_nof2  : NoF2ChkSq 2158  := by decide +kernel
private theorem c2158_nof3  : NoF3ChkSq 2158  := by decide +kernel
private theorem c2158_nof4z : NoF4zChkSq 2158 := by decide +kernel
theorem C'_2158 : C' 2158 :=
  ⟨c2158_sqf, c2158_range, c2158_ell, leafNSq_of_sq c2158_nsq, leafHAr_of_sq c2158_har,
   c2158_r, c2158_e', c2158_f1, leafS2_of_sq c2158_s2, leafS3_of_sq c2158_s3,
   c2158_iso, leafR8_of_sq c2158_nof2 c2158_nof3 c2158_nof4z⟩
theorem not_tile'_2158 (D : CongruentDissection 2158) : False :=
  not_tile_of_conditions' 2158 C'_2158 D

end Erdos634.Draft.AllN2

/- AllN2Check218: N = 4142, 4143, 4146, 4147, 4151
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4142_sqf   : LeafSqf 4142   := by decide +kernel
private theorem c4142_range : LeafRange 4142  := by decide +kernel
private theorem c4142_ell   : LeafEll 4142    := by decide +kernel
private theorem c4142_nsq   : NSqChkSq 4142   := by decide +kernel
private theorem c4142_har   : HArithChkSq 4142 := by decide +kernel
private theorem c4142_r     : LeafR 4142      := by decide +kernel
private theorem c4142_e'    : LeafE' 4142     := by decide +kernel
private theorem c4142_f1    : LeafF1 4142     := Or.inl (by decide)
private theorem c4142_s2    : S2ChkSq 4142    := by decide +kernel
private theorem c4142_s3    : S3ChkSq 4142    := by decide +kernel
private theorem c4142_iso   : LeafIso 4142    := by decide +kernel
private theorem c4142_nof2  : NoF2ChkSq 4142  := by decide +kernel
private theorem c4142_nof3  : NoF3ChkSq 4142  := by decide +kernel
private theorem c4142_nof4z : NoF4zChkSq 4142 := by decide +kernel
theorem C'_4142 : C' 4142 :=
  ⟨c4142_sqf, c4142_range, c4142_ell, leafNSq_of_sq c4142_nsq, leafHAr_of_sq c4142_har,
   c4142_r, c4142_e', c4142_f1, leafS2_of_sq c4142_s2, leafS3_of_sq c4142_s3,
   c4142_iso, leafR8_of_sq c4142_nof2 c4142_nof3 c4142_nof4z⟩
theorem not_tile'_4142 (D : CongruentDissection 4142) : False :=
  not_tile_of_conditions' 4142 C'_4142 D

private theorem c4143_sqf   : LeafSqf 4143   := by decide +kernel
private theorem c4143_range : LeafRange 4143  := by decide +kernel
private theorem c4143_ell   : LeafEll 4143    := by decide +kernel
private theorem c4143_nsq   : NSqChkSq 4143   := by decide +kernel
private theorem c4143_har   : HArithChkSq 4143 := by decide +kernel
private theorem c4143_r     : LeafR 4143      := by decide +kernel
private theorem c4143_e'    : LeafE' 4143     := by decide +kernel
private theorem c4143_f1    : LeafF1 4143     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4143_s2    : S2ChkSq 4143    := by decide +kernel
private theorem c4143_s3    : S3ChkSq 4143    := by decide +kernel
private theorem c4143_iso   : LeafIso 4143    := by decide +kernel
private theorem c4143_nof2  : NoF2ChkSq 4143  := by decide +kernel
private theorem c4143_nof3  : NoF3ChkSq 4143  := by decide +kernel
private theorem c4143_nof4z : NoF4zChkSq 4143 := by decide +kernel
theorem C'_4143 : C' 4143 :=
  ⟨c4143_sqf, c4143_range, c4143_ell, leafNSq_of_sq c4143_nsq, leafHAr_of_sq c4143_har,
   c4143_r, c4143_e', c4143_f1, leafS2_of_sq c4143_s2, leafS3_of_sq c4143_s3,
   c4143_iso, leafR8_of_sq c4143_nof2 c4143_nof3 c4143_nof4z⟩
theorem not_tile'_4143 (D : CongruentDissection 4143) : False :=
  not_tile_of_conditions' 4143 C'_4143 D

private theorem c4146_sqf   : LeafSqf 4146   := by decide +kernel
private theorem c4146_range : LeafRange 4146  := by decide +kernel
private theorem c4146_ell   : LeafEll 4146    := by decide +kernel
private theorem c4146_nsq   : NSqChkSq 4146   := by decide +kernel
private theorem c4146_har   : HArithChkSq 4146 := by decide +kernel
private theorem c4146_r     : LeafR 4146      := by decide +kernel
private theorem c4146_e'    : LeafE' 4146     := by decide +kernel
private theorem c4146_f1    : LeafF1 4146     := Or.inl (by decide)
private theorem c4146_s2    : S2ChkSq 4146    := by decide +kernel
private theorem c4146_s3    : S3ChkSq 4146    := by decide +kernel
private theorem c4146_iso   : LeafIso 4146    := by decide +kernel
private theorem c4146_nof2  : NoF2ChkSq 4146  := by decide +kernel
private theorem c4146_nof3  : NoF3ChkSq 4146  := by decide +kernel
private theorem c4146_nof4z : NoF4zChkSq 4146 := by decide +kernel
theorem C'_4146 : C' 4146 :=
  ⟨c4146_sqf, c4146_range, c4146_ell, leafNSq_of_sq c4146_nsq, leafHAr_of_sq c4146_har,
   c4146_r, c4146_e', c4146_f1, leafS2_of_sq c4146_s2, leafS3_of_sq c4146_s3,
   c4146_iso, leafR8_of_sq c4146_nof2 c4146_nof3 c4146_nof4z⟩
theorem not_tile'_4146 (D : CongruentDissection 4146) : False :=
  not_tile_of_conditions' 4146 C'_4146 D

private theorem c4147_sqf   : LeafSqf 4147   := by decide +kernel
private theorem c4147_range : LeafRange 4147  := by decide +kernel
private theorem c4147_ell   : LeafEll 4147    := by decide +kernel
private theorem c4147_nsq   : NSqChkSq 4147   := by decide +kernel
private theorem c4147_har   : HArithChkSq 4147 := by decide +kernel
private theorem c4147_r     : LeafR 4147      := by decide +kernel
private theorem c4147_e'    : LeafE' 4147     := by decide +kernel
private theorem c4147_f1    : LeafF1 4147     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4147_s2    : S2ChkSq 4147    := by decide +kernel
private theorem c4147_s3    : S3ChkSq 4147    := by decide +kernel
private theorem c4147_iso   : LeafIso 4147    := by decide +kernel
private theorem c4147_nof2  : NoF2ChkSq 4147  := by decide +kernel
private theorem c4147_nof3  : NoF3ChkSq 4147  := by decide +kernel
private theorem c4147_nof4z : NoF4zChkSq 4147 := by decide +kernel
theorem C'_4147 : C' 4147 :=
  ⟨c4147_sqf, c4147_range, c4147_ell, leafNSq_of_sq c4147_nsq, leafHAr_of_sq c4147_har,
   c4147_r, c4147_e', c4147_f1, leafS2_of_sq c4147_s2, leafS3_of_sq c4147_s3,
   c4147_iso, leafR8_of_sq c4147_nof2 c4147_nof3 c4147_nof4z⟩
theorem not_tile'_4147 (D : CongruentDissection 4147) : False :=
  not_tile_of_conditions' 4147 C'_4147 D

private theorem c4151_sqf   : LeafSqf 4151   := by decide +kernel
private theorem c4151_range : LeafRange 4151  := by decide +kernel
private theorem c4151_ell   : LeafEll 4151    := by decide +kernel
private theorem c4151_nsq   : NSqChkSq 4151   := by decide +kernel
private theorem c4151_har   : HArithChkSq 4151 := by decide +kernel
private theorem c4151_r     : LeafR 4151      := by decide +kernel
private theorem c4151_e'    : LeafE' 4151     := by decide +kernel
private theorem c4151_f1    : LeafF1 4151     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4151_s2    : S2ChkSq 4151    := by decide +kernel
private theorem c4151_s3    : S3ChkSq 4151    := by decide +kernel
private theorem c4151_iso   : LeafIso 4151    := by decide +kernel
private theorem c4151_nof2  : NoF2ChkSq 4151  := by decide +kernel
private theorem c4151_nof3  : NoF3ChkSq 4151  := by decide +kernel
private theorem c4151_nof4z : NoF4zChkSq 4151 := by decide +kernel
theorem C'_4151 : C' 4151 :=
  ⟨c4151_sqf, c4151_range, c4151_ell, leafNSq_of_sq c4151_nsq, leafHAr_of_sq c4151_har,
   c4151_r, c4151_e', c4151_f1, leafS2_of_sq c4151_s2, leafS3_of_sq c4151_s3,
   c4151_iso, leafR8_of_sq c4151_nof2 c4151_nof3 c4151_nof4z⟩
theorem not_tile'_4151 (D : CongruentDissection 4151) : False :=
  not_tile_of_conditions' 4151 C'_4151 D

end Erdos634.Draft.AllN2

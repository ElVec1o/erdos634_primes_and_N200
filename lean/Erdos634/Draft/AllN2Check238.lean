/- AllN2Check238: N = 4393, 4398, 4399, 4402, 4403
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4393_sqf   : LeafSqf 4393   := by decide +kernel
private theorem c4393_range : LeafRange 4393  := by decide +kernel
private theorem c4393_ell   : LeafEll 4393    := by decide +kernel
private theorem c4393_nsq   : NSqChkSq 4393   := by decide +kernel
private theorem c4393_har   : HArithChkSq 4393 := by decide +kernel
private theorem c4393_r     : LeafR 4393      := by decide +kernel
private theorem c4393_e'    : LeafE' 4393     := by decide +kernel
private theorem c4393_f1    : LeafF1 4393     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4393_s2    : S2ChkSq 4393    := by decide +kernel
private theorem c4393_s3    : S3ChkSq 4393    := by decide +kernel
private theorem c4393_iso   : LeafIso 4393    := by decide +kernel
private theorem c4393_nof2  : NoF2ChkSq 4393  := by decide +kernel
private theorem c4393_nof3  : NoF3ChkSq 4393  := by decide +kernel
private theorem c4393_nof4z : NoF4zChkSq 4393 := by decide +kernel
theorem C'_4393 : C' 4393 :=
  ⟨c4393_sqf, c4393_range, c4393_ell, leafNSq_of_sq c4393_nsq, leafHAr_of_sq c4393_har,
   c4393_r, c4393_e', c4393_f1, leafS2_of_sq c4393_s2, leafS3_of_sq c4393_s3,
   c4393_iso, leafR8_of_sq c4393_nof2 c4393_nof3 c4393_nof4z⟩
theorem not_tile'_4393 (D : CongruentDissection 4393) : False :=
  not_tile_of_conditions' 4393 C'_4393 D

private theorem c4398_sqf   : LeafSqf 4398   := by decide +kernel
private theorem c4398_range : LeafRange 4398  := by decide +kernel
private theorem c4398_ell   : LeafEll 4398    := by decide +kernel
private theorem c4398_nsq   : NSqChkSq 4398   := by decide +kernel
private theorem c4398_har   : HArithChkSq 4398 := by decide +kernel
private theorem c4398_r     : LeafR 4398      := by decide +kernel
private theorem c4398_e'    : LeafE' 4398     := by decide +kernel
private theorem c4398_f1    : LeafF1 4398     := Or.inl (by decide)
private theorem c4398_s2    : S2ChkSq 4398    := by decide +kernel
private theorem c4398_s3    : S3ChkSq 4398    := by decide +kernel
private theorem c4398_iso   : LeafIso 4398    := by decide +kernel
private theorem c4398_nof2  : NoF2ChkSq 4398  := by decide +kernel
private theorem c4398_nof3  : NoF3ChkSq 4398  := by decide +kernel
private theorem c4398_nof4z : NoF4zChkSq 4398 := by decide +kernel
theorem C'_4398 : C' 4398 :=
  ⟨c4398_sqf, c4398_range, c4398_ell, leafNSq_of_sq c4398_nsq, leafHAr_of_sq c4398_har,
   c4398_r, c4398_e', c4398_f1, leafS2_of_sq c4398_s2, leafS3_of_sq c4398_s3,
   c4398_iso, leafR8_of_sq c4398_nof2 c4398_nof3 c4398_nof4z⟩
theorem not_tile'_4398 (D : CongruentDissection 4398) : False :=
  not_tile_of_conditions' 4398 C'_4398 D

private theorem c4399_sqf   : LeafSqf 4399   := by decide +kernel
private theorem c4399_range : LeafRange 4399  := by decide +kernel
private theorem c4399_ell   : LeafEll 4399    := by decide +kernel
private theorem c4399_nsq   : NSqChkSq 4399   := by decide +kernel
private theorem c4399_har   : HArithChkSq 4399 := by decide +kernel
private theorem c4399_r     : LeafR 4399      := by decide +kernel
private theorem c4399_e'    : LeafE' 4399     := by decide +kernel
private theorem c4399_f1    : LeafF1 4399     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4399_s2    : S2ChkSq 4399    := by decide +kernel
private theorem c4399_s3    : S3ChkSq 4399    := by decide +kernel
private theorem c4399_iso   : LeafIso 4399    := by decide +kernel
private theorem c4399_nof2  : NoF2ChkSq 4399  := by decide +kernel
private theorem c4399_nof3  : NoF3ChkSq 4399  := by decide +kernel
private theorem c4399_nof4z : NoF4zChkSq 4399 := by decide +kernel
theorem C'_4399 : C' 4399 :=
  ⟨c4399_sqf, c4399_range, c4399_ell, leafNSq_of_sq c4399_nsq, leafHAr_of_sq c4399_har,
   c4399_r, c4399_e', c4399_f1, leafS2_of_sq c4399_s2, leafS3_of_sq c4399_s3,
   c4399_iso, leafR8_of_sq c4399_nof2 c4399_nof3 c4399_nof4z⟩
theorem not_tile'_4399 (D : CongruentDissection 4399) : False :=
  not_tile_of_conditions' 4399 C'_4399 D

private theorem c4402_sqf   : LeafSqf 4402   := by decide +kernel
private theorem c4402_range : LeafRange 4402  := by decide +kernel
private theorem c4402_ell   : LeafEll 4402    := by decide +kernel
private theorem c4402_nsq   : NSqChkSq 4402   := by decide +kernel
private theorem c4402_har   : HArithChkSq 4402 := by decide +kernel
private theorem c4402_r     : LeafR 4402      := by decide +kernel
private theorem c4402_e'    : LeafE' 4402     := by decide +kernel
private theorem c4402_f1    : LeafF1 4402     := Or.inl (by decide)
private theorem c4402_s2    : S2ChkSq 4402    := by decide +kernel
private theorem c4402_s3    : S3ChkSq 4402    := by decide +kernel
private theorem c4402_iso   : LeafIso 4402    := by decide +kernel
private theorem c4402_nof2  : NoF2ChkSq 4402  := by decide +kernel
private theorem c4402_nof3  : NoF3ChkSq 4402  := by decide +kernel
private theorem c4402_nof4z : NoF4zChkSq 4402 := by decide +kernel
theorem C'_4402 : C' 4402 :=
  ⟨c4402_sqf, c4402_range, c4402_ell, leafNSq_of_sq c4402_nsq, leafHAr_of_sq c4402_har,
   c4402_r, c4402_e', c4402_f1, leafS2_of_sq c4402_s2, leafS3_of_sq c4402_s3,
   c4402_iso, leafR8_of_sq c4402_nof2 c4402_nof3 c4402_nof4z⟩
theorem not_tile'_4402 (D : CongruentDissection 4402) : False :=
  not_tile_of_conditions' 4402 C'_4402 D

private theorem c4403_sqf   : LeafSqf 4403   := by decide +kernel
private theorem c4403_range : LeafRange 4403  := by decide +kernel
private theorem c4403_ell   : LeafEll 4403    := by decide +kernel
private theorem c4403_nsq   : NSqChkSq 4403   := by decide +kernel
private theorem c4403_har   : HArithChkSq 4403 := by decide +kernel
private theorem c4403_r     : LeafR 4403      := by decide +kernel
private theorem c4403_e'    : LeafE' 4403     := by decide +kernel
private theorem c4403_f1    : LeafF1 4403     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4403_s2    : S2ChkSq 4403    := by decide +kernel
private theorem c4403_s3    : S3ChkSq 4403    := by decide +kernel
private theorem c4403_iso   : LeafIso 4403    := by decide +kernel
private theorem c4403_nof2  : NoF2ChkSq 4403  := by decide +kernel
private theorem c4403_nof3  : NoF3ChkSq 4403  := by decide +kernel
private theorem c4403_nof4z : NoF4zChkSq 4403 := by decide +kernel
theorem C'_4403 : C' 4403 :=
  ⟨c4403_sqf, c4403_range, c4403_ell, leafNSq_of_sq c4403_nsq, leafHAr_of_sq c4403_har,
   c4403_r, c4403_e', c4403_f1, leafS2_of_sq c4403_s2, leafS3_of_sq c4403_s3,
   c4403_iso, leafR8_of_sq c4403_nof2 c4403_nof3 c4403_nof4z⟩
theorem not_tile'_4403 (D : CongruentDissection 4403) : False :=
  not_tile_of_conditions' 4403 C'_4403 D

end Erdos634.Draft.AllN2

/- AllN2Check254: N = 4593, 4595, 4601, 4602, 4603
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4593_sqf   : LeafSqf 4593   := by decide +kernel
private theorem c4593_range : LeafRange 4593  := by decide +kernel
private theorem c4593_ell   : LeafEll 4593    := by decide +kernel
private theorem c4593_nsq   : NSqChkSq 4593   := by decide +kernel
private theorem c4593_har   : HArithChkSq 4593 := by decide +kernel
private theorem c4593_r     : LeafR 4593      := by decide +kernel
private theorem c4593_e'    : LeafE' 4593     := by decide +kernel
private theorem c4593_f1    : LeafF1 4593     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4593_s2    : S2ChkSq 4593    := by decide +kernel
private theorem c4593_s3    : S3ChkSq 4593    := by decide +kernel
private theorem c4593_iso   : LeafIso 4593    := by decide +kernel
private theorem c4593_nof2  : NoF2ChkSq 4593  := by decide +kernel
private theorem c4593_nof3  : NoF3ChkSq 4593  := by decide +kernel
private theorem c4593_nof4z : NoF4zChkSq 4593 := by decide +kernel
theorem C'_4593 : C' 4593 :=
  ⟨c4593_sqf, c4593_range, c4593_ell, leafNSq_of_sq c4593_nsq, leafHAr_of_sq c4593_har,
   c4593_r, c4593_e', c4593_f1, leafS2_of_sq c4593_s2, leafS3_of_sq c4593_s3,
   c4593_iso, leafR8_of_sq c4593_nof2 c4593_nof3 c4593_nof4z⟩
theorem not_tile'_4593 (D : CongruentDissection 4593) : False :=
  not_tile_of_conditions' 4593 C'_4593 D

private theorem c4595_sqf   : LeafSqf 4595   := by decide +kernel
private theorem c4595_range : LeafRange 4595  := by decide +kernel
private theorem c4595_ell   : LeafEll 4595    := by decide +kernel
private theorem c4595_nsq   : NSqChkSq 4595   := by decide +kernel
private theorem c4595_har   : HArithChkSq 4595 := by decide +kernel
private theorem c4595_r     : LeafR 4595      := by decide +kernel
private theorem c4595_e'    : LeafE' 4595     := by decide +kernel
private theorem c4595_f1    : LeafF1 4595     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4595_s2    : S2ChkSq 4595    := by decide +kernel
private theorem c4595_s3    : S3ChkSq 4595    := by decide +kernel
private theorem c4595_iso   : LeafIso 4595    := by decide +kernel
private theorem c4595_nof2  : NoF2ChkSq 4595  := by decide +kernel
private theorem c4595_nof3  : NoF3ChkSq 4595  := by decide +kernel
private theorem c4595_nof4z : NoF4zChkSq 4595 := by decide +kernel
theorem C'_4595 : C' 4595 :=
  ⟨c4595_sqf, c4595_range, c4595_ell, leafNSq_of_sq c4595_nsq, leafHAr_of_sq c4595_har,
   c4595_r, c4595_e', c4595_f1, leafS2_of_sq c4595_s2, leafS3_of_sq c4595_s3,
   c4595_iso, leafR8_of_sq c4595_nof2 c4595_nof3 c4595_nof4z⟩
theorem not_tile'_4595 (D : CongruentDissection 4595) : False :=
  not_tile_of_conditions' 4595 C'_4595 D

private theorem c4601_sqf   : LeafSqf 4601   := by decide +kernel
private theorem c4601_range : LeafRange 4601  := by decide +kernel
private theorem c4601_ell   : LeafEll 4601    := by decide +kernel
private theorem c4601_nsq   : NSqChkSq 4601   := by decide +kernel
private theorem c4601_har   : HArithChkSq 4601 := by decide +kernel
private theorem c4601_r     : LeafR 4601      := by decide +kernel
private theorem c4601_e'    : LeafE' 4601     := by decide +kernel
private theorem c4601_f1    : LeafF1 4601     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4601_s2    : S2ChkSq 4601    := by decide +kernel
private theorem c4601_s3    : S3ChkSq 4601    := by decide +kernel
private theorem c4601_iso   : LeafIso 4601    := by decide +kernel
private theorem c4601_nof2  : NoF2ChkSq 4601  := by decide +kernel
private theorem c4601_nof3  : NoF3ChkSq 4601  := by decide +kernel
private theorem c4601_nof4z : NoF4zChkSq 4601 := by decide +kernel
theorem C'_4601 : C' 4601 :=
  ⟨c4601_sqf, c4601_range, c4601_ell, leafNSq_of_sq c4601_nsq, leafHAr_of_sq c4601_har,
   c4601_r, c4601_e', c4601_f1, leafS2_of_sq c4601_s2, leafS3_of_sq c4601_s3,
   c4601_iso, leafR8_of_sq c4601_nof2 c4601_nof3 c4601_nof4z⟩
theorem not_tile'_4601 (D : CongruentDissection 4601) : False :=
  not_tile_of_conditions' 4601 C'_4601 D

private theorem c4602_sqf   : LeafSqf 4602   := by decide +kernel
private theorem c4602_range : LeafRange 4602  := by decide +kernel
private theorem c4602_ell   : LeafEll 4602    := by decide +kernel
private theorem c4602_nsq   : NSqChkSq 4602   := by decide +kernel
private theorem c4602_har   : HArithChkSq 4602 := by decide +kernel
private theorem c4602_r     : LeafR 4602      := by decide +kernel
private theorem c4602_e'    : LeafE' 4602     := by decide +kernel
private theorem c4602_f1    : LeafF1 4602     := Or.inl (by decide)
private theorem c4602_s2    : S2ChkSq 4602    := by decide +kernel
private theorem c4602_s3    : S3ChkSq 4602    := by decide +kernel
private theorem c4602_iso   : LeafIso 4602    := by decide +kernel
private theorem c4602_nof2  : NoF2ChkSq 4602  := by decide +kernel
private theorem c4602_nof3  : NoF3ChkSq 4602  := by decide +kernel
private theorem c4602_nof4z : NoF4zChkSq 4602 := by decide +kernel
theorem C'_4602 : C' 4602 :=
  ⟨c4602_sqf, c4602_range, c4602_ell, leafNSq_of_sq c4602_nsq, leafHAr_of_sq c4602_har,
   c4602_r, c4602_e', c4602_f1, leafS2_of_sq c4602_s2, leafS3_of_sq c4602_s3,
   c4602_iso, leafR8_of_sq c4602_nof2 c4602_nof3 c4602_nof4z⟩
theorem not_tile'_4602 (D : CongruentDissection 4602) : False :=
  not_tile_of_conditions' 4602 C'_4602 D

private theorem c4603_sqf   : LeafSqf 4603   := by decide +kernel
private theorem c4603_range : LeafRange 4603  := by decide +kernel
private theorem c4603_ell   : LeafEll 4603    := by decide +kernel
private theorem c4603_nsq   : NSqChkSq 4603   := by decide +kernel
private theorem c4603_har   : HArithChkSq 4603 := by decide +kernel
private theorem c4603_r     : LeafR 4603      := by decide +kernel
private theorem c4603_e'    : LeafE' 4603     := by decide +kernel
private theorem c4603_f1    : LeafF1 4603     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4603_s2    : S2ChkSq 4603    := by decide +kernel
private theorem c4603_s3    : S3ChkSq 4603    := by decide +kernel
private theorem c4603_iso   : LeafIso 4603    := by decide +kernel
private theorem c4603_nof2  : NoF2ChkSq 4603  := by decide +kernel
private theorem c4603_nof3  : NoF3ChkSq 4603  := by decide +kernel
private theorem c4603_nof4z : NoF4zChkSq 4603 := by decide +kernel
theorem C'_4603 : C' 4603 :=
  ⟨c4603_sqf, c4603_range, c4603_ell, leafNSq_of_sq c4603_nsq, leafHAr_of_sq c4603_har,
   c4603_r, c4603_e', c4603_f1, leafS2_of_sq c4603_s2, leafS3_of_sq c4603_s3,
   c4603_iso, leafR8_of_sq c4603_nof2 c4603_nof3 c4603_nof4z⟩
theorem not_tile'_4603 (D : CongruentDissection 4603) : False :=
  not_tile_of_conditions' 4603 C'_4603 D

end Erdos634.Draft.AllN2

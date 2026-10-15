/- AllN2Check175: N = 3583, 3586, 3587, 3590, 3594
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3583_sqf   : LeafSqf 3583   := by decide +kernel
private theorem c3583_range : LeafRange 3583  := by decide +kernel
private theorem c3583_ell   : LeafEll 3583    := by decide +kernel
private theorem c3583_nsq   : NSqChkSq 3583   := by decide +kernel
private theorem c3583_har   : HArithChkSq 3583 := by decide +kernel
private theorem c3583_r     : LeafR 3583      := by decide +kernel
private theorem c3583_e'    : LeafE' 3583     := by decide +kernel
private theorem c3583_f1    : LeafF1 3583     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3583_s2    : S2ChkSq 3583    := by decide +kernel
private theorem c3583_s3    : S3ChkSq 3583    := by decide +kernel
private theorem c3583_iso   : LeafIso 3583    := by decide +kernel
private theorem c3583_nof2  : NoF2ChkSq 3583  := by decide +kernel
private theorem c3583_nof3  : NoF3ChkSq 3583  := by decide +kernel
private theorem c3583_nof4z : NoF4zChkSq 3583 := by decide +kernel
theorem C'_3583 : C' 3583 :=
  ⟨c3583_sqf, c3583_range, c3583_ell, leafNSq_of_sq c3583_nsq, leafHAr_of_sq c3583_har,
   c3583_r, c3583_e', c3583_f1, leafS2_of_sq c3583_s2, leafS3_of_sq c3583_s3,
   c3583_iso, leafR8_of_sq c3583_nof2 c3583_nof3 c3583_nof4z⟩
theorem not_tile'_3583 (D : CongruentDissection 3583) : False :=
  not_tile_of_conditions' 3583 C'_3583 D

private theorem c3586_sqf   : LeafSqf 3586   := by decide +kernel
private theorem c3586_range : LeafRange 3586  := by decide +kernel
private theorem c3586_ell   : LeafEll 3586    := by decide +kernel
private theorem c3586_nsq   : NSqChkSq 3586   := by decide +kernel
private theorem c3586_har   : HArithChkSq 3586 := by decide +kernel
private theorem c3586_r     : LeafR 3586      := by decide +kernel
private theorem c3586_e'    : LeafE' 3586     := by decide +kernel
private theorem c3586_f1    : LeafF1 3586     := Or.inl (by decide)
private theorem c3586_s2    : S2ChkSq 3586    := by decide +kernel
private theorem c3586_s3    : S3ChkSq 3586    := by decide +kernel
private theorem c3586_iso   : LeafIso 3586    := by decide +kernel
private theorem c3586_nof2  : NoF2ChkSq 3586  := by decide +kernel
private theorem c3586_nof3  : NoF3ChkSq 3586  := by decide +kernel
private theorem c3586_nof4z : NoF4zChkSq 3586 := by decide +kernel
theorem C'_3586 : C' 3586 :=
  ⟨c3586_sqf, c3586_range, c3586_ell, leafNSq_of_sq c3586_nsq, leafHAr_of_sq c3586_har,
   c3586_r, c3586_e', c3586_f1, leafS2_of_sq c3586_s2, leafS3_of_sq c3586_s3,
   c3586_iso, leafR8_of_sq c3586_nof2 c3586_nof3 c3586_nof4z⟩
theorem not_tile'_3586 (D : CongruentDissection 3586) : False :=
  not_tile_of_conditions' 3586 C'_3586 D

private theorem c3587_sqf   : LeafSqf 3587   := by decide +kernel
private theorem c3587_range : LeafRange 3587  := by decide +kernel
private theorem c3587_ell   : LeafEll 3587    := by decide +kernel
private theorem c3587_nsq   : NSqChkSq 3587   := by decide +kernel
private theorem c3587_har   : HArithChkSq 3587 := by decide +kernel
private theorem c3587_r     : LeafR 3587      := by decide +kernel
private theorem c3587_e'    : LeafE' 3587     := by decide +kernel
private theorem c3587_f1    : LeafF1 3587     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3587_s2    : S2ChkSq 3587    := by decide +kernel
private theorem c3587_s3    : S3ChkSq 3587    := by decide +kernel
private theorem c3587_iso   : LeafIso 3587    := by decide +kernel
private theorem c3587_nof2  : NoF2ChkSq 3587  := by decide +kernel
private theorem c3587_nof3  : NoF3ChkSq 3587  := by decide +kernel
private theorem c3587_nof4z : NoF4zChkSq 3587 := by decide +kernel
theorem C'_3587 : C' 3587 :=
  ⟨c3587_sqf, c3587_range, c3587_ell, leafNSq_of_sq c3587_nsq, leafHAr_of_sq c3587_har,
   c3587_r, c3587_e', c3587_f1, leafS2_of_sq c3587_s2, leafS3_of_sq c3587_s3,
   c3587_iso, leafR8_of_sq c3587_nof2 c3587_nof3 c3587_nof4z⟩
theorem not_tile'_3587 (D : CongruentDissection 3587) : False :=
  not_tile_of_conditions' 3587 C'_3587 D

private theorem c3590_sqf   : LeafSqf 3590   := by decide +kernel
private theorem c3590_range : LeafRange 3590  := by decide +kernel
private theorem c3590_ell   : LeafEll 3590    := by decide +kernel
private theorem c3590_nsq   : NSqChkSq 3590   := by decide +kernel
private theorem c3590_har   : HArithChkSq 3590 := by decide +kernel
private theorem c3590_r     : LeafR 3590      := by decide +kernel
private theorem c3590_e'    : LeafE' 3590     := by decide +kernel
private theorem c3590_f1    : LeafF1 3590     := Or.inl (by decide)
private theorem c3590_s2    : S2ChkSq 3590    := by decide +kernel
private theorem c3590_s3    : S3ChkSq 3590    := by decide +kernel
private theorem c3590_iso   : LeafIso 3590    := by decide +kernel
private theorem c3590_nof2  : NoF2ChkSq 3590  := by decide +kernel
private theorem c3590_nof3  : NoF3ChkSq 3590  := by decide +kernel
private theorem c3590_nof4z : NoF4zChkSq 3590 := by decide +kernel
theorem C'_3590 : C' 3590 :=
  ⟨c3590_sqf, c3590_range, c3590_ell, leafNSq_of_sq c3590_nsq, leafHAr_of_sq c3590_har,
   c3590_r, c3590_e', c3590_f1, leafS2_of_sq c3590_s2, leafS3_of_sq c3590_s3,
   c3590_iso, leafR8_of_sq c3590_nof2 c3590_nof3 c3590_nof4z⟩
theorem not_tile'_3590 (D : CongruentDissection 3590) : False :=
  not_tile_of_conditions' 3590 C'_3590 D

private theorem c3594_sqf   : LeafSqf 3594   := by decide +kernel
private theorem c3594_range : LeafRange 3594  := by decide +kernel
private theorem c3594_ell   : LeafEll 3594    := by decide +kernel
private theorem c3594_nsq   : NSqChkSq 3594   := by decide +kernel
private theorem c3594_har   : HArithChkSq 3594 := by decide +kernel
private theorem c3594_r     : LeafR 3594      := by decide +kernel
private theorem c3594_e'    : LeafE' 3594     := by decide +kernel
private theorem c3594_f1    : LeafF1 3594     := Or.inl (by decide)
private theorem c3594_s2    : S2ChkSq 3594    := by decide +kernel
private theorem c3594_s3    : S3ChkSq 3594    := by decide +kernel
private theorem c3594_iso   : LeafIso 3594    := by decide +kernel
private theorem c3594_nof2  : NoF2ChkSq 3594  := by decide +kernel
private theorem c3594_nof3  : NoF3ChkSq 3594  := by decide +kernel
private theorem c3594_nof4z : NoF4zChkSq 3594 := by decide +kernel
theorem C'_3594 : C' 3594 :=
  ⟨c3594_sqf, c3594_range, c3594_ell, leafNSq_of_sq c3594_nsq, leafHAr_of_sq c3594_har,
   c3594_r, c3594_e', c3594_f1, leafS2_of_sq c3594_s2, leafS3_of_sq c3594_s3,
   c3594_iso, leafR8_of_sq c3594_nof2 c3594_nof3 c3594_nof4z⟩
theorem not_tile'_3594 (D : CongruentDissection 3594) : False :=
  not_tile_of_conditions' 3594 C'_3594 D

end Erdos634.Draft.AllN2

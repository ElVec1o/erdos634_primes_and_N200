/- AllN2Check17b: N = 591, 595, 597, 623, 633
   Squarefree exclusions via C' with sqrt-bounded checks (Wave-2 OOM fix). -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c591_sqf   : LeafSqf 591   := by decide +kernel
private theorem c591_range : LeafRange 591  := by decide +kernel
private theorem c591_ell   : LeafEll 591    := by decide +kernel
private theorem c591_nsq   : NSqChkSq 591   := by decide +kernel
private theorem c591_har   : HArithChkSq 591 := by decide +kernel
private theorem c591_r     : LeafR 591      := by decide +kernel
private theorem c591_e'    : LeafE' 591     := by decide +kernel
private theorem c591_f1    : LeafF1 591     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c591_s2    : S2ChkSq 591    := by decide +kernel
private theorem c591_s3    : S3ChkSq 591    := by decide +kernel
private theorem c591_iso   : LeafIso 591    := by decide +kernel
private theorem c591_nof2  : NoF2ChkSq 591  := by decide +kernel
private theorem c591_nof3  : NoF3ChkSq 591  := by decide +kernel
private theorem c591_nof4z : NoF4zChkSq 591 := by decide +kernel
theorem C'_591 : C' 591 :=
  ⟨c591_sqf, c591_range, c591_ell, leafNSq_of_sq c591_nsq, leafHAr_of_sq c591_har,
   c591_r, c591_e', c591_f1, leafS2_of_sq c591_s2, leafS3_of_sq c591_s3,
   c591_iso, leafR8_of_sq c591_nof2 c591_nof3 c591_nof4z⟩
theorem not_tile'_591 (D : CongruentDissection 591) : False :=
  not_tile_of_conditions' 591 C'_591 D

private theorem c595_sqf   : LeafSqf 595   := by decide +kernel
private theorem c595_range : LeafRange 595  := by decide +kernel
private theorem c595_ell   : LeafEll 595    := by decide +kernel
private theorem c595_nsq   : NSqChkSq 595   := by decide +kernel
private theorem c595_har   : HArithChkSq 595 := by decide +kernel
private theorem c595_r     : LeafR 595      := by decide +kernel
private theorem c595_e'    : LeafE' 595     := by decide +kernel
private theorem c595_f1    : LeafF1 595     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c595_s2    : S2ChkSq 595    := by decide +kernel
private theorem c595_s3    : S3ChkSq 595    := by decide +kernel
private theorem c595_iso   : LeafIso 595    := by decide +kernel
private theorem c595_nof2  : NoF2ChkSq 595  := by decide +kernel
private theorem c595_nof3  : NoF3ChkSq 595  := by decide +kernel
private theorem c595_nof4z : NoF4zChkSq 595 := by decide +kernel
theorem C'_595 : C' 595 :=
  ⟨c595_sqf, c595_range, c595_ell, leafNSq_of_sq c595_nsq, leafHAr_of_sq c595_har,
   c595_r, c595_e', c595_f1, leafS2_of_sq c595_s2, leafS3_of_sq c595_s3,
   c595_iso, leafR8_of_sq c595_nof2 c595_nof3 c595_nof4z⟩
theorem not_tile'_595 (D : CongruentDissection 595) : False :=
  not_tile_of_conditions' 595 C'_595 D

private theorem c597_sqf   : LeafSqf 597   := by decide +kernel
private theorem c597_range : LeafRange 597  := by decide +kernel
private theorem c597_ell   : LeafEll 597    := by decide +kernel
private theorem c597_nsq   : NSqChkSq 597   := by decide +kernel
private theorem c597_har   : HArithChkSq 597 := by decide +kernel
private theorem c597_r     : LeafR 597      := by decide +kernel
private theorem c597_e'    : LeafE' 597     := by decide +kernel
private theorem c597_f1    : LeafF1 597     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c597_s2    : S2ChkSq 597    := by decide +kernel
private theorem c597_s3    : S3ChkSq 597    := by decide +kernel
private theorem c597_iso   : LeafIso 597    := by decide +kernel
private theorem c597_nof2  : NoF2ChkSq 597  := by decide +kernel
private theorem c597_nof3  : NoF3ChkSq 597  := by decide +kernel
private theorem c597_nof4z : NoF4zChkSq 597 := by decide +kernel
theorem C'_597 : C' 597 :=
  ⟨c597_sqf, c597_range, c597_ell, leafNSq_of_sq c597_nsq, leafHAr_of_sq c597_har,
   c597_r, c597_e', c597_f1, leafS2_of_sq c597_s2, leafS3_of_sq c597_s3,
   c597_iso, leafR8_of_sq c597_nof2 c597_nof3 c597_nof4z⟩
theorem not_tile'_597 (D : CongruentDissection 597) : False :=
  not_tile_of_conditions' 597 C'_597 D

private theorem c623_sqf   : LeafSqf 623   := by decide +kernel
private theorem c623_range : LeafRange 623  := by decide +kernel
private theorem c623_ell   : LeafEll 623    := by decide +kernel
private theorem c623_nsq   : NSqChkSq 623   := by decide +kernel
private theorem c623_har   : HArithChkSq 623 := by decide +kernel
private theorem c623_r     : LeafR 623      := by decide +kernel
private theorem c623_e'    : LeafE' 623     := by decide +kernel
private theorem c623_f1    : LeafF1 623     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c623_s2    : S2ChkSq 623    := by decide +kernel
private theorem c623_s3    : S3ChkSq 623    := by decide +kernel
private theorem c623_iso   : LeafIso 623    := by decide +kernel
private theorem c623_nof2  : NoF2ChkSq 623  := by decide +kernel
private theorem c623_nof3  : NoF3ChkSq 623  := by decide +kernel
private theorem c623_nof4z : NoF4zChkSq 623 := by decide +kernel
theorem C'_623 : C' 623 :=
  ⟨c623_sqf, c623_range, c623_ell, leafNSq_of_sq c623_nsq, leafHAr_of_sq c623_har,
   c623_r, c623_e', c623_f1, leafS2_of_sq c623_s2, leafS3_of_sq c623_s3,
   c623_iso, leafR8_of_sq c623_nof2 c623_nof3 c623_nof4z⟩
theorem not_tile'_623 (D : CongruentDissection 623) : False :=
  not_tile_of_conditions' 623 C'_623 D

private theorem c633_sqf   : LeafSqf 633   := by decide +kernel
private theorem c633_range : LeafRange 633  := by decide +kernel
private theorem c633_ell   : LeafEll 633    := by decide +kernel
private theorem c633_nsq   : NSqChkSq 633   := by decide +kernel
private theorem c633_har   : HArithChkSq 633 := by decide +kernel
private theorem c633_r     : LeafR 633      := by decide +kernel
private theorem c633_e'    : LeafE' 633     := by decide +kernel
private theorem c633_f1    : LeafF1 633     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c633_s2    : S2ChkSq 633    := by decide +kernel
private theorem c633_s3    : S3ChkSq 633    := by decide +kernel
private theorem c633_iso   : LeafIso 633    := by decide +kernel
private theorem c633_nof2  : NoF2ChkSq 633  := by decide +kernel
private theorem c633_nof3  : NoF3ChkSq 633  := by decide +kernel
private theorem c633_nof4z : NoF4zChkSq 633 := by decide +kernel
theorem C'_633 : C' 633 :=
  ⟨c633_sqf, c633_range, c633_ell, leafNSq_of_sq c633_nsq, leafHAr_of_sq c633_har,
   c633_r, c633_e', c633_f1, leafS2_of_sq c633_s2, leafS3_of_sq c633_s3,
   c633_iso, leafR8_of_sq c633_nof2 c633_nof3 c633_nof4z⟩
theorem not_tile'_633 (D : CongruentDissection 633) : False :=
  not_tile_of_conditions' 633 C'_633 D

end Erdos634.Draft.AllN2

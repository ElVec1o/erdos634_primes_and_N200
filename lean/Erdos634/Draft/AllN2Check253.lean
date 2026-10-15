/- AllN2Check253: N = 4579, 4582, 4583, 4585, 4591
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4579_sqf   : LeafSqf 4579   := by decide +kernel
private theorem c4579_range : LeafRange 4579  := by decide +kernel
private theorem c4579_ell   : LeafEll 4579    := by decide +kernel
private theorem c4579_nsq   : NSqChkSq 4579   := by decide +kernel
private theorem c4579_har   : HArithChkSq 4579 := by decide +kernel
private theorem c4579_r     : LeafR 4579      := by decide +kernel
private theorem c4579_e'    : LeafE' 4579     := by decide +kernel
private theorem c4579_f1    : LeafF1 4579     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4579_s2    : S2ChkSq 4579    := by decide +kernel
private theorem c4579_s3    : S3ChkSq 4579    := by decide +kernel
private theorem c4579_iso   : LeafIso 4579    := by decide +kernel
private theorem c4579_nof2  : NoF2ChkSq 4579  := by decide +kernel
private theorem c4579_nof3  : NoF3ChkSq 4579  := by decide +kernel
private theorem c4579_nof4z : NoF4zChkSq 4579 := by decide +kernel
theorem C'_4579 : C' 4579 :=
  ⟨c4579_sqf, c4579_range, c4579_ell, leafNSq_of_sq c4579_nsq, leafHAr_of_sq c4579_har,
   c4579_r, c4579_e', c4579_f1, leafS2_of_sq c4579_s2, leafS3_of_sq c4579_s3,
   c4579_iso, leafR8_of_sq c4579_nof2 c4579_nof3 c4579_nof4z⟩
theorem not_tile'_4579 (D : CongruentDissection 4579) : False :=
  not_tile_of_conditions' 4579 C'_4579 D

private theorem c4582_sqf   : LeafSqf 4582   := by decide +kernel
private theorem c4582_range : LeafRange 4582  := by decide +kernel
private theorem c4582_ell   : LeafEll 4582    := by decide +kernel
private theorem c4582_nsq   : NSqChkSq 4582   := by decide +kernel
private theorem c4582_har   : HArithChkSq 4582 := by decide +kernel
private theorem c4582_r     : LeafR 4582      := by decide +kernel
private theorem c4582_e'    : LeafE' 4582     := by decide +kernel
private theorem c4582_f1    : LeafF1 4582     := Or.inl (by decide)
private theorem c4582_s2    : S2ChkSq 4582    := by decide +kernel
private theorem c4582_s3    : S3ChkSq 4582    := by decide +kernel
private theorem c4582_iso   : LeafIso 4582    := by decide +kernel
private theorem c4582_nof2  : NoF2ChkSq 4582  := by decide +kernel
private theorem c4582_nof3  : NoF3ChkSq 4582  := by decide +kernel
private theorem c4582_nof4z : NoF4zChkSq 4582 := by decide +kernel
theorem C'_4582 : C' 4582 :=
  ⟨c4582_sqf, c4582_range, c4582_ell, leafNSq_of_sq c4582_nsq, leafHAr_of_sq c4582_har,
   c4582_r, c4582_e', c4582_f1, leafS2_of_sq c4582_s2, leafS3_of_sq c4582_s3,
   c4582_iso, leafR8_of_sq c4582_nof2 c4582_nof3 c4582_nof4z⟩
theorem not_tile'_4582 (D : CongruentDissection 4582) : False :=
  not_tile_of_conditions' 4582 C'_4582 D

private theorem c4583_sqf   : LeafSqf 4583   := by decide +kernel
private theorem c4583_range : LeafRange 4583  := by decide +kernel
private theorem c4583_ell   : LeafEll 4583    := by decide +kernel
private theorem c4583_nsq   : NSqChkSq 4583   := by decide +kernel
private theorem c4583_har   : HArithChkSq 4583 := by decide +kernel
private theorem c4583_r     : LeafR 4583      := by decide +kernel
private theorem c4583_e'    : LeafE' 4583     := by decide +kernel
private theorem c4583_f1    : LeafF1 4583     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4583_s2    : S2ChkSq 4583    := by decide +kernel
private theorem c4583_s3    : S3ChkSq 4583    := by decide +kernel
private theorem c4583_iso   : LeafIso 4583    := by decide +kernel
private theorem c4583_nof2  : NoF2ChkSq 4583  := by decide +kernel
private theorem c4583_nof3  : NoF3ChkSq 4583  := by decide +kernel
private theorem c4583_nof4z : NoF4zChkSq 4583 := by decide +kernel
theorem C'_4583 : C' 4583 :=
  ⟨c4583_sqf, c4583_range, c4583_ell, leafNSq_of_sq c4583_nsq, leafHAr_of_sq c4583_har,
   c4583_r, c4583_e', c4583_f1, leafS2_of_sq c4583_s2, leafS3_of_sq c4583_s3,
   c4583_iso, leafR8_of_sq c4583_nof2 c4583_nof3 c4583_nof4z⟩
theorem not_tile'_4583 (D : CongruentDissection 4583) : False :=
  not_tile_of_conditions' 4583 C'_4583 D

private theorem c4585_sqf   : LeafSqf 4585   := by decide +kernel
private theorem c4585_range : LeafRange 4585  := by decide +kernel
private theorem c4585_ell   : LeafEll 4585    := by decide +kernel
private theorem c4585_nsq   : NSqChkSq 4585   := by decide +kernel
private theorem c4585_har   : HArithChkSq 4585 := by decide +kernel
private theorem c4585_r     : LeafR 4585      := by decide +kernel
private theorem c4585_e'    : LeafE' 4585     := by decide +kernel
private theorem c4585_f1    : LeafF1 4585     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4585_s2    : S2ChkSq 4585    := by decide +kernel
private theorem c4585_s3    : S3ChkSq 4585    := by decide +kernel
private theorem c4585_iso   : LeafIso 4585    := by decide +kernel
private theorem c4585_nof2  : NoF2ChkSq 4585  := by decide +kernel
private theorem c4585_nof3  : NoF3ChkSq 4585  := by decide +kernel
private theorem c4585_nof4z : NoF4zChkSq 4585 := by decide +kernel
theorem C'_4585 : C' 4585 :=
  ⟨c4585_sqf, c4585_range, c4585_ell, leafNSq_of_sq c4585_nsq, leafHAr_of_sq c4585_har,
   c4585_r, c4585_e', c4585_f1, leafS2_of_sq c4585_s2, leafS3_of_sq c4585_s3,
   c4585_iso, leafR8_of_sq c4585_nof2 c4585_nof3 c4585_nof4z⟩
theorem not_tile'_4585 (D : CongruentDissection 4585) : False :=
  not_tile_of_conditions' 4585 C'_4585 D

private theorem c4591_sqf   : LeafSqf 4591   := by decide +kernel
private theorem c4591_range : LeafRange 4591  := by decide +kernel
private theorem c4591_ell   : LeafEll 4591    := by decide +kernel
private theorem c4591_nsq   : NSqChkSq 4591   := by decide +kernel
private theorem c4591_har   : HArithChkSq 4591 := by decide +kernel
private theorem c4591_r     : LeafR 4591      := by decide +kernel
private theorem c4591_e'    : LeafE' 4591     := by decide +kernel
private theorem c4591_f1    : LeafF1 4591     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4591_s2    : S2ChkSq 4591    := by decide +kernel
private theorem c4591_s3    : S3ChkSq 4591    := by decide +kernel
private theorem c4591_iso   : LeafIso 4591    := by decide +kernel
private theorem c4591_nof2  : NoF2ChkSq 4591  := by decide +kernel
private theorem c4591_nof3  : NoF3ChkSq 4591  := by decide +kernel
private theorem c4591_nof4z : NoF4zChkSq 4591 := by decide +kernel
theorem C'_4591 : C' 4591 :=
  ⟨c4591_sqf, c4591_range, c4591_ell, leafNSq_of_sq c4591_nsq, leafHAr_of_sq c4591_har,
   c4591_r, c4591_e', c4591_f1, leafS2_of_sq c4591_s2, leafS3_of_sq c4591_s3,
   c4591_iso, leafR8_of_sq c4591_nof2 c4591_nof3 c4591_nof4z⟩
theorem not_tile'_4591 (D : CongruentDissection 4591) : False :=
  not_tile_of_conditions' 4591 C'_4591 D

end Erdos634.Draft.AllN2

/- AllN2Check235: N = 4355, 4358, 4359, 4362, 4363
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4355_sqf   : LeafSqf 4355   := by decide +kernel
private theorem c4355_range : LeafRange 4355  := by decide +kernel
private theorem c4355_ell   : LeafEll 4355    := by decide +kernel
private theorem c4355_nsq   : NSqChkSq 4355   := by decide +kernel
private theorem c4355_har   : HArithChkSq 4355 := by decide +kernel
private theorem c4355_r     : LeafR 4355      := by decide +kernel
private theorem c4355_e'    : LeafE' 4355     := by decide +kernel
private theorem c4355_f1    : LeafF1 4355     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4355_s2    : S2ChkSq 4355    := by decide +kernel
private theorem c4355_s3    : S3ChkSq 4355    := by decide +kernel
private theorem c4355_iso   : LeafIso 4355    := by decide +kernel
private theorem c4355_nof2  : NoF2ChkSq 4355  := by decide +kernel
private theorem c4355_nof3  : NoF3ChkSq 4355  := by decide +kernel
private theorem c4355_nof4z : NoF4zChkSq 4355 := by decide +kernel
theorem C'_4355 : C' 4355 :=
  ⟨c4355_sqf, c4355_range, c4355_ell, leafNSq_of_sq c4355_nsq, leafHAr_of_sq c4355_har,
   c4355_r, c4355_e', c4355_f1, leafS2_of_sq c4355_s2, leafS3_of_sq c4355_s3,
   c4355_iso, leafR8_of_sq c4355_nof2 c4355_nof3 c4355_nof4z⟩
theorem not_tile'_4355 (D : CongruentDissection 4355) : False :=
  not_tile_of_conditions' 4355 C'_4355 D

private theorem c4358_sqf   : LeafSqf 4358   := by decide +kernel
private theorem c4358_range : LeafRange 4358  := by decide +kernel
private theorem c4358_ell   : LeafEll 4358    := by decide +kernel
private theorem c4358_nsq   : NSqChkSq 4358   := by decide +kernel
private theorem c4358_har   : HArithChkSq 4358 := by decide +kernel
private theorem c4358_r     : LeafR 4358      := by decide +kernel
private theorem c4358_e'    : LeafE' 4358     := by decide +kernel
private theorem c4358_f1    : LeafF1 4358     := Or.inl (by decide)
private theorem c4358_s2    : S2ChkSq 4358    := by decide +kernel
private theorem c4358_s3    : S3ChkSq 4358    := by decide +kernel
private theorem c4358_iso   : LeafIso 4358    := by decide +kernel
private theorem c4358_nof2  : NoF2ChkSq 4358  := by decide +kernel
private theorem c4358_nof3  : NoF3ChkSq 4358  := by decide +kernel
private theorem c4358_nof4z : NoF4zChkSq 4358 := by decide +kernel
theorem C'_4358 : C' 4358 :=
  ⟨c4358_sqf, c4358_range, c4358_ell, leafNSq_of_sq c4358_nsq, leafHAr_of_sq c4358_har,
   c4358_r, c4358_e', c4358_f1, leafS2_of_sq c4358_s2, leafS3_of_sq c4358_s3,
   c4358_iso, leafR8_of_sq c4358_nof2 c4358_nof3 c4358_nof4z⟩
theorem not_tile'_4358 (D : CongruentDissection 4358) : False :=
  not_tile_of_conditions' 4358 C'_4358 D

private theorem c4359_sqf   : LeafSqf 4359   := by decide +kernel
private theorem c4359_range : LeafRange 4359  := by decide +kernel
private theorem c4359_ell   : LeafEll 4359    := by decide +kernel
private theorem c4359_nsq   : NSqChkSq 4359   := by decide +kernel
private theorem c4359_har   : HArithChkSq 4359 := by decide +kernel
private theorem c4359_r     : LeafR 4359      := by decide +kernel
private theorem c4359_e'    : LeafE' 4359     := by decide +kernel
private theorem c4359_f1    : LeafF1 4359     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4359_s2    : S2ChkSq 4359    := by decide +kernel
private theorem c4359_s3    : S3ChkSq 4359    := by decide +kernel
private theorem c4359_iso   : LeafIso 4359    := by decide +kernel
private theorem c4359_nof2  : NoF2ChkSq 4359  := by decide +kernel
private theorem c4359_nof3  : NoF3ChkSq 4359  := by decide +kernel
private theorem c4359_nof4z : NoF4zChkSq 4359 := by decide +kernel
theorem C'_4359 : C' 4359 :=
  ⟨c4359_sqf, c4359_range, c4359_ell, leafNSq_of_sq c4359_nsq, leafHAr_of_sq c4359_har,
   c4359_r, c4359_e', c4359_f1, leafS2_of_sq c4359_s2, leafS3_of_sq c4359_s3,
   c4359_iso, leafR8_of_sq c4359_nof2 c4359_nof3 c4359_nof4z⟩
theorem not_tile'_4359 (D : CongruentDissection 4359) : False :=
  not_tile_of_conditions' 4359 C'_4359 D

private theorem c4362_sqf   : LeafSqf 4362   := by decide +kernel
private theorem c4362_range : LeafRange 4362  := by decide +kernel
private theorem c4362_ell   : LeafEll 4362    := by decide +kernel
private theorem c4362_nsq   : NSqChkSq 4362   := by decide +kernel
private theorem c4362_har   : HArithChkSq 4362 := by decide +kernel
private theorem c4362_r     : LeafR 4362      := by decide +kernel
private theorem c4362_e'    : LeafE' 4362     := by decide +kernel
private theorem c4362_f1    : LeafF1 4362     := Or.inl (by decide)
private theorem c4362_s2    : S2ChkSq 4362    := by decide +kernel
private theorem c4362_s3    : S3ChkSq 4362    := by decide +kernel
private theorem c4362_iso   : LeafIso 4362    := by decide +kernel
private theorem c4362_nof2  : NoF2ChkSq 4362  := by decide +kernel
private theorem c4362_nof3  : NoF3ChkSq 4362  := by decide +kernel
private theorem c4362_nof4z : NoF4zChkSq 4362 := by decide +kernel
theorem C'_4362 : C' 4362 :=
  ⟨c4362_sqf, c4362_range, c4362_ell, leafNSq_of_sq c4362_nsq, leafHAr_of_sq c4362_har,
   c4362_r, c4362_e', c4362_f1, leafS2_of_sq c4362_s2, leafS3_of_sq c4362_s3,
   c4362_iso, leafR8_of_sq c4362_nof2 c4362_nof3 c4362_nof4z⟩
theorem not_tile'_4362 (D : CongruentDissection 4362) : False :=
  not_tile_of_conditions' 4362 C'_4362 D

private theorem c4363_sqf   : LeafSqf 4363   := by decide +kernel
private theorem c4363_range : LeafRange 4363  := by decide +kernel
private theorem c4363_ell   : LeafEll 4363    := by decide +kernel
private theorem c4363_nsq   : NSqChkSq 4363   := by decide +kernel
private theorem c4363_har   : HArithChkSq 4363 := by decide +kernel
private theorem c4363_r     : LeafR 4363      := by decide +kernel
private theorem c4363_e'    : LeafE' 4363     := by decide +kernel
private theorem c4363_f1    : LeafF1 4363     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4363_s2    : S2ChkSq 4363    := by decide +kernel
private theorem c4363_s3    : S3ChkSq 4363    := by decide +kernel
private theorem c4363_iso   : LeafIso 4363    := by decide +kernel
private theorem c4363_nof2  : NoF2ChkSq 4363  := by decide +kernel
private theorem c4363_nof3  : NoF3ChkSq 4363  := by decide +kernel
private theorem c4363_nof4z : NoF4zChkSq 4363 := by decide +kernel
theorem C'_4363 : C' 4363 :=
  ⟨c4363_sqf, c4363_range, c4363_ell, leafNSq_of_sq c4363_nsq, leafHAr_of_sq c4363_har,
   c4363_r, c4363_e', c4363_f1, leafS2_of_sq c4363_s2, leafS3_of_sq c4363_s3,
   c4363_iso, leafR8_of_sq c4363_nof2 c4363_nof3 c4363_nof4z⟩
theorem not_tile'_4363 (D : CongruentDissection 4363) : False :=
  not_tile_of_conditions' 4363 C'_4363 D

end Erdos634.Draft.AllN2

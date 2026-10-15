/- AllN2Check248: N = 4519, 4522, 4523, 4526, 4529
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4519_sqf   : LeafSqf 4519   := by decide +kernel
private theorem c4519_range : LeafRange 4519  := by decide +kernel
private theorem c4519_ell   : LeafEll 4519    := by decide +kernel
private theorem c4519_nsq   : NSqChkSq 4519   := by decide +kernel
private theorem c4519_har   : HArithChkSq 4519 := by decide +kernel
private theorem c4519_r     : LeafR 4519      := by decide +kernel
private theorem c4519_e'    : LeafE' 4519     := by decide +kernel
private theorem c4519_f1    : LeafF1 4519     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4519_s2    : S2ChkSq 4519    := by decide +kernel
private theorem c4519_s3    : S3ChkSq 4519    := by decide +kernel
private theorem c4519_iso   : LeafIso 4519    := by decide +kernel
private theorem c4519_nof2  : NoF2ChkSq 4519  := by decide +kernel
private theorem c4519_nof3  : NoF3ChkSq 4519  := by decide +kernel
private theorem c4519_nof4z : NoF4zChkSq 4519 := by decide +kernel
theorem C'_4519 : C' 4519 :=
  ⟨c4519_sqf, c4519_range, c4519_ell, leafNSq_of_sq c4519_nsq, leafHAr_of_sq c4519_har,
   c4519_r, c4519_e', c4519_f1, leafS2_of_sq c4519_s2, leafS3_of_sq c4519_s3,
   c4519_iso, leafR8_of_sq c4519_nof2 c4519_nof3 c4519_nof4z⟩
theorem not_tile'_4519 (D : CongruentDissection 4519) : False :=
  not_tile_of_conditions' 4519 C'_4519 D

private theorem c4522_sqf   : LeafSqf 4522   := by decide +kernel
private theorem c4522_range : LeafRange 4522  := by decide +kernel
private theorem c4522_ell   : LeafEll 4522    := by decide +kernel
private theorem c4522_nsq   : NSqChkSq 4522   := by decide +kernel
private theorem c4522_har   : HArithChkSq 4522 := by decide +kernel
private theorem c4522_r     : LeafR 4522      := by decide +kernel
private theorem c4522_e'    : LeafE' 4522     := by decide +kernel
private theorem c4522_f1    : LeafF1 4522     := Or.inl (by decide)
private theorem c4522_s2    : S2ChkSq 4522    := by decide +kernel
private theorem c4522_s3    : S3ChkSq 4522    := by decide +kernel
private theorem c4522_iso   : LeafIso 4522    := by decide +kernel
private theorem c4522_nof2  : NoF2ChkSq 4522  := by decide +kernel
private theorem c4522_nof3  : NoF3ChkSq 4522  := by decide +kernel
private theorem c4522_nof4z : NoF4zChkSq 4522 := by decide +kernel
theorem C'_4522 : C' 4522 :=
  ⟨c4522_sqf, c4522_range, c4522_ell, leafNSq_of_sq c4522_nsq, leafHAr_of_sq c4522_har,
   c4522_r, c4522_e', c4522_f1, leafS2_of_sq c4522_s2, leafS3_of_sq c4522_s3,
   c4522_iso, leafR8_of_sq c4522_nof2 c4522_nof3 c4522_nof4z⟩
theorem not_tile'_4522 (D : CongruentDissection 4522) : False :=
  not_tile_of_conditions' 4522 C'_4522 D

private theorem c4523_sqf   : LeafSqf 4523   := by decide +kernel
private theorem c4523_range : LeafRange 4523  := by decide +kernel
private theorem c4523_ell   : LeafEll 4523    := by decide +kernel
private theorem c4523_nsq   : NSqChkSq 4523   := by decide +kernel
private theorem c4523_har   : HArithChkSq 4523 := by decide +kernel
private theorem c4523_r     : LeafR 4523      := by decide +kernel
private theorem c4523_e'    : LeafE' 4523     := by decide +kernel
private theorem c4523_f1    : LeafF1 4523     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4523_s2    : S2ChkSq 4523    := by decide +kernel
private theorem c4523_s3    : S3ChkSq 4523    := by decide +kernel
private theorem c4523_iso   : LeafIso 4523    := by decide +kernel
private theorem c4523_nof2  : NoF2ChkSq 4523  := by decide +kernel
private theorem c4523_nof3  : NoF3ChkSq 4523  := by decide +kernel
private theorem c4523_nof4z : NoF4zChkSq 4523 := by decide +kernel
theorem C'_4523 : C' 4523 :=
  ⟨c4523_sqf, c4523_range, c4523_ell, leafNSq_of_sq c4523_nsq, leafHAr_of_sq c4523_har,
   c4523_r, c4523_e', c4523_f1, leafS2_of_sq c4523_s2, leafS3_of_sq c4523_s3,
   c4523_iso, leafR8_of_sq c4523_nof2 c4523_nof3 c4523_nof4z⟩
theorem not_tile'_4523 (D : CongruentDissection 4523) : False :=
  not_tile_of_conditions' 4523 C'_4523 D

private theorem c4526_sqf   : LeafSqf 4526   := by decide +kernel
private theorem c4526_range : LeafRange 4526  := by decide +kernel
private theorem c4526_ell   : LeafEll 4526    := by decide +kernel
private theorem c4526_nsq   : NSqChkSq 4526   := by decide +kernel
private theorem c4526_har   : HArithChkSq 4526 := by decide +kernel
private theorem c4526_r     : LeafR 4526      := by decide +kernel
private theorem c4526_e'    : LeafE' 4526     := by decide +kernel
private theorem c4526_f1    : LeafF1 4526     := Or.inl (by decide)
private theorem c4526_s2    : S2ChkSq 4526    := by decide +kernel
private theorem c4526_s3    : S3ChkSq 4526    := by decide +kernel
private theorem c4526_iso   : LeafIso 4526    := by decide +kernel
private theorem c4526_nof2  : NoF2ChkSq 4526  := by decide +kernel
private theorem c4526_nof3  : NoF3ChkSq 4526  := by decide +kernel
private theorem c4526_nof4z : NoF4zChkSq 4526 := by decide +kernel
theorem C'_4526 : C' 4526 :=
  ⟨c4526_sqf, c4526_range, c4526_ell, leafNSq_of_sq c4526_nsq, leafHAr_of_sq c4526_har,
   c4526_r, c4526_e', c4526_f1, leafS2_of_sq c4526_s2, leafS3_of_sq c4526_s3,
   c4526_iso, leafR8_of_sq c4526_nof2 c4526_nof3 c4526_nof4z⟩
theorem not_tile'_4526 (D : CongruentDissection 4526) : False :=
  not_tile_of_conditions' 4526 C'_4526 D

private theorem c4529_sqf   : LeafSqf 4529   := by decide +kernel
private theorem c4529_range : LeafRange 4529  := by decide +kernel
private theorem c4529_ell   : LeafEll 4529    := by decide +kernel
private theorem c4529_nsq   : NSqChkSq 4529   := by decide +kernel
private theorem c4529_har   : HArithChkSq 4529 := by decide +kernel
private theorem c4529_r     : LeafR 4529      := by decide +kernel
private theorem c4529_e'    : LeafE' 4529     := by decide +kernel
private theorem c4529_f1    : LeafF1 4529     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4529_s2    : S2ChkSq 4529    := by decide +kernel
private theorem c4529_s3    : S3ChkSq 4529    := by decide +kernel
private theorem c4529_iso   : LeafIso 4529    := by decide +kernel
private theorem c4529_nof2  : NoF2ChkSq 4529  := by decide +kernel
private theorem c4529_nof3  : NoF3ChkSq 4529  := by decide +kernel
private theorem c4529_nof4z : NoF4zChkSq 4529 := by decide +kernel
theorem C'_4529 : C' 4529 :=
  ⟨c4529_sqf, c4529_range, c4529_ell, leafNSq_of_sq c4529_nsq, leafHAr_of_sq c4529_har,
   c4529_r, c4529_e', c4529_f1, leafS2_of_sq c4529_s2, leafS3_of_sq c4529_s3,
   c4529_iso, leafR8_of_sq c4529_nof2 c4529_nof3 c4529_nof4z⟩
theorem not_tile'_4529 (D : CongruentDissection 4529) : False :=
  not_tile_of_conditions' 4529 C'_4529 D

end Erdos634.Draft.AllN2

/- AllN2Check247: N = 4502, 4506, 4507, 4510, 4511
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4502_sqf   : LeafSqf 4502   := by decide +kernel
private theorem c4502_range : LeafRange 4502  := by decide +kernel
private theorem c4502_ell   : LeafEll 4502    := by decide +kernel
private theorem c4502_nsq   : NSqChkSq 4502   := by decide +kernel
private theorem c4502_har   : HArithChkSq 4502 := by decide +kernel
private theorem c4502_r     : LeafR 4502      := by decide +kernel
private theorem c4502_e'    : LeafE' 4502     := by decide +kernel
private theorem c4502_f1    : LeafF1 4502     := Or.inl (by decide)
private theorem c4502_s2    : S2ChkSq 4502    := by decide +kernel
private theorem c4502_s3    : S3ChkSq 4502    := by decide +kernel
private theorem c4502_iso   : LeafIso 4502    := by decide +kernel
private theorem c4502_nof2  : NoF2ChkSq 4502  := by decide +kernel
private theorem c4502_nof3  : NoF3ChkSq 4502  := by decide +kernel
private theorem c4502_nof4z : NoF4zChkSq 4502 := by decide +kernel
theorem C'_4502 : C' 4502 :=
  ⟨c4502_sqf, c4502_range, c4502_ell, leafNSq_of_sq c4502_nsq, leafHAr_of_sq c4502_har,
   c4502_r, c4502_e', c4502_f1, leafS2_of_sq c4502_s2, leafS3_of_sq c4502_s3,
   c4502_iso, leafR8_of_sq c4502_nof2 c4502_nof3 c4502_nof4z⟩
theorem not_tile'_4502 (D : CongruentDissection 4502) : False :=
  not_tile_of_conditions' 4502 C'_4502 D

private theorem c4506_sqf   : LeafSqf 4506   := by decide +kernel
private theorem c4506_range : LeafRange 4506  := by decide +kernel
private theorem c4506_ell   : LeafEll 4506    := by decide +kernel
private theorem c4506_nsq   : NSqChkSq 4506   := by decide +kernel
private theorem c4506_har   : HArithChkSq 4506 := by decide +kernel
private theorem c4506_r     : LeafR 4506      := by decide +kernel
private theorem c4506_e'    : LeafE' 4506     := by decide +kernel
private theorem c4506_f1    : LeafF1 4506     := Or.inl (by decide)
private theorem c4506_s2    : S2ChkSq 4506    := by decide +kernel
private theorem c4506_s3    : S3ChkSq 4506    := by decide +kernel
private theorem c4506_iso   : LeafIso 4506    := by decide +kernel
private theorem c4506_nof2  : NoF2ChkSq 4506  := by decide +kernel
private theorem c4506_nof3  : NoF3ChkSq 4506  := by decide +kernel
private theorem c4506_nof4z : NoF4zChkSq 4506 := by decide +kernel
theorem C'_4506 : C' 4506 :=
  ⟨c4506_sqf, c4506_range, c4506_ell, leafNSq_of_sq c4506_nsq, leafHAr_of_sq c4506_har,
   c4506_r, c4506_e', c4506_f1, leafS2_of_sq c4506_s2, leafS3_of_sq c4506_s3,
   c4506_iso, leafR8_of_sq c4506_nof2 c4506_nof3 c4506_nof4z⟩
theorem not_tile'_4506 (D : CongruentDissection 4506) : False :=
  not_tile_of_conditions' 4506 C'_4506 D

private theorem c4507_sqf   : LeafSqf 4507   := by decide +kernel
private theorem c4507_range : LeafRange 4507  := by decide +kernel
private theorem c4507_ell   : LeafEll 4507    := by decide +kernel
private theorem c4507_nsq   : NSqChkSq 4507   := by decide +kernel
private theorem c4507_har   : HArithChkSq 4507 := by decide +kernel
private theorem c4507_r     : LeafR 4507      := by decide +kernel
private theorem c4507_e'    : LeafE' 4507     := by decide +kernel
private theorem c4507_f1    : LeafF1 4507     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4507_s2    : S2ChkSq 4507    := by decide +kernel
private theorem c4507_s3    : S3ChkSq 4507    := by decide +kernel
private theorem c4507_iso   : LeafIso 4507    := by decide +kernel
private theorem c4507_nof2  : NoF2ChkSq 4507  := by decide +kernel
private theorem c4507_nof3  : NoF3ChkSq 4507  := by decide +kernel
private theorem c4507_nof4z : NoF4zChkSq 4507 := by decide +kernel
theorem C'_4507 : C' 4507 :=
  ⟨c4507_sqf, c4507_range, c4507_ell, leafNSq_of_sq c4507_nsq, leafHAr_of_sq c4507_har,
   c4507_r, c4507_e', c4507_f1, leafS2_of_sq c4507_s2, leafS3_of_sq c4507_s3,
   c4507_iso, leafR8_of_sq c4507_nof2 c4507_nof3 c4507_nof4z⟩
theorem not_tile'_4507 (D : CongruentDissection 4507) : False :=
  not_tile_of_conditions' 4507 C'_4507 D

private theorem c4510_sqf   : LeafSqf 4510   := by decide +kernel
private theorem c4510_range : LeafRange 4510  := by decide +kernel
private theorem c4510_ell   : LeafEll 4510    := by decide +kernel
private theorem c4510_nsq   : NSqChkSq 4510   := by decide +kernel
private theorem c4510_har   : HArithChkSq 4510 := by decide +kernel
private theorem c4510_r     : LeafR 4510      := by decide +kernel
private theorem c4510_e'    : LeafE' 4510     := by decide +kernel
private theorem c4510_f1    : LeafF1 4510     := Or.inl (by decide)
private theorem c4510_s2    : S2ChkSq 4510    := by decide +kernel
private theorem c4510_s3    : S3ChkSq 4510    := by decide +kernel
private theorem c4510_iso   : LeafIso 4510    := by decide +kernel
private theorem c4510_nof2  : NoF2ChkSq 4510  := by decide +kernel
private theorem c4510_nof3  : NoF3ChkSq 4510  := by decide +kernel
private theorem c4510_nof4z : NoF4zChkSq 4510 := by decide +kernel
theorem C'_4510 : C' 4510 :=
  ⟨c4510_sqf, c4510_range, c4510_ell, leafNSq_of_sq c4510_nsq, leafHAr_of_sq c4510_har,
   c4510_r, c4510_e', c4510_f1, leafS2_of_sq c4510_s2, leafS3_of_sq c4510_s3,
   c4510_iso, leafR8_of_sq c4510_nof2 c4510_nof3 c4510_nof4z⟩
theorem not_tile'_4510 (D : CongruentDissection 4510) : False :=
  not_tile_of_conditions' 4510 C'_4510 D

private theorem c4511_sqf   : LeafSqf 4511   := by decide +kernel
private theorem c4511_range : LeafRange 4511  := by decide +kernel
private theorem c4511_ell   : LeafEll 4511    := by decide +kernel
private theorem c4511_nsq   : NSqChkSq 4511   := by decide +kernel
private theorem c4511_har   : HArithChkSq 4511 := by decide +kernel
private theorem c4511_r     : LeafR 4511      := by decide +kernel
private theorem c4511_e'    : LeafE' 4511     := by decide +kernel
private theorem c4511_f1    : LeafF1 4511     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4511_s2    : S2ChkSq 4511    := by decide +kernel
private theorem c4511_s3    : S3ChkSq 4511    := by decide +kernel
private theorem c4511_iso   : LeafIso 4511    := by decide +kernel
private theorem c4511_nof2  : NoF2ChkSq 4511  := by decide +kernel
private theorem c4511_nof3  : NoF3ChkSq 4511  := by decide +kernel
private theorem c4511_nof4z : NoF4zChkSq 4511 := by decide +kernel
theorem C'_4511 : C' 4511 :=
  ⟨c4511_sqf, c4511_range, c4511_ell, leafNSq_of_sq c4511_nsq, leafHAr_of_sq c4511_har,
   c4511_r, c4511_e', c4511_f1, leafS2_of_sq c4511_s2, leafS3_of_sq c4511_s3,
   c4511_iso, leafR8_of_sq c4511_nof2 c4511_nof3 c4511_nof4z⟩
theorem not_tile'_4511 (D : CongruentDissection 4511) : False :=
  not_tile_of_conditions' 4511 C'_4511 D

end Erdos634.Draft.AllN2

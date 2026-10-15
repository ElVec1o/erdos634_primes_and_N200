/- AllN2Check99: N = 2591, 2598, 2599, 2603, 2606
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2591_sqf   : LeafSqf 2591   := by decide +kernel
private theorem c2591_range : LeafRange 2591  := by decide +kernel
private theorem c2591_ell   : LeafEll 2591    := by decide +kernel
private theorem c2591_nsq   : NSqChkSq 2591   := by decide +kernel
private theorem c2591_har   : HArithChkSq 2591 := by decide +kernel
private theorem c2591_r     : LeafR 2591      := by decide +kernel
private theorem c2591_e'    : LeafE' 2591     := by decide +kernel
private theorem c2591_f1    : LeafF1 2591     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2591_s2    : S2ChkSq 2591    := by decide +kernel
private theorem c2591_s3    : S3ChkSq 2591    := by decide +kernel
private theorem c2591_iso   : LeafIso 2591    := by decide +kernel
private theorem c2591_nof2  : NoF2ChkSq 2591  := by decide +kernel
private theorem c2591_nof3  : NoF3ChkSq 2591  := by decide +kernel
private theorem c2591_nof4z : NoF4zChkSq 2591 := by decide +kernel
theorem C'_2591 : C' 2591 :=
  ⟨c2591_sqf, c2591_range, c2591_ell, leafNSq_of_sq c2591_nsq, leafHAr_of_sq c2591_har,
   c2591_r, c2591_e', c2591_f1, leafS2_of_sq c2591_s2, leafS3_of_sq c2591_s3,
   c2591_iso, leafR8_of_sq c2591_nof2 c2591_nof3 c2591_nof4z⟩
theorem not_tile'_2591 (D : CongruentDissection 2591) : False :=
  not_tile_of_conditions' 2591 C'_2591 D

private theorem c2598_sqf   : LeafSqf 2598   := by decide +kernel
private theorem c2598_range : LeafRange 2598  := by decide +kernel
private theorem c2598_ell   : LeafEll 2598    := by decide +kernel
private theorem c2598_nsq   : NSqChkSq 2598   := by decide +kernel
private theorem c2598_har   : HArithChkSq 2598 := by decide +kernel
private theorem c2598_r     : LeafR 2598      := by decide +kernel
private theorem c2598_e'    : LeafE' 2598     := by decide +kernel
private theorem c2598_f1    : LeafF1 2598     := Or.inl (by decide)
private theorem c2598_s2    : S2ChkSq 2598    := by decide +kernel
private theorem c2598_s3    : S3ChkSq 2598    := by decide +kernel
private theorem c2598_iso   : LeafIso 2598    := by decide +kernel
private theorem c2598_nof2  : NoF2ChkSq 2598  := by decide +kernel
private theorem c2598_nof3  : NoF3ChkSq 2598  := by decide +kernel
private theorem c2598_nof4z : NoF4zChkSq 2598 := by decide +kernel
theorem C'_2598 : C' 2598 :=
  ⟨c2598_sqf, c2598_range, c2598_ell, leafNSq_of_sq c2598_nsq, leafHAr_of_sq c2598_har,
   c2598_r, c2598_e', c2598_f1, leafS2_of_sq c2598_s2, leafS3_of_sq c2598_s3,
   c2598_iso, leafR8_of_sq c2598_nof2 c2598_nof3 c2598_nof4z⟩
theorem not_tile'_2598 (D : CongruentDissection 2598) : False :=
  not_tile_of_conditions' 2598 C'_2598 D

private theorem c2599_sqf   : LeafSqf 2599   := by decide +kernel
private theorem c2599_range : LeafRange 2599  := by decide +kernel
private theorem c2599_ell   : LeafEll 2599    := by decide +kernel
private theorem c2599_nsq   : NSqChkSq 2599   := by decide +kernel
private theorem c2599_har   : HArithChkSq 2599 := by decide +kernel
private theorem c2599_r     : LeafR 2599      := by decide +kernel
private theorem c2599_e'    : LeafE' 2599     := by decide +kernel
private theorem c2599_f1    : LeafF1 2599     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2599_s2    : S2ChkSq 2599    := by decide +kernel
private theorem c2599_s3    : S3ChkSq 2599    := by decide +kernel
private theorem c2599_iso   : LeafIso 2599    := by decide +kernel
private theorem c2599_nof2  : NoF2ChkSq 2599  := by decide +kernel
private theorem c2599_nof3  : NoF3ChkSq 2599  := by decide +kernel
private theorem c2599_nof4z : NoF4zChkSq 2599 := by decide +kernel
theorem C'_2599 : C' 2599 :=
  ⟨c2599_sqf, c2599_range, c2599_ell, leafNSq_of_sq c2599_nsq, leafHAr_of_sq c2599_har,
   c2599_r, c2599_e', c2599_f1, leafS2_of_sq c2599_s2, leafS3_of_sq c2599_s3,
   c2599_iso, leafR8_of_sq c2599_nof2 c2599_nof3 c2599_nof4z⟩
theorem not_tile'_2599 (D : CongruentDissection 2599) : False :=
  not_tile_of_conditions' 2599 C'_2599 D

private theorem c2603_sqf   : LeafSqf 2603   := by decide +kernel
private theorem c2603_range : LeafRange 2603  := by decide +kernel
private theorem c2603_ell   : LeafEll 2603    := by decide +kernel
private theorem c2603_nsq   : NSqChkSq 2603   := by decide +kernel
private theorem c2603_har   : HArithChkSq 2603 := by decide +kernel
private theorem c2603_r     : LeafR 2603      := by decide +kernel
private theorem c2603_e'    : LeafE' 2603     := by decide +kernel
private theorem c2603_f1    : LeafF1 2603     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2603_s2    : S2ChkSq 2603    := by decide +kernel
private theorem c2603_s3    : S3ChkSq 2603    := by decide +kernel
private theorem c2603_iso   : LeafIso 2603    := by decide +kernel
private theorem c2603_nof2  : NoF2ChkSq 2603  := by decide +kernel
private theorem c2603_nof3  : NoF3ChkSq 2603  := by decide +kernel
private theorem c2603_nof4z : NoF4zChkSq 2603 := by decide +kernel
theorem C'_2603 : C' 2603 :=
  ⟨c2603_sqf, c2603_range, c2603_ell, leafNSq_of_sq c2603_nsq, leafHAr_of_sq c2603_har,
   c2603_r, c2603_e', c2603_f1, leafS2_of_sq c2603_s2, leafS3_of_sq c2603_s3,
   c2603_iso, leafR8_of_sq c2603_nof2 c2603_nof3 c2603_nof4z⟩
theorem not_tile'_2603 (D : CongruentDissection 2603) : False :=
  not_tile_of_conditions' 2603 C'_2603 D

private theorem c2606_sqf   : LeafSqf 2606   := by decide +kernel
private theorem c2606_range : LeafRange 2606  := by decide +kernel
private theorem c2606_ell   : LeafEll 2606    := by decide +kernel
private theorem c2606_nsq   : NSqChkSq 2606   := by decide +kernel
private theorem c2606_har   : HArithChkSq 2606 := by decide +kernel
private theorem c2606_r     : LeafR 2606      := by decide +kernel
private theorem c2606_e'    : LeafE' 2606     := by decide +kernel
private theorem c2606_f1    : LeafF1 2606     := Or.inl (by decide)
private theorem c2606_s2    : S2ChkSq 2606    := by decide +kernel
private theorem c2606_s3    : S3ChkSq 2606    := by decide +kernel
private theorem c2606_iso   : LeafIso 2606    := by decide +kernel
private theorem c2606_nof2  : NoF2ChkSq 2606  := by decide +kernel
private theorem c2606_nof3  : NoF3ChkSq 2606  := by decide +kernel
private theorem c2606_nof4z : NoF4zChkSq 2606 := by decide +kernel
theorem C'_2606 : C' 2606 :=
  ⟨c2606_sqf, c2606_range, c2606_ell, leafNSq_of_sq c2606_nsq, leafHAr_of_sq c2606_har,
   c2606_r, c2606_e', c2606_f1, leafS2_of_sq c2606_s2, leafS3_of_sq c2606_s3,
   c2606_iso, leafR8_of_sq c2606_nof2 c2606_nof3 c2606_nof4z⟩
theorem not_tile'_2606 (D : CongruentDissection 2606) : False :=
  not_tile_of_conditions' 2606 C'_2606 D

end Erdos634.Draft.AllN2

/- AllN2Check104: N = 2658, 2659, 2661, 2663, 2666
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2658_sqf   : LeafSqf 2658   := by decide +kernel
private theorem c2658_range : LeafRange 2658  := by decide +kernel
private theorem c2658_ell   : LeafEll 2658    := by decide +kernel
private theorem c2658_nsq   : NSqChkSq 2658   := by decide +kernel
private theorem c2658_har   : HArithChkSq 2658 := by decide +kernel
private theorem c2658_r     : LeafR 2658      := by decide +kernel
private theorem c2658_e'    : LeafE' 2658     := by decide +kernel
private theorem c2658_f1    : LeafF1 2658     := Or.inl (by decide)
private theorem c2658_s2    : S2ChkSq 2658    := by decide +kernel
private theorem c2658_s3    : S3ChkSq 2658    := by decide +kernel
private theorem c2658_iso   : LeafIso 2658    := by decide +kernel
private theorem c2658_nof2  : NoF2ChkSq 2658  := by decide +kernel
private theorem c2658_nof3  : NoF3ChkSq 2658  := by decide +kernel
private theorem c2658_nof4z : NoF4zChkSq 2658 := by decide +kernel
theorem C'_2658 : C' 2658 :=
  ⟨c2658_sqf, c2658_range, c2658_ell, leafNSq_of_sq c2658_nsq, leafHAr_of_sq c2658_har,
   c2658_r, c2658_e', c2658_f1, leafS2_of_sq c2658_s2, leafS3_of_sq c2658_s3,
   c2658_iso, leafR8_of_sq c2658_nof2 c2658_nof3 c2658_nof4z⟩
theorem not_tile'_2658 (D : CongruentDissection 2658) : False :=
  not_tile_of_conditions' 2658 C'_2658 D

private theorem c2659_sqf   : LeafSqf 2659   := by decide +kernel
private theorem c2659_range : LeafRange 2659  := by decide +kernel
private theorem c2659_ell   : LeafEll 2659    := by decide +kernel
private theorem c2659_nsq   : NSqChkSq 2659   := by decide +kernel
private theorem c2659_har   : HArithChkSq 2659 := by decide +kernel
private theorem c2659_r     : LeafR 2659      := by decide +kernel
private theorem c2659_e'    : LeafE' 2659     := by decide +kernel
private theorem c2659_f1    : LeafF1 2659     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2659_s2    : S2ChkSq 2659    := by decide +kernel
private theorem c2659_s3    : S3ChkSq 2659    := by decide +kernel
private theorem c2659_iso   : LeafIso 2659    := by decide +kernel
private theorem c2659_nof2  : NoF2ChkSq 2659  := by decide +kernel
private theorem c2659_nof3  : NoF3ChkSq 2659  := by decide +kernel
private theorem c2659_nof4z : NoF4zChkSq 2659 := by decide +kernel
theorem C'_2659 : C' 2659 :=
  ⟨c2659_sqf, c2659_range, c2659_ell, leafNSq_of_sq c2659_nsq, leafHAr_of_sq c2659_har,
   c2659_r, c2659_e', c2659_f1, leafS2_of_sq c2659_s2, leafS3_of_sq c2659_s3,
   c2659_iso, leafR8_of_sq c2659_nof2 c2659_nof3 c2659_nof4z⟩
theorem not_tile'_2659 (D : CongruentDissection 2659) : False :=
  not_tile_of_conditions' 2659 C'_2659 D

private theorem c2661_sqf   : LeafSqf 2661   := by decide +kernel
private theorem c2661_range : LeafRange 2661  := by decide +kernel
private theorem c2661_ell   : LeafEll 2661    := by decide +kernel
private theorem c2661_nsq   : NSqChkSq 2661   := by decide +kernel
private theorem c2661_har   : HArithChkSq 2661 := by decide +kernel
private theorem c2661_r     : LeafR 2661      := by decide +kernel
private theorem c2661_e'    : LeafE' 2661     := by decide +kernel
private theorem c2661_f1    : LeafF1 2661     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2661_s2    : S2ChkSq 2661    := by decide +kernel
private theorem c2661_s3    : S3ChkSq 2661    := by decide +kernel
private theorem c2661_iso   : LeafIso 2661    := by decide +kernel
private theorem c2661_nof2  : NoF2ChkSq 2661  := by decide +kernel
private theorem c2661_nof3  : NoF3ChkSq 2661  := by decide +kernel
private theorem c2661_nof4z : NoF4zChkSq 2661 := by decide +kernel
theorem C'_2661 : C' 2661 :=
  ⟨c2661_sqf, c2661_range, c2661_ell, leafNSq_of_sq c2661_nsq, leafHAr_of_sq c2661_har,
   c2661_r, c2661_e', c2661_f1, leafS2_of_sq c2661_s2, leafS3_of_sq c2661_s3,
   c2661_iso, leafR8_of_sq c2661_nof2 c2661_nof3 c2661_nof4z⟩
theorem not_tile'_2661 (D : CongruentDissection 2661) : False :=
  not_tile_of_conditions' 2661 C'_2661 D

private theorem c2663_sqf   : LeafSqf 2663   := by decide +kernel
private theorem c2663_range : LeafRange 2663  := by decide +kernel
private theorem c2663_ell   : LeafEll 2663    := by decide +kernel
private theorem c2663_nsq   : NSqChkSq 2663   := by decide +kernel
private theorem c2663_har   : HArithChkSq 2663 := by decide +kernel
private theorem c2663_r     : LeafR 2663      := by decide +kernel
private theorem c2663_e'    : LeafE' 2663     := by decide +kernel
private theorem c2663_f1    : LeafF1 2663     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2663_s2    : S2ChkSq 2663    := by decide +kernel
private theorem c2663_s3    : S3ChkSq 2663    := by decide +kernel
private theorem c2663_iso   : LeafIso 2663    := by decide +kernel
private theorem c2663_nof2  : NoF2ChkSq 2663  := by decide +kernel
private theorem c2663_nof3  : NoF3ChkSq 2663  := by decide +kernel
private theorem c2663_nof4z : NoF4zChkSq 2663 := by decide +kernel
theorem C'_2663 : C' 2663 :=
  ⟨c2663_sqf, c2663_range, c2663_ell, leafNSq_of_sq c2663_nsq, leafHAr_of_sq c2663_har,
   c2663_r, c2663_e', c2663_f1, leafS2_of_sq c2663_s2, leafS3_of_sq c2663_s3,
   c2663_iso, leafR8_of_sq c2663_nof2 c2663_nof3 c2663_nof4z⟩
theorem not_tile'_2663 (D : CongruentDissection 2663) : False :=
  not_tile_of_conditions' 2663 C'_2663 D

private theorem c2666_sqf   : LeafSqf 2666   := by decide +kernel
private theorem c2666_range : LeafRange 2666  := by decide +kernel
private theorem c2666_ell   : LeafEll 2666    := by decide +kernel
private theorem c2666_nsq   : NSqChkSq 2666   := by decide +kernel
private theorem c2666_har   : HArithChkSq 2666 := by decide +kernel
private theorem c2666_r     : LeafR 2666      := by decide +kernel
private theorem c2666_e'    : LeafE' 2666     := by decide +kernel
private theorem c2666_f1    : LeafF1 2666     := Or.inl (by decide)
private theorem c2666_s2    : S2ChkSq 2666    := by decide +kernel
private theorem c2666_s3    : S3ChkSq 2666    := by decide +kernel
private theorem c2666_iso   : LeafIso 2666    := by decide +kernel
private theorem c2666_nof2  : NoF2ChkSq 2666  := by decide +kernel
private theorem c2666_nof3  : NoF3ChkSq 2666  := by decide +kernel
private theorem c2666_nof4z : NoF4zChkSq 2666 := by decide +kernel
theorem C'_2666 : C' 2666 :=
  ⟨c2666_sqf, c2666_range, c2666_ell, leafNSq_of_sq c2666_nsq, leafHAr_of_sq c2666_har,
   c2666_r, c2666_e', c2666_f1, leafS2_of_sq c2666_s2, leafS3_of_sq c2666_s3,
   c2666_iso, leafR8_of_sq c2666_nof2 c2666_nof3 c2666_nof4z⟩
theorem not_tile'_2666 (D : CongruentDissection 2666) : False :=
  not_tile_of_conditions' 2666 C'_2666 D

end Erdos634.Draft.AllN2

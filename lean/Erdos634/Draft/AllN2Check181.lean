/- AllN2Check181: N = 3657, 3658, 3659, 3661, 3662
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3657_sqf   : LeafSqf 3657   := by decide +kernel
private theorem c3657_range : LeafRange 3657  := by decide +kernel
private theorem c3657_ell   : LeafEll 3657    := by decide +kernel
private theorem c3657_nsq   : NSqChkSq 3657   := by decide +kernel
private theorem c3657_har   : HArithChkSq 3657 := by decide +kernel
private theorem c3657_r     : LeafR 3657      := by decide +kernel
private theorem c3657_e'    : LeafE' 3657     := by decide +kernel
private theorem c3657_f1    : LeafF1 3657     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3657_s2    : S2ChkSq 3657    := by decide +kernel
private theorem c3657_s3    : S3ChkSq 3657    := by decide +kernel
private theorem c3657_iso   : LeafIso 3657    := by decide +kernel
private theorem c3657_nof2  : NoF2ChkSq 3657  := by decide +kernel
private theorem c3657_nof3  : NoF3ChkSq 3657  := by decide +kernel
private theorem c3657_nof4z : NoF4zChkSq 3657 := by decide +kernel
theorem C'_3657 : C' 3657 :=
  ⟨c3657_sqf, c3657_range, c3657_ell, leafNSq_of_sq c3657_nsq, leafHAr_of_sq c3657_har,
   c3657_r, c3657_e', c3657_f1, leafS2_of_sq c3657_s2, leafS3_of_sq c3657_s3,
   c3657_iso, leafR8_of_sq c3657_nof2 c3657_nof3 c3657_nof4z⟩
theorem not_tile'_3657 (D : CongruentDissection 3657) : False :=
  not_tile_of_conditions' 3657 C'_3657 D

private theorem c3658_sqf   : LeafSqf 3658   := by decide +kernel
private theorem c3658_range : LeafRange 3658  := by decide +kernel
private theorem c3658_ell   : LeafEll 3658    := by decide +kernel
private theorem c3658_nsq   : NSqChkSq 3658   := by decide +kernel
private theorem c3658_har   : HArithChkSq 3658 := by decide +kernel
private theorem c3658_r     : LeafR 3658      := by decide +kernel
private theorem c3658_e'    : LeafE' 3658     := by decide +kernel
private theorem c3658_f1    : LeafF1 3658     := Or.inl (by decide)
private theorem c3658_s2    : S2ChkSq 3658    := by decide +kernel
private theorem c3658_s3    : S3ChkSq 3658    := by decide +kernel
private theorem c3658_iso   : LeafIso 3658    := by decide +kernel
private theorem c3658_nof2  : NoF2ChkSq 3658  := by decide +kernel
private theorem c3658_nof3  : NoF3ChkSq 3658  := by decide +kernel
private theorem c3658_nof4z : NoF4zChkSq 3658 := by decide +kernel
theorem C'_3658 : C' 3658 :=
  ⟨c3658_sqf, c3658_range, c3658_ell, leafNSq_of_sq c3658_nsq, leafHAr_of_sq c3658_har,
   c3658_r, c3658_e', c3658_f1, leafS2_of_sq c3658_s2, leafS3_of_sq c3658_s3,
   c3658_iso, leafR8_of_sq c3658_nof2 c3658_nof3 c3658_nof4z⟩
theorem not_tile'_3658 (D : CongruentDissection 3658) : False :=
  not_tile_of_conditions' 3658 C'_3658 D

private theorem c3659_sqf   : LeafSqf 3659   := by decide +kernel
private theorem c3659_range : LeafRange 3659  := by decide +kernel
private theorem c3659_ell   : LeafEll 3659    := by decide +kernel
private theorem c3659_nsq   : NSqChkSq 3659   := by decide +kernel
private theorem c3659_har   : HArithChkSq 3659 := by decide +kernel
private theorem c3659_r     : LeafR 3659      := by decide +kernel
private theorem c3659_e'    : LeafE' 3659     := by decide +kernel
private theorem c3659_f1    : LeafF1 3659     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3659_s2    : S2ChkSq 3659    := by decide +kernel
private theorem c3659_s3    : S3ChkSq 3659    := by decide +kernel
private theorem c3659_iso   : LeafIso 3659    := by decide +kernel
private theorem c3659_nof2  : NoF2ChkSq 3659  := by decide +kernel
private theorem c3659_nof3  : NoF3ChkSq 3659  := by decide +kernel
private theorem c3659_nof4z : NoF4zChkSq 3659 := by decide +kernel
theorem C'_3659 : C' 3659 :=
  ⟨c3659_sqf, c3659_range, c3659_ell, leafNSq_of_sq c3659_nsq, leafHAr_of_sq c3659_har,
   c3659_r, c3659_e', c3659_f1, leafS2_of_sq c3659_s2, leafS3_of_sq c3659_s3,
   c3659_iso, leafR8_of_sq c3659_nof2 c3659_nof3 c3659_nof4z⟩
theorem not_tile'_3659 (D : CongruentDissection 3659) : False :=
  not_tile_of_conditions' 3659 C'_3659 D

private theorem c3661_sqf   : LeafSqf 3661   := by decide +kernel
private theorem c3661_range : LeafRange 3661  := by decide +kernel
private theorem c3661_ell   : LeafEll 3661    := by decide +kernel
private theorem c3661_nsq   : NSqChkSq 3661   := by decide +kernel
private theorem c3661_har   : HArithChkSq 3661 := by decide +kernel
private theorem c3661_r     : LeafR 3661      := by decide +kernel
private theorem c3661_e'    : LeafE' 3661     := by decide +kernel
private theorem c3661_f1    : LeafF1 3661     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3661_s2    : S2ChkSq 3661    := by decide +kernel
private theorem c3661_s3    : S3ChkSq 3661    := by decide +kernel
private theorem c3661_iso   : LeafIso 3661    := by decide +kernel
private theorem c3661_nof2  : NoF2ChkSq 3661  := by decide +kernel
private theorem c3661_nof3  : NoF3ChkSq 3661  := by decide +kernel
private theorem c3661_nof4z : NoF4zChkSq 3661 := by decide +kernel
theorem C'_3661 : C' 3661 :=
  ⟨c3661_sqf, c3661_range, c3661_ell, leafNSq_of_sq c3661_nsq, leafHAr_of_sq c3661_har,
   c3661_r, c3661_e', c3661_f1, leafS2_of_sq c3661_s2, leafS3_of_sq c3661_s3,
   c3661_iso, leafR8_of_sq c3661_nof2 c3661_nof3 c3661_nof4z⟩
theorem not_tile'_3661 (D : CongruentDissection 3661) : False :=
  not_tile_of_conditions' 3661 C'_3661 D

private theorem c3662_sqf   : LeafSqf 3662   := by decide +kernel
private theorem c3662_range : LeafRange 3662  := by decide +kernel
private theorem c3662_ell   : LeafEll 3662    := by decide +kernel
private theorem c3662_nsq   : NSqChkSq 3662   := by decide +kernel
private theorem c3662_har   : HArithChkSq 3662 := by decide +kernel
private theorem c3662_r     : LeafR 3662      := by decide +kernel
private theorem c3662_e'    : LeafE' 3662     := by decide +kernel
private theorem c3662_f1    : LeafF1 3662     := Or.inl (by decide)
private theorem c3662_s2    : S2ChkSq 3662    := by decide +kernel
private theorem c3662_s3    : S3ChkSq 3662    := by decide +kernel
private theorem c3662_iso   : LeafIso 3662    := by decide +kernel
private theorem c3662_nof2  : NoF2ChkSq 3662  := by decide +kernel
private theorem c3662_nof3  : NoF3ChkSq 3662  := by decide +kernel
private theorem c3662_nof4z : NoF4zChkSq 3662 := by decide +kernel
theorem C'_3662 : C' 3662 :=
  ⟨c3662_sqf, c3662_range, c3662_ell, leafNSq_of_sq c3662_nsq, leafHAr_of_sq c3662_har,
   c3662_r, c3662_e', c3662_f1, leafS2_of_sq c3662_s2, leafS3_of_sq c3662_s3,
   c3662_iso, leafR8_of_sq c3662_nof2 c3662_nof3 c3662_nof4z⟩
theorem not_tile'_3662 (D : CongruentDissection 3662) : False :=
  not_tile_of_conditions' 3662 C'_3662 D

end Erdos634.Draft.AllN2

/- AllN2Check180: N = 3643, 3646, 3647, 3651, 3655
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3643_sqf   : LeafSqf 3643   := by decide +kernel
private theorem c3643_range : LeafRange 3643  := by decide +kernel
private theorem c3643_ell   : LeafEll 3643    := by decide +kernel
private theorem c3643_nsq   : NSqChkSq 3643   := by decide +kernel
private theorem c3643_har   : HArithChkSq 3643 := by decide +kernel
private theorem c3643_r     : LeafR 3643      := by decide +kernel
private theorem c3643_e'    : LeafE' 3643     := by decide +kernel
private theorem c3643_f1    : LeafF1 3643     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3643_s2    : S2ChkSq 3643    := by decide +kernel
private theorem c3643_s3    : S3ChkSq 3643    := by decide +kernel
private theorem c3643_iso   : LeafIso 3643    := by decide +kernel
private theorem c3643_nof2  : NoF2ChkSq 3643  := by decide +kernel
private theorem c3643_nof3  : NoF3ChkSq 3643  := by decide +kernel
private theorem c3643_nof4z : NoF4zChkSq 3643 := by decide +kernel
theorem C'_3643 : C' 3643 :=
  ⟨c3643_sqf, c3643_range, c3643_ell, leafNSq_of_sq c3643_nsq, leafHAr_of_sq c3643_har,
   c3643_r, c3643_e', c3643_f1, leafS2_of_sq c3643_s2, leafS3_of_sq c3643_s3,
   c3643_iso, leafR8_of_sq c3643_nof2 c3643_nof3 c3643_nof4z⟩
theorem not_tile'_3643 (D : CongruentDissection 3643) : False :=
  not_tile_of_conditions' 3643 C'_3643 D

private theorem c3646_sqf   : LeafSqf 3646   := by decide +kernel
private theorem c3646_range : LeafRange 3646  := by decide +kernel
private theorem c3646_ell   : LeafEll 3646    := by decide +kernel
private theorem c3646_nsq   : NSqChkSq 3646   := by decide +kernel
private theorem c3646_har   : HArithChkSq 3646 := by decide +kernel
private theorem c3646_r     : LeafR 3646      := by decide +kernel
private theorem c3646_e'    : LeafE' 3646     := by decide +kernel
private theorem c3646_f1    : LeafF1 3646     := Or.inl (by decide)
private theorem c3646_s2    : S2ChkSq 3646    := by decide +kernel
private theorem c3646_s3    : S3ChkSq 3646    := by decide +kernel
private theorem c3646_iso   : LeafIso 3646    := by decide +kernel
private theorem c3646_nof2  : NoF2ChkSq 3646  := by decide +kernel
private theorem c3646_nof3  : NoF3ChkSq 3646  := by decide +kernel
private theorem c3646_nof4z : NoF4zChkSq 3646 := by decide +kernel
theorem C'_3646 : C' 3646 :=
  ⟨c3646_sqf, c3646_range, c3646_ell, leafNSq_of_sq c3646_nsq, leafHAr_of_sq c3646_har,
   c3646_r, c3646_e', c3646_f1, leafS2_of_sq c3646_s2, leafS3_of_sq c3646_s3,
   c3646_iso, leafR8_of_sq c3646_nof2 c3646_nof3 c3646_nof4z⟩
theorem not_tile'_3646 (D : CongruentDissection 3646) : False :=
  not_tile_of_conditions' 3646 C'_3646 D

private theorem c3647_sqf   : LeafSqf 3647   := by decide +kernel
private theorem c3647_range : LeafRange 3647  := by decide +kernel
private theorem c3647_ell   : LeafEll 3647    := by decide +kernel
private theorem c3647_nsq   : NSqChkSq 3647   := by decide +kernel
private theorem c3647_har   : HArithChkSq 3647 := by decide +kernel
private theorem c3647_r     : LeafR 3647      := by decide +kernel
private theorem c3647_e'    : LeafE' 3647     := by decide +kernel
private theorem c3647_f1    : LeafF1 3647     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3647_s2    : S2ChkSq 3647    := by decide +kernel
private theorem c3647_s3    : S3ChkSq 3647    := by decide +kernel
private theorem c3647_iso   : LeafIso 3647    := by decide +kernel
private theorem c3647_nof2  : NoF2ChkSq 3647  := by decide +kernel
private theorem c3647_nof3  : NoF3ChkSq 3647  := by decide +kernel
private theorem c3647_nof4z : NoF4zChkSq 3647 := by decide +kernel
theorem C'_3647 : C' 3647 :=
  ⟨c3647_sqf, c3647_range, c3647_ell, leafNSq_of_sq c3647_nsq, leafHAr_of_sq c3647_har,
   c3647_r, c3647_e', c3647_f1, leafS2_of_sq c3647_s2, leafS3_of_sq c3647_s3,
   c3647_iso, leafR8_of_sq c3647_nof2 c3647_nof3 c3647_nof4z⟩
theorem not_tile'_3647 (D : CongruentDissection 3647) : False :=
  not_tile_of_conditions' 3647 C'_3647 D

private theorem c3651_sqf   : LeafSqf 3651   := by decide +kernel
private theorem c3651_range : LeafRange 3651  := by decide +kernel
private theorem c3651_ell   : LeafEll 3651    := by decide +kernel
private theorem c3651_nsq   : NSqChkSq 3651   := by decide +kernel
private theorem c3651_har   : HArithChkSq 3651 := by decide +kernel
private theorem c3651_r     : LeafR 3651      := by decide +kernel
private theorem c3651_e'    : LeafE' 3651     := by decide +kernel
private theorem c3651_f1    : LeafF1 3651     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3651_s2    : S2ChkSq 3651    := by decide +kernel
private theorem c3651_s3    : S3ChkSq 3651    := by decide +kernel
private theorem c3651_iso   : LeafIso 3651    := by decide +kernel
private theorem c3651_nof2  : NoF2ChkSq 3651  := by decide +kernel
private theorem c3651_nof3  : NoF3ChkSq 3651  := by decide +kernel
private theorem c3651_nof4z : NoF4zChkSq 3651 := by decide +kernel
theorem C'_3651 : C' 3651 :=
  ⟨c3651_sqf, c3651_range, c3651_ell, leafNSq_of_sq c3651_nsq, leafHAr_of_sq c3651_har,
   c3651_r, c3651_e', c3651_f1, leafS2_of_sq c3651_s2, leafS3_of_sq c3651_s3,
   c3651_iso, leafR8_of_sq c3651_nof2 c3651_nof3 c3651_nof4z⟩
theorem not_tile'_3651 (D : CongruentDissection 3651) : False :=
  not_tile_of_conditions' 3651 C'_3651 D

private theorem c3655_sqf   : LeafSqf 3655   := by decide +kernel
private theorem c3655_range : LeafRange 3655  := by decide +kernel
private theorem c3655_ell   : LeafEll 3655    := by decide +kernel
private theorem c3655_nsq   : NSqChkSq 3655   := by decide +kernel
private theorem c3655_har   : HArithChkSq 3655 := by decide +kernel
private theorem c3655_r     : LeafR 3655      := by decide +kernel
private theorem c3655_e'    : LeafE' 3655     := by decide +kernel
private theorem c3655_f1    : LeafF1 3655     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3655_s2    : S2ChkSq 3655    := by decide +kernel
private theorem c3655_s3    : S3ChkSq 3655    := by decide +kernel
private theorem c3655_iso   : LeafIso 3655    := by decide +kernel
private theorem c3655_nof2  : NoF2ChkSq 3655  := by decide +kernel
private theorem c3655_nof3  : NoF3ChkSq 3655  := by decide +kernel
private theorem c3655_nof4z : NoF4zChkSq 3655 := by decide +kernel
theorem C'_3655 : C' 3655 :=
  ⟨c3655_sqf, c3655_range, c3655_ell, leafNSq_of_sq c3655_nsq, leafHAr_of_sq c3655_har,
   c3655_r, c3655_e', c3655_f1, leafS2_of_sq c3655_s2, leafS3_of_sq c3655_s3,
   c3655_iso, leafR8_of_sq c3655_nof2 c3655_nof3 c3655_nof4z⟩
theorem not_tile'_3655 (D : CongruentDissection 3655) : False :=
  not_tile_of_conditions' 3655 C'_3655 D

end Erdos634.Draft.AllN2

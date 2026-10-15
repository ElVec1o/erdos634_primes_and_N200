/- AllN2Check111: N = 2757, 2758, 2759, 2761, 2765
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2757_sqf   : LeafSqf 2757   := by decide +kernel
private theorem c2757_range : LeafRange 2757  := by decide +kernel
private theorem c2757_ell   : LeafEll 2757    := by decide +kernel
private theorem c2757_nsq   : NSqChkSq 2757   := by decide +kernel
private theorem c2757_har   : HArithChkSq 2757 := by decide +kernel
private theorem c2757_r     : LeafR 2757      := by decide +kernel
private theorem c2757_e'    : LeafE' 2757     := by decide +kernel
private theorem c2757_f1    : LeafF1 2757     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2757_s2    : S2ChkSq 2757    := by decide +kernel
private theorem c2757_s3    : S3ChkSq 2757    := by decide +kernel
private theorem c2757_iso   : LeafIso 2757    := by decide +kernel
private theorem c2757_nof2  : NoF2ChkSq 2757  := by decide +kernel
private theorem c2757_nof3  : NoF3ChkSq 2757  := by decide +kernel
private theorem c2757_nof4z : NoF4zChkSq 2757 := by decide +kernel
theorem C'_2757 : C' 2757 :=
  ⟨c2757_sqf, c2757_range, c2757_ell, leafNSq_of_sq c2757_nsq, leafHAr_of_sq c2757_har,
   c2757_r, c2757_e', c2757_f1, leafS2_of_sq c2757_s2, leafS3_of_sq c2757_s3,
   c2757_iso, leafR8_of_sq c2757_nof2 c2757_nof3 c2757_nof4z⟩
theorem not_tile'_2757 (D : CongruentDissection 2757) : False :=
  not_tile_of_conditions' 2757 C'_2757 D

private theorem c2758_sqf   : LeafSqf 2758   := by decide +kernel
private theorem c2758_range : LeafRange 2758  := by decide +kernel
private theorem c2758_ell   : LeafEll 2758    := by decide +kernel
private theorem c2758_nsq   : NSqChkSq 2758   := by decide +kernel
private theorem c2758_har   : HArithChkSq 2758 := by decide +kernel
private theorem c2758_r     : LeafR 2758      := by decide +kernel
private theorem c2758_e'    : LeafE' 2758     := by decide +kernel
private theorem c2758_f1    : LeafF1 2758     := Or.inl (by decide)
private theorem c2758_s2    : S2ChkSq 2758    := by decide +kernel
private theorem c2758_s3    : S3ChkSq 2758    := by decide +kernel
private theorem c2758_iso   : LeafIso 2758    := by decide +kernel
private theorem c2758_nof2  : NoF2ChkSq 2758  := by decide +kernel
private theorem c2758_nof3  : NoF3ChkSq 2758  := by decide +kernel
private theorem c2758_nof4z : NoF4zChkSq 2758 := by decide +kernel
theorem C'_2758 : C' 2758 :=
  ⟨c2758_sqf, c2758_range, c2758_ell, leafNSq_of_sq c2758_nsq, leafHAr_of_sq c2758_har,
   c2758_r, c2758_e', c2758_f1, leafS2_of_sq c2758_s2, leafS3_of_sq c2758_s3,
   c2758_iso, leafR8_of_sq c2758_nof2 c2758_nof3 c2758_nof4z⟩
theorem not_tile'_2758 (D : CongruentDissection 2758) : False :=
  not_tile_of_conditions' 2758 C'_2758 D

private theorem c2759_sqf   : LeafSqf 2759   := by decide +kernel
private theorem c2759_range : LeafRange 2759  := by decide +kernel
private theorem c2759_ell   : LeafEll 2759    := by decide +kernel
private theorem c2759_nsq   : NSqChkSq 2759   := by decide +kernel
private theorem c2759_har   : HArithChkSq 2759 := by decide +kernel
private theorem c2759_r     : LeafR 2759      := by decide +kernel
private theorem c2759_e'    : LeafE' 2759     := by decide +kernel
private theorem c2759_f1    : LeafF1 2759     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2759_s2    : S2ChkSq 2759    := by decide +kernel
private theorem c2759_s3    : S3ChkSq 2759    := by decide +kernel
private theorem c2759_iso   : LeafIso 2759    := by decide +kernel
private theorem c2759_nof2  : NoF2ChkSq 2759  := by decide +kernel
private theorem c2759_nof3  : NoF3ChkSq 2759  := by decide +kernel
private theorem c2759_nof4z : NoF4zChkSq 2759 := by decide +kernel
theorem C'_2759 : C' 2759 :=
  ⟨c2759_sqf, c2759_range, c2759_ell, leafNSq_of_sq c2759_nsq, leafHAr_of_sq c2759_har,
   c2759_r, c2759_e', c2759_f1, leafS2_of_sq c2759_s2, leafS3_of_sq c2759_s3,
   c2759_iso, leafR8_of_sq c2759_nof2 c2759_nof3 c2759_nof4z⟩
theorem not_tile'_2759 (D : CongruentDissection 2759) : False :=
  not_tile_of_conditions' 2759 C'_2759 D

private theorem c2761_sqf   : LeafSqf 2761   := by decide +kernel
private theorem c2761_range : LeafRange 2761  := by decide +kernel
private theorem c2761_ell   : LeafEll 2761    := by decide +kernel
private theorem c2761_nsq   : NSqChkSq 2761   := by decide +kernel
private theorem c2761_har   : HArithChkSq 2761 := by decide +kernel
private theorem c2761_r     : LeafR 2761      := by decide +kernel
private theorem c2761_e'    : LeafE' 2761     := by decide +kernel
private theorem c2761_f1    : LeafF1 2761     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2761_s2    : S2ChkSq 2761    := by decide +kernel
private theorem c2761_s3    : S3ChkSq 2761    := by decide +kernel
private theorem c2761_iso   : LeafIso 2761    := by decide +kernel
private theorem c2761_nof2  : NoF2ChkSq 2761  := by decide +kernel
private theorem c2761_nof3  : NoF3ChkSq 2761  := by decide +kernel
private theorem c2761_nof4z : NoF4zChkSq 2761 := by decide +kernel
theorem C'_2761 : C' 2761 :=
  ⟨c2761_sqf, c2761_range, c2761_ell, leafNSq_of_sq c2761_nsq, leafHAr_of_sq c2761_har,
   c2761_r, c2761_e', c2761_f1, leafS2_of_sq c2761_s2, leafS3_of_sq c2761_s3,
   c2761_iso, leafR8_of_sq c2761_nof2 c2761_nof3 c2761_nof4z⟩
theorem not_tile'_2761 (D : CongruentDissection 2761) : False :=
  not_tile_of_conditions' 2761 C'_2761 D

private theorem c2765_sqf   : LeafSqf 2765   := by decide +kernel
private theorem c2765_range : LeafRange 2765  := by decide +kernel
private theorem c2765_ell   : LeafEll 2765    := by decide +kernel
private theorem c2765_nsq   : NSqChkSq 2765   := by decide +kernel
private theorem c2765_har   : HArithChkSq 2765 := by decide +kernel
private theorem c2765_r     : LeafR 2765      := by decide +kernel
private theorem c2765_e'    : LeafE' 2765     := by decide +kernel
private theorem c2765_f1    : LeafF1 2765     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2765_s2    : S2ChkSq 2765    := by decide +kernel
private theorem c2765_s3    : S3ChkSq 2765    := by decide +kernel
private theorem c2765_iso   : LeafIso 2765    := by decide +kernel
private theorem c2765_nof2  : NoF2ChkSq 2765  := by decide +kernel
private theorem c2765_nof3  : NoF3ChkSq 2765  := by decide +kernel
private theorem c2765_nof4z : NoF4zChkSq 2765 := by decide +kernel
theorem C'_2765 : C' 2765 :=
  ⟨c2765_sqf, c2765_range, c2765_ell, leafNSq_of_sq c2765_nsq, leafHAr_of_sq c2765_har,
   c2765_r, c2765_e', c2765_f1, leafS2_of_sq c2765_s2, leafS3_of_sq c2765_s3,
   c2765_iso, leafR8_of_sq c2765_nof2 c2765_nof3 c2765_nof4z⟩
theorem not_tile'_2765 (D : CongruentDissection 2765) : False :=
  not_tile_of_conditions' 2765 C'_2765 D

end Erdos634.Draft.AllN2

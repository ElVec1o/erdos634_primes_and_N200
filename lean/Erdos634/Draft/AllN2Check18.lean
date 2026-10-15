/- AllN2Check18: N = 635, 655, 665, 669, 679
   Squarefree exclusions via C' with sqrt-bounded checks (Wave-2 OOM fix). -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c635_sqf   : LeafSqf 635   := by decide +kernel
private theorem c635_range : LeafRange 635  := by decide +kernel
private theorem c635_ell   : LeafEll 635    := by decide +kernel
private theorem c635_nsq   : NSqChkSq 635   := by decide +kernel
private theorem c635_har   : HArithChkSq 635 := by decide +kernel
private theorem c635_r     : LeafR 635      := by decide +kernel
private theorem c635_e'    : LeafE' 635     := by decide +kernel
private theorem c635_f1    : LeafF1 635     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c635_s2    : S2ChkSq 635    := by decide +kernel
private theorem c635_s3    : S3ChkSq 635    := by decide +kernel
private theorem c635_iso   : LeafIso 635    := by decide +kernel
private theorem c635_nof2  : NoF2ChkSq 635  := by decide +kernel
private theorem c635_nof3  : NoF3ChkSq 635  := by decide +kernel
private theorem c635_nof4z : NoF4zChkSq 635 := by decide +kernel
theorem C'_635 : C' 635 :=
  ⟨c635_sqf, c635_range, c635_ell, leafNSq_of_sq c635_nsq, leafHAr_of_sq c635_har,
   c635_r, c635_e', c635_f1, leafS2_of_sq c635_s2, leafS3_of_sq c635_s3,
   c635_iso, leafR8_of_sq c635_nof2 c635_nof3 c635_nof4z⟩
theorem not_tile'_635 (D : CongruentDissection 635) : False :=
  not_tile_of_conditions' 635 C'_635 D

private theorem c655_sqf   : LeafSqf 655   := by decide +kernel
private theorem c655_range : LeafRange 655  := by decide +kernel
private theorem c655_ell   : LeafEll 655    := by decide +kernel
private theorem c655_nsq   : NSqChkSq 655   := by decide +kernel
private theorem c655_har   : HArithChkSq 655 := by decide +kernel
private theorem c655_r     : LeafR 655      := by decide +kernel
private theorem c655_e'    : LeafE' 655     := by decide +kernel
private theorem c655_f1    : LeafF1 655     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c655_s2    : S2ChkSq 655    := by decide +kernel
private theorem c655_s3    : S3ChkSq 655    := by decide +kernel
private theorem c655_iso   : LeafIso 655    := by decide +kernel
private theorem c655_nof2  : NoF2ChkSq 655  := by decide +kernel
private theorem c655_nof3  : NoF3ChkSq 655  := by decide +kernel
private theorem c655_nof4z : NoF4zChkSq 655 := by decide +kernel
theorem C'_655 : C' 655 :=
  ⟨c655_sqf, c655_range, c655_ell, leafNSq_of_sq c655_nsq, leafHAr_of_sq c655_har,
   c655_r, c655_e', c655_f1, leafS2_of_sq c655_s2, leafS3_of_sq c655_s3,
   c655_iso, leafR8_of_sq c655_nof2 c655_nof3 c655_nof4z⟩
theorem not_tile'_655 (D : CongruentDissection 655) : False :=
  not_tile_of_conditions' 655 C'_655 D

private theorem c665_sqf   : LeafSqf 665   := by decide +kernel
private theorem c665_range : LeafRange 665  := by decide +kernel
private theorem c665_ell   : LeafEll 665    := by decide +kernel
private theorem c665_nsq   : NSqChkSq 665   := by decide +kernel
private theorem c665_har   : HArithChkSq 665 := by decide +kernel
private theorem c665_r     : LeafR 665      := by decide +kernel
private theorem c665_e'    : LeafE' 665     := by decide +kernel
private theorem c665_f1    : LeafF1 665     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c665_s2    : S2ChkSq 665    := by decide +kernel
private theorem c665_s3    : S3ChkSq 665    := by decide +kernel
private theorem c665_iso   : LeafIso 665    := by decide +kernel
private theorem c665_nof2  : NoF2ChkSq 665  := by decide +kernel
private theorem c665_nof3  : NoF3ChkSq 665  := by decide +kernel
private theorem c665_nof4z : NoF4zChkSq 665 := by decide +kernel
theorem C'_665 : C' 665 :=
  ⟨c665_sqf, c665_range, c665_ell, leafNSq_of_sq c665_nsq, leafHAr_of_sq c665_har,
   c665_r, c665_e', c665_f1, leafS2_of_sq c665_s2, leafS3_of_sq c665_s3,
   c665_iso, leafR8_of_sq c665_nof2 c665_nof3 c665_nof4z⟩
theorem not_tile'_665 (D : CongruentDissection 665) : False :=
  not_tile_of_conditions' 665 C'_665 D

private theorem c669_sqf   : LeafSqf 669   := by decide +kernel
private theorem c669_range : LeafRange 669  := by decide +kernel
private theorem c669_ell   : LeafEll 669    := by decide +kernel
private theorem c669_nsq   : NSqChkSq 669   := by decide +kernel
private theorem c669_har   : HArithChkSq 669 := by decide +kernel
private theorem c669_r     : LeafR 669      := by decide +kernel
private theorem c669_e'    : LeafE' 669     := by decide +kernel
private theorem c669_f1    : LeafF1 669     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c669_s2    : S2ChkSq 669    := by decide +kernel
private theorem c669_s3    : S3ChkSq 669    := by decide +kernel
private theorem c669_iso   : LeafIso 669    := by decide +kernel
private theorem c669_nof2  : NoF2ChkSq 669  := by decide +kernel
private theorem c669_nof3  : NoF3ChkSq 669  := by decide +kernel
private theorem c669_nof4z : NoF4zChkSq 669 := by decide +kernel
theorem C'_669 : C' 669 :=
  ⟨c669_sqf, c669_range, c669_ell, leafNSq_of_sq c669_nsq, leafHAr_of_sq c669_har,
   c669_r, c669_e', c669_f1, leafS2_of_sq c669_s2, leafS3_of_sq c669_s3,
   c669_iso, leafR8_of_sq c669_nof2 c669_nof3 c669_nof4z⟩
theorem not_tile'_669 (D : CongruentDissection 669) : False :=
  not_tile_of_conditions' 669 C'_669 D

private theorem c679_sqf   : LeafSqf 679   := by decide +kernel
private theorem c679_range : LeafRange 679  := by decide +kernel
private theorem c679_ell   : LeafEll 679    := by decide +kernel
private theorem c679_nsq   : NSqChkSq 679   := by decide +kernel
private theorem c679_har   : HArithChkSq 679 := by decide +kernel
private theorem c679_r     : LeafR 679      := by decide +kernel
private theorem c679_e'    : LeafE' 679     := by decide +kernel
private theorem c679_f1    : LeafF1 679     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c679_s2    : S2ChkSq 679    := by decide +kernel
private theorem c679_s3    : S3ChkSq 679    := by decide +kernel
private theorem c679_iso   : LeafIso 679    := by decide +kernel
private theorem c679_nof2  : NoF2ChkSq 679  := by decide +kernel
private theorem c679_nof3  : NoF3ChkSq 679  := by decide +kernel
private theorem c679_nof4z : NoF4zChkSq 679 := by decide +kernel
theorem C'_679 : C' 679 :=
  ⟨c679_sqf, c679_range, c679_ell, leafNSq_of_sq c679_nsq, leafHAr_of_sq c679_har,
   c679_r, c679_e', c679_f1, leafS2_of_sq c679_s2, leafS3_of_sq c679_s3,
   c679_iso, leafR8_of_sq c679_nof2 c679_nof3 c679_nof4z⟩
theorem not_tile'_679 (D : CongruentDissection 679) : False :=
  not_tile_of_conditions' 679 C'_679 D

end Erdos634.Draft.AllN2

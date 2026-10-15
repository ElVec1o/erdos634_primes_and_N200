/- AllN2Check260: N = 4669, 4670, 4677, 4678, 4679
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4669_sqf   : LeafSqf 4669   := by decide +kernel
private theorem c4669_range : LeafRange 4669  := by decide +kernel
private theorem c4669_ell   : LeafEll 4669    := by decide +kernel
private theorem c4669_nsq   : NSqChkSq 4669   := by decide +kernel
private theorem c4669_har   : HArithChkSq 4669 := by decide +kernel
private theorem c4669_r     : LeafR 4669      := by decide +kernel
private theorem c4669_e'    : LeafE' 4669     := by decide +kernel
private theorem c4669_f1    : LeafF1 4669     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4669_s2    : S2ChkSq 4669    := by decide +kernel
private theorem c4669_s3    : S3ChkSq 4669    := by decide +kernel
private theorem c4669_iso   : LeafIso 4669    := by decide +kernel
private theorem c4669_nof2  : NoF2ChkSq 4669  := by decide +kernel
private theorem c4669_nof3  : NoF3ChkSq 4669  := by decide +kernel
private theorem c4669_nof4z : NoF4zChkSq 4669 := by decide +kernel
theorem C'_4669 : C' 4669 :=
  ⟨c4669_sqf, c4669_range, c4669_ell, leafNSq_of_sq c4669_nsq, leafHAr_of_sq c4669_har,
   c4669_r, c4669_e', c4669_f1, leafS2_of_sq c4669_s2, leafS3_of_sq c4669_s3,
   c4669_iso, leafR8_of_sq c4669_nof2 c4669_nof3 c4669_nof4z⟩
theorem not_tile'_4669 (D : CongruentDissection 4669) : False :=
  not_tile_of_conditions' 4669 C'_4669 D

private theorem c4670_sqf   : LeafSqf 4670   := by decide +kernel
private theorem c4670_range : LeafRange 4670  := by decide +kernel
private theorem c4670_ell   : LeafEll 4670    := by decide +kernel
private theorem c4670_nsq   : NSqChkSq 4670   := by decide +kernel
private theorem c4670_har   : HArithChkSq 4670 := by decide +kernel
private theorem c4670_r     : LeafR 4670      := by decide +kernel
private theorem c4670_e'    : LeafE' 4670     := by decide +kernel
private theorem c4670_f1    : LeafF1 4670     := Or.inl (by decide)
private theorem c4670_s2    : S2ChkSq 4670    := by decide +kernel
private theorem c4670_s3    : S3ChkSq 4670    := by decide +kernel
private theorem c4670_iso   : LeafIso 4670    := by decide +kernel
private theorem c4670_nof2  : NoF2ChkSq 4670  := by decide +kernel
private theorem c4670_nof3  : NoF3ChkSq 4670  := by decide +kernel
private theorem c4670_nof4z : NoF4zChkSq 4670 := by decide +kernel
theorem C'_4670 : C' 4670 :=
  ⟨c4670_sqf, c4670_range, c4670_ell, leafNSq_of_sq c4670_nsq, leafHAr_of_sq c4670_har,
   c4670_r, c4670_e', c4670_f1, leafS2_of_sq c4670_s2, leafS3_of_sq c4670_s3,
   c4670_iso, leafR8_of_sq c4670_nof2 c4670_nof3 c4670_nof4z⟩
theorem not_tile'_4670 (D : CongruentDissection 4670) : False :=
  not_tile_of_conditions' 4670 C'_4670 D

private theorem c4677_sqf   : LeafSqf 4677   := by decide +kernel
private theorem c4677_range : LeafRange 4677  := by decide +kernel
private theorem c4677_ell   : LeafEll 4677    := by decide +kernel
private theorem c4677_nsq   : NSqChkSq 4677   := by decide +kernel
private theorem c4677_har   : HArithChkSq 4677 := by decide +kernel
private theorem c4677_r     : LeafR 4677      := by decide +kernel
private theorem c4677_e'    : LeafE' 4677     := by decide +kernel
private theorem c4677_f1    : LeafF1 4677     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4677_s2    : S2ChkSq 4677    := by decide +kernel
private theorem c4677_s3    : S3ChkSq 4677    := by decide +kernel
private theorem c4677_iso   : LeafIso 4677    := by decide +kernel
private theorem c4677_nof2  : NoF2ChkSq 4677  := by decide +kernel
private theorem c4677_nof3  : NoF3ChkSq 4677  := by decide +kernel
private theorem c4677_nof4z : NoF4zChkSq 4677 := by decide +kernel
theorem C'_4677 : C' 4677 :=
  ⟨c4677_sqf, c4677_range, c4677_ell, leafNSq_of_sq c4677_nsq, leafHAr_of_sq c4677_har,
   c4677_r, c4677_e', c4677_f1, leafS2_of_sq c4677_s2, leafS3_of_sq c4677_s3,
   c4677_iso, leafR8_of_sq c4677_nof2 c4677_nof3 c4677_nof4z⟩
theorem not_tile'_4677 (D : CongruentDissection 4677) : False :=
  not_tile_of_conditions' 4677 C'_4677 D

private theorem c4678_sqf   : LeafSqf 4678   := by decide +kernel
private theorem c4678_range : LeafRange 4678  := by decide +kernel
private theorem c4678_ell   : LeafEll 4678    := by decide +kernel
private theorem c4678_nsq   : NSqChkSq 4678   := by decide +kernel
private theorem c4678_har   : HArithChkSq 4678 := by decide +kernel
private theorem c4678_r     : LeafR 4678      := by decide +kernel
private theorem c4678_e'    : LeafE' 4678     := by decide +kernel
private theorem c4678_f1    : LeafF1 4678     := Or.inl (by decide)
private theorem c4678_s2    : S2ChkSq 4678    := by decide +kernel
private theorem c4678_s3    : S3ChkSq 4678    := by decide +kernel
private theorem c4678_iso   : LeafIso 4678    := by decide +kernel
private theorem c4678_nof2  : NoF2ChkSq 4678  := by decide +kernel
private theorem c4678_nof3  : NoF3ChkSq 4678  := by decide +kernel
private theorem c4678_nof4z : NoF4zChkSq 4678 := by decide +kernel
theorem C'_4678 : C' 4678 :=
  ⟨c4678_sqf, c4678_range, c4678_ell, leafNSq_of_sq c4678_nsq, leafHAr_of_sq c4678_har,
   c4678_r, c4678_e', c4678_f1, leafS2_of_sq c4678_s2, leafS3_of_sq c4678_s3,
   c4678_iso, leafR8_of_sq c4678_nof2 c4678_nof3 c4678_nof4z⟩
theorem not_tile'_4678 (D : CongruentDissection 4678) : False :=
  not_tile_of_conditions' 4678 C'_4678 D

private theorem c4679_sqf   : LeafSqf 4679   := by decide +kernel
private theorem c4679_range : LeafRange 4679  := by decide +kernel
private theorem c4679_ell   : LeafEll 4679    := by decide +kernel
private theorem c4679_nsq   : NSqChkSq 4679   := by decide +kernel
private theorem c4679_har   : HArithChkSq 4679 := by decide +kernel
private theorem c4679_r     : LeafR 4679      := by decide +kernel
private theorem c4679_e'    : LeafE' 4679     := by decide +kernel
private theorem c4679_f1    : LeafF1 4679     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4679_s2    : S2ChkSq 4679    := by decide +kernel
private theorem c4679_s3    : S3ChkSq 4679    := by decide +kernel
private theorem c4679_iso   : LeafIso 4679    := by decide +kernel
private theorem c4679_nof2  : NoF2ChkSq 4679  := by decide +kernel
private theorem c4679_nof3  : NoF3ChkSq 4679  := by decide +kernel
private theorem c4679_nof4z : NoF4zChkSq 4679 := by decide +kernel
theorem C'_4679 : C' 4679 :=
  ⟨c4679_sqf, c4679_range, c4679_ell, leafNSq_of_sq c4679_nsq, leafHAr_of_sq c4679_har,
   c4679_r, c4679_e', c4679_f1, leafS2_of_sq c4679_s2, leafS3_of_sq c4679_s3,
   c4679_iso, leafR8_of_sq c4679_nof2 c4679_nof3 c4679_nof4z⟩
theorem not_tile'_4679 (D : CongruentDissection 4679) : False :=
  not_tile_of_conditions' 4679 C'_4679 D

end Erdos634.Draft.AllN2

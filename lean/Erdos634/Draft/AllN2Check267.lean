/- AllN2Check267: N = 4751, 4757, 4758, 4759, 4763
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4751_sqf   : LeafSqf 4751   := by decide +kernel
private theorem c4751_range : LeafRange 4751  := by decide +kernel
private theorem c4751_ell   : LeafEll 4751    := by decide +kernel
private theorem c4751_nsq   : NSqChkSq 4751   := by decide +kernel
private theorem c4751_har   : HArithChkSq 4751 := by decide +kernel
private theorem c4751_r     : LeafR 4751      := by decide +kernel
private theorem c4751_e'    : LeafE' 4751     := by decide +kernel
private theorem c4751_f1    : LeafF1 4751     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4751_s2    : S2ChkSq 4751    := by decide +kernel
private theorem c4751_s3    : S3ChkSq 4751    := by decide +kernel
private theorem c4751_iso   : LeafIso 4751    := by decide +kernel
private theorem c4751_nof2  : NoF2ChkSq 4751  := by decide +kernel
private theorem c4751_nof3  : NoF3ChkSq 4751  := by decide +kernel
private theorem c4751_nof4z : NoF4zChkSq 4751 := by decide +kernel
theorem C'_4751 : C' 4751 :=
  ⟨c4751_sqf, c4751_range, c4751_ell, leafNSq_of_sq c4751_nsq, leafHAr_of_sq c4751_har,
   c4751_r, c4751_e', c4751_f1, leafS2_of_sq c4751_s2, leafS3_of_sq c4751_s3,
   c4751_iso, leafR8_of_sq c4751_nof2 c4751_nof3 c4751_nof4z⟩
theorem not_tile'_4751 (D : CongruentDissection 4751) : False :=
  not_tile_of_conditions' 4751 C'_4751 D

private theorem c4757_sqf   : LeafSqf 4757   := by decide +kernel
private theorem c4757_range : LeafRange 4757  := by decide +kernel
private theorem c4757_ell   : LeafEll 4757    := by decide +kernel
private theorem c4757_nsq   : NSqChkSq 4757   := by decide +kernel
private theorem c4757_har   : HArithChkSq 4757 := by decide +kernel
private theorem c4757_r     : LeafR 4757      := by decide +kernel
private theorem c4757_e'    : LeafE' 4757     := by decide +kernel
private theorem c4757_f1    : LeafF1 4757     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4757_s2    : S2ChkSq 4757    := by decide +kernel
private theorem c4757_s3    : S3ChkSq 4757    := by decide +kernel
private theorem c4757_iso   : LeafIso 4757    := by decide +kernel
private theorem c4757_nof2  : NoF2ChkSq 4757  := by decide +kernel
private theorem c4757_nof3  : NoF3ChkSq 4757  := by decide +kernel
private theorem c4757_nof4z : NoF4zChkSq 4757 := by decide +kernel
theorem C'_4757 : C' 4757 :=
  ⟨c4757_sqf, c4757_range, c4757_ell, leafNSq_of_sq c4757_nsq, leafHAr_of_sq c4757_har,
   c4757_r, c4757_e', c4757_f1, leafS2_of_sq c4757_s2, leafS3_of_sq c4757_s3,
   c4757_iso, leafR8_of_sq c4757_nof2 c4757_nof3 c4757_nof4z⟩
theorem not_tile'_4757 (D : CongruentDissection 4757) : False :=
  not_tile_of_conditions' 4757 C'_4757 D

private theorem c4758_sqf   : LeafSqf 4758   := by decide +kernel
private theorem c4758_range : LeafRange 4758  := by decide +kernel
private theorem c4758_ell   : LeafEll 4758    := by decide +kernel
private theorem c4758_nsq   : NSqChkSq 4758   := by decide +kernel
private theorem c4758_har   : HArithChkSq 4758 := by decide +kernel
private theorem c4758_r     : LeafR 4758      := by decide +kernel
private theorem c4758_e'    : LeafE' 4758     := by decide +kernel
private theorem c4758_f1    : LeafF1 4758     := Or.inl (by decide)
private theorem c4758_s2    : S2ChkSq 4758    := by decide +kernel
private theorem c4758_s3    : S3ChkSq 4758    := by decide +kernel
private theorem c4758_iso   : LeafIso 4758    := by decide +kernel
private theorem c4758_nof2  : NoF2ChkSq 4758  := by decide +kernel
private theorem c4758_nof3  : NoF3ChkSq 4758  := by decide +kernel
private theorem c4758_nof4z : NoF4zChkSq 4758 := by decide +kernel
theorem C'_4758 : C' 4758 :=
  ⟨c4758_sqf, c4758_range, c4758_ell, leafNSq_of_sq c4758_nsq, leafHAr_of_sq c4758_har,
   c4758_r, c4758_e', c4758_f1, leafS2_of_sq c4758_s2, leafS3_of_sq c4758_s3,
   c4758_iso, leafR8_of_sq c4758_nof2 c4758_nof3 c4758_nof4z⟩
theorem not_tile'_4758 (D : CongruentDissection 4758) : False :=
  not_tile_of_conditions' 4758 C'_4758 D

private theorem c4759_sqf   : LeafSqf 4759   := by decide +kernel
private theorem c4759_range : LeafRange 4759  := by decide +kernel
private theorem c4759_ell   : LeafEll 4759    := by decide +kernel
private theorem c4759_nsq   : NSqChkSq 4759   := by decide +kernel
private theorem c4759_har   : HArithChkSq 4759 := by decide +kernel
private theorem c4759_r     : LeafR 4759      := by decide +kernel
private theorem c4759_e'    : LeafE' 4759     := by decide +kernel
private theorem c4759_f1    : LeafF1 4759     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4759_s2    : S2ChkSq 4759    := by decide +kernel
private theorem c4759_s3    : S3ChkSq 4759    := by decide +kernel
private theorem c4759_iso   : LeafIso 4759    := by decide +kernel
private theorem c4759_nof2  : NoF2ChkSq 4759  := by decide +kernel
private theorem c4759_nof3  : NoF3ChkSq 4759  := by decide +kernel
private theorem c4759_nof4z : NoF4zChkSq 4759 := by decide +kernel
theorem C'_4759 : C' 4759 :=
  ⟨c4759_sqf, c4759_range, c4759_ell, leafNSq_of_sq c4759_nsq, leafHAr_of_sq c4759_har,
   c4759_r, c4759_e', c4759_f1, leafS2_of_sq c4759_s2, leafS3_of_sq c4759_s3,
   c4759_iso, leafR8_of_sq c4759_nof2 c4759_nof3 c4759_nof4z⟩
theorem not_tile'_4759 (D : CongruentDissection 4759) : False :=
  not_tile_of_conditions' 4759 C'_4759 D

private theorem c4763_sqf   : LeafSqf 4763   := by decide +kernel
private theorem c4763_range : LeafRange 4763  := by decide +kernel
private theorem c4763_ell   : LeafEll 4763    := by decide +kernel
private theorem c4763_nsq   : NSqChkSq 4763   := by decide +kernel
private theorem c4763_har   : HArithChkSq 4763 := by decide +kernel
private theorem c4763_r     : LeafR 4763      := by decide +kernel
private theorem c4763_e'    : LeafE' 4763     := by decide +kernel
private theorem c4763_f1    : LeafF1 4763     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4763_s2    : S2ChkSq 4763    := by decide +kernel
private theorem c4763_s3    : S3ChkSq 4763    := by decide +kernel
private theorem c4763_iso   : LeafIso 4763    := by decide +kernel
private theorem c4763_nof2  : NoF2ChkSq 4763  := by decide +kernel
private theorem c4763_nof3  : NoF3ChkSq 4763  := by decide +kernel
private theorem c4763_nof4z : NoF4zChkSq 4763 := by decide +kernel
theorem C'_4763 : C' 4763 :=
  ⟨c4763_sqf, c4763_range, c4763_ell, leafNSq_of_sq c4763_nsq, leafHAr_of_sq c4763_har,
   c4763_r, c4763_e', c4763_f1, leafS2_of_sq c4763_s2, leafS3_of_sq c4763_s3,
   c4763_iso, leafR8_of_sq c4763_nof2 c4763_nof3 c4763_nof4z⟩
theorem not_tile'_4763 (D : CongruentDissection 4763) : False :=
  not_tile_of_conditions' 4763 C'_4763 D

end Erdos634.Draft.AllN2

/- AllN2Check189: N = 3755, 3758, 3763, 3766, 3767
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3755_sqf   : LeafSqf 3755   := by decide +kernel
private theorem c3755_range : LeafRange 3755  := by decide +kernel
private theorem c3755_ell   : LeafEll 3755    := by decide +kernel
private theorem c3755_nsq   : NSqChkSq 3755   := by decide +kernel
private theorem c3755_har   : HArithChkSq 3755 := by decide +kernel
private theorem c3755_r     : LeafR 3755      := by decide +kernel
private theorem c3755_e'    : LeafE' 3755     := by decide +kernel
private theorem c3755_f1    : LeafF1 3755     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3755_s2    : S2ChkSq 3755    := by decide +kernel
private theorem c3755_s3    : S3ChkSq 3755    := by decide +kernel
private theorem c3755_iso   : LeafIso 3755    := by decide +kernel
private theorem c3755_nof2  : NoF2ChkSq 3755  := by decide +kernel
private theorem c3755_nof3  : NoF3ChkSq 3755  := by decide +kernel
private theorem c3755_nof4z : NoF4zChkSq 3755 := by decide +kernel
theorem C'_3755 : C' 3755 :=
  ⟨c3755_sqf, c3755_range, c3755_ell, leafNSq_of_sq c3755_nsq, leafHAr_of_sq c3755_har,
   c3755_r, c3755_e', c3755_f1, leafS2_of_sq c3755_s2, leafS3_of_sq c3755_s3,
   c3755_iso, leafR8_of_sq c3755_nof2 c3755_nof3 c3755_nof4z⟩
theorem not_tile'_3755 (D : CongruentDissection 3755) : False :=
  not_tile_of_conditions' 3755 C'_3755 D

private theorem c3758_sqf   : LeafSqf 3758   := by decide +kernel
private theorem c3758_range : LeafRange 3758  := by decide +kernel
private theorem c3758_ell   : LeafEll 3758    := by decide +kernel
private theorem c3758_nsq   : NSqChkSq 3758   := by decide +kernel
private theorem c3758_har   : HArithChkSq 3758 := by decide +kernel
private theorem c3758_r     : LeafR 3758      := by decide +kernel
private theorem c3758_e'    : LeafE' 3758     := by decide +kernel
private theorem c3758_f1    : LeafF1 3758     := Or.inl (by decide)
private theorem c3758_s2    : S2ChkSq 3758    := by decide +kernel
private theorem c3758_s3    : S3ChkSq 3758    := by decide +kernel
private theorem c3758_iso   : LeafIso 3758    := by decide +kernel
private theorem c3758_nof2  : NoF2ChkSq 3758  := by decide +kernel
private theorem c3758_nof3  : NoF3ChkSq 3758  := by decide +kernel
private theorem c3758_nof4z : NoF4zChkSq 3758 := by decide +kernel
theorem C'_3758 : C' 3758 :=
  ⟨c3758_sqf, c3758_range, c3758_ell, leafNSq_of_sq c3758_nsq, leafHAr_of_sq c3758_har,
   c3758_r, c3758_e', c3758_f1, leafS2_of_sq c3758_s2, leafS3_of_sq c3758_s3,
   c3758_iso, leafR8_of_sq c3758_nof2 c3758_nof3 c3758_nof4z⟩
theorem not_tile'_3758 (D : CongruentDissection 3758) : False :=
  not_tile_of_conditions' 3758 C'_3758 D

private theorem c3763_sqf   : LeafSqf 3763   := by decide +kernel
private theorem c3763_range : LeafRange 3763  := by decide +kernel
private theorem c3763_ell   : LeafEll 3763    := by decide +kernel
private theorem c3763_nsq   : NSqChkSq 3763   := by decide +kernel
private theorem c3763_har   : HArithChkSq 3763 := by decide +kernel
private theorem c3763_r     : LeafR 3763      := by decide +kernel
private theorem c3763_e'    : LeafE' 3763     := by decide +kernel
private theorem c3763_f1    : LeafF1 3763     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3763_s2    : S2ChkSq 3763    := by decide +kernel
private theorem c3763_s3    : S3ChkSq 3763    := by decide +kernel
private theorem c3763_iso   : LeafIso 3763    := by decide +kernel
private theorem c3763_nof2  : NoF2ChkSq 3763  := by decide +kernel
private theorem c3763_nof3  : NoF3ChkSq 3763  := by decide +kernel
private theorem c3763_nof4z : NoF4zChkSq 3763 := by decide +kernel
theorem C'_3763 : C' 3763 :=
  ⟨c3763_sqf, c3763_range, c3763_ell, leafNSq_of_sq c3763_nsq, leafHAr_of_sq c3763_har,
   c3763_r, c3763_e', c3763_f1, leafS2_of_sq c3763_s2, leafS3_of_sq c3763_s3,
   c3763_iso, leafR8_of_sq c3763_nof2 c3763_nof3 c3763_nof4z⟩
theorem not_tile'_3763 (D : CongruentDissection 3763) : False :=
  not_tile_of_conditions' 3763 C'_3763 D

private theorem c3766_sqf   : LeafSqf 3766   := by decide +kernel
private theorem c3766_range : LeafRange 3766  := by decide +kernel
private theorem c3766_ell   : LeafEll 3766    := by decide +kernel
private theorem c3766_nsq   : NSqChkSq 3766   := by decide +kernel
private theorem c3766_har   : HArithChkSq 3766 := by decide +kernel
private theorem c3766_r     : LeafR 3766      := by decide +kernel
private theorem c3766_e'    : LeafE' 3766     := by decide +kernel
private theorem c3766_f1    : LeafF1 3766     := Or.inl (by decide)
private theorem c3766_s2    : S2ChkSq 3766    := by decide +kernel
private theorem c3766_s3    : S3ChkSq 3766    := by decide +kernel
private theorem c3766_iso   : LeafIso 3766    := by decide +kernel
private theorem c3766_nof2  : NoF2ChkSq 3766  := by decide +kernel
private theorem c3766_nof3  : NoF3ChkSq 3766  := by decide +kernel
private theorem c3766_nof4z : NoF4zChkSq 3766 := by decide +kernel
theorem C'_3766 : C' 3766 :=
  ⟨c3766_sqf, c3766_range, c3766_ell, leafNSq_of_sq c3766_nsq, leafHAr_of_sq c3766_har,
   c3766_r, c3766_e', c3766_f1, leafS2_of_sq c3766_s2, leafS3_of_sq c3766_s3,
   c3766_iso, leafR8_of_sq c3766_nof2 c3766_nof3 c3766_nof4z⟩
theorem not_tile'_3766 (D : CongruentDissection 3766) : False :=
  not_tile_of_conditions' 3766 C'_3766 D

private theorem c3767_sqf   : LeafSqf 3767   := by decide +kernel
private theorem c3767_range : LeafRange 3767  := by decide +kernel
private theorem c3767_ell   : LeafEll 3767    := by decide +kernel
private theorem c3767_nsq   : NSqChkSq 3767   := by decide +kernel
private theorem c3767_har   : HArithChkSq 3767 := by decide +kernel
private theorem c3767_r     : LeafR 3767      := by decide +kernel
private theorem c3767_e'    : LeafE' 3767     := by decide +kernel
private theorem c3767_f1    : LeafF1 3767     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3767_s2    : S2ChkSq 3767    := by decide +kernel
private theorem c3767_s3    : S3ChkSq 3767    := by decide +kernel
private theorem c3767_iso   : LeafIso 3767    := by decide +kernel
private theorem c3767_nof2  : NoF2ChkSq 3767  := by decide +kernel
private theorem c3767_nof3  : NoF3ChkSq 3767  := by decide +kernel
private theorem c3767_nof4z : NoF4zChkSq 3767 := by decide +kernel
theorem C'_3767 : C' 3767 :=
  ⟨c3767_sqf, c3767_range, c3767_ell, leafNSq_of_sq c3767_nsq, leafHAr_of_sq c3767_har,
   c3767_r, c3767_e', c3767_f1, leafS2_of_sq c3767_s2, leafS3_of_sq c3767_s3,
   c3767_iso, leafR8_of_sq c3767_nof2 c3767_nof3 c3767_nof4z⟩
theorem not_tile'_3767 (D : CongruentDissection 3767) : False :=
  not_tile_of_conditions' 3767 C'_3767 D

end Erdos634.Draft.AllN2

/- AllN2Check40: N = 1623, 1639, 1641, 1645, 1651
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1623_sqf   : LeafSqf 1623   := by decide +kernel
private theorem c1623_range : LeafRange 1623  := by decide +kernel
private theorem c1623_ell   : LeafEll 1623    := by decide +kernel
private theorem c1623_nsq   : NSqChkSq 1623   := by decide +kernel
private theorem c1623_har   : HArithChkSq 1623 := by decide +kernel
private theorem c1623_r     : LeafR 1623      := by decide +kernel
private theorem c1623_e'    : LeafE' 1623     := by decide +kernel
private theorem c1623_f1    : LeafF1 1623     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1623_s2    : S2ChkSq 1623    := by decide +kernel
private theorem c1623_s3    : S3ChkSq 1623    := by decide +kernel
private theorem c1623_iso   : LeafIso 1623    := by decide +kernel
private theorem c1623_nof2  : NoF2ChkSq 1623  := by decide +kernel
private theorem c1623_nof3  : NoF3ChkSq 1623  := by decide +kernel
private theorem c1623_nof4z : NoF4zChkSq 1623 := by decide +kernel
theorem C'_1623 : C' 1623 :=
  ⟨c1623_sqf, c1623_range, c1623_ell, leafNSq_of_sq c1623_nsq, leafHAr_of_sq c1623_har,
   c1623_r, c1623_e', c1623_f1, leafS2_of_sq c1623_s2, leafS3_of_sq c1623_s3,
   c1623_iso, leafR8_of_sq c1623_nof2 c1623_nof3 c1623_nof4z⟩
theorem not_tile'_1623 (D : CongruentDissection 1623) : False :=
  not_tile_of_conditions' 1623 C'_1623 D

private theorem c1639_sqf   : LeafSqf 1639   := by decide +kernel
private theorem c1639_range : LeafRange 1639  := by decide +kernel
private theorem c1639_ell   : LeafEll 1639    := by decide +kernel
private theorem c1639_nsq   : NSqChkSq 1639   := by decide +kernel
private theorem c1639_har   : HArithChkSq 1639 := by decide +kernel
private theorem c1639_r     : LeafR 1639      := by decide +kernel
private theorem c1639_e'    : LeafE' 1639     := by decide +kernel
private theorem c1639_f1    : LeafF1 1639     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1639_s2    : S2ChkSq 1639    := by decide +kernel
private theorem c1639_s3    : S3ChkSq 1639    := by decide +kernel
private theorem c1639_iso   : LeafIso 1639    := by decide +kernel
private theorem c1639_nof2  : NoF2ChkSq 1639  := by decide +kernel
private theorem c1639_nof3  : NoF3ChkSq 1639  := by decide +kernel
private theorem c1639_nof4z : NoF4zChkSq 1639 := by decide +kernel
theorem C'_1639 : C' 1639 :=
  ⟨c1639_sqf, c1639_range, c1639_ell, leafNSq_of_sq c1639_nsq, leafHAr_of_sq c1639_har,
   c1639_r, c1639_e', c1639_f1, leafS2_of_sq c1639_s2, leafS3_of_sq c1639_s3,
   c1639_iso, leafR8_of_sq c1639_nof2 c1639_nof3 c1639_nof4z⟩
theorem not_tile'_1639 (D : CongruentDissection 1639) : False :=
  not_tile_of_conditions' 1639 C'_1639 D

private theorem c1641_sqf   : LeafSqf 1641   := by decide +kernel
private theorem c1641_range : LeafRange 1641  := by decide +kernel
private theorem c1641_ell   : LeafEll 1641    := by decide +kernel
private theorem c1641_nsq   : NSqChkSq 1641   := by decide +kernel
private theorem c1641_har   : HArithChkSq 1641 := by decide +kernel
private theorem c1641_r     : LeafR 1641      := by decide +kernel
private theorem c1641_e'    : LeafE' 1641     := by decide +kernel
private theorem c1641_f1    : LeafF1 1641     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1641_s2    : S2ChkSq 1641    := by decide +kernel
private theorem c1641_s3    : S3ChkSq 1641    := by decide +kernel
private theorem c1641_iso   : LeafIso 1641    := by decide +kernel
private theorem c1641_nof2  : NoF2ChkSq 1641  := by decide +kernel
private theorem c1641_nof3  : NoF3ChkSq 1641  := by decide +kernel
private theorem c1641_nof4z : NoF4zChkSq 1641 := by decide +kernel
theorem C'_1641 : C' 1641 :=
  ⟨c1641_sqf, c1641_range, c1641_ell, leafNSq_of_sq c1641_nsq, leafHAr_of_sq c1641_har,
   c1641_r, c1641_e', c1641_f1, leafS2_of_sq c1641_s2, leafS3_of_sq c1641_s3,
   c1641_iso, leafR8_of_sq c1641_nof2 c1641_nof3 c1641_nof4z⟩
theorem not_tile'_1641 (D : CongruentDissection 1641) : False :=
  not_tile_of_conditions' 1641 C'_1641 D

private theorem c1645_sqf   : LeafSqf 1645   := by decide +kernel
private theorem c1645_range : LeafRange 1645  := by decide +kernel
private theorem c1645_ell   : LeafEll 1645    := by decide +kernel
private theorem c1645_nsq   : NSqChkSq 1645   := by decide +kernel
private theorem c1645_har   : HArithChkSq 1645 := by decide +kernel
private theorem c1645_r     : LeafR 1645      := by decide +kernel
private theorem c1645_e'    : LeafE' 1645     := by decide +kernel
private theorem c1645_f1    : LeafF1 1645     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1645_s2    : S2ChkSq 1645    := by decide +kernel
private theorem c1645_s3    : S3ChkSq 1645    := by decide +kernel
private theorem c1645_iso   : LeafIso 1645    := by decide +kernel
private theorem c1645_nof2  : NoF2ChkSq 1645  := by decide +kernel
private theorem c1645_nof3  : NoF3ChkSq 1645  := by decide +kernel
private theorem c1645_nof4z : NoF4zChkSq 1645 := by decide +kernel
theorem C'_1645 : C' 1645 :=
  ⟨c1645_sqf, c1645_range, c1645_ell, leafNSq_of_sq c1645_nsq, leafHAr_of_sq c1645_har,
   c1645_r, c1645_e', c1645_f1, leafS2_of_sq c1645_s2, leafS3_of_sq c1645_s3,
   c1645_iso, leafR8_of_sq c1645_nof2 c1645_nof3 c1645_nof4z⟩
theorem not_tile'_1645 (D : CongruentDissection 1645) : False :=
  not_tile_of_conditions' 1645 C'_1645 D

private theorem c1651_sqf   : LeafSqf 1651   := by decide +kernel
private theorem c1651_range : LeafRange 1651  := by decide +kernel
private theorem c1651_ell   : LeafEll 1651    := by decide +kernel
private theorem c1651_nsq   : NSqChkSq 1651   := by decide +kernel
private theorem c1651_har   : HArithChkSq 1651 := by decide +kernel
private theorem c1651_r     : LeafR 1651      := by decide +kernel
private theorem c1651_e'    : LeafE' 1651     := by decide +kernel
private theorem c1651_f1    : LeafF1 1651     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1651_s2    : S2ChkSq 1651    := by decide +kernel
private theorem c1651_s3    : S3ChkSq 1651    := by decide +kernel
private theorem c1651_iso   : LeafIso 1651    := by decide +kernel
private theorem c1651_nof2  : NoF2ChkSq 1651  := by decide +kernel
private theorem c1651_nof3  : NoF3ChkSq 1651  := by decide +kernel
private theorem c1651_nof4z : NoF4zChkSq 1651 := by decide +kernel
theorem C'_1651 : C' 1651 :=
  ⟨c1651_sqf, c1651_range, c1651_ell, leafNSq_of_sq c1651_nsq, leafHAr_of_sq c1651_har,
   c1651_r, c1651_e', c1651_f1, leafS2_of_sq c1651_s2, leafS3_of_sq c1651_s3,
   c1651_iso, leafR8_of_sq c1651_nof2 c1651_nof3 c1651_nof4z⟩
theorem not_tile'_1651 (D : CongruentDissection 1651) : False :=
  not_tile_of_conditions' 1651 C'_1651 D

end Erdos634.Draft.AllN2

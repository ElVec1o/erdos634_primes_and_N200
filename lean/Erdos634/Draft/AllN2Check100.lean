/- AllN2Check100: N = 2611, 2614, 2615, 2618, 2623
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2611_sqf   : LeafSqf 2611   := by decide +kernel
private theorem c2611_range : LeafRange 2611  := by decide +kernel
private theorem c2611_ell   : LeafEll 2611    := by decide +kernel
private theorem c2611_nsq   : NSqChkSq 2611   := by decide +kernel
private theorem c2611_har   : HArithChkSq 2611 := by decide +kernel
private theorem c2611_r     : LeafR 2611      := by decide +kernel
private theorem c2611_e'    : LeafE' 2611     := by decide +kernel
private theorem c2611_f1    : LeafF1 2611     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2611_s2    : S2ChkSq 2611    := by decide +kernel
private theorem c2611_s3    : S3ChkSq 2611    := by decide +kernel
private theorem c2611_iso   : LeafIso 2611    := by decide +kernel
private theorem c2611_nof2  : NoF2ChkSq 2611  := by decide +kernel
private theorem c2611_nof3  : NoF3ChkSq 2611  := by decide +kernel
private theorem c2611_nof4z : NoF4zChkSq 2611 := by decide +kernel
theorem C'_2611 : C' 2611 :=
  ⟨c2611_sqf, c2611_range, c2611_ell, leafNSq_of_sq c2611_nsq, leafHAr_of_sq c2611_har,
   c2611_r, c2611_e', c2611_f1, leafS2_of_sq c2611_s2, leafS3_of_sq c2611_s3,
   c2611_iso, leafR8_of_sq c2611_nof2 c2611_nof3 c2611_nof4z⟩
theorem not_tile'_2611 (D : CongruentDissection 2611) : False :=
  not_tile_of_conditions' 2611 C'_2611 D

private theorem c2614_sqf   : LeafSqf 2614   := by decide +kernel
private theorem c2614_range : LeafRange 2614  := by decide +kernel
private theorem c2614_ell   : LeafEll 2614    := by decide +kernel
private theorem c2614_nsq   : NSqChkSq 2614   := by decide +kernel
private theorem c2614_har   : HArithChkSq 2614 := by decide +kernel
private theorem c2614_r     : LeafR 2614      := by decide +kernel
private theorem c2614_e'    : LeafE' 2614     := by decide +kernel
private theorem c2614_f1    : LeafF1 2614     := Or.inl (by decide)
private theorem c2614_s2    : S2ChkSq 2614    := by decide +kernel
private theorem c2614_s3    : S3ChkSq 2614    := by decide +kernel
private theorem c2614_iso   : LeafIso 2614    := by decide +kernel
private theorem c2614_nof2  : NoF2ChkSq 2614  := by decide +kernel
private theorem c2614_nof3  : NoF3ChkSq 2614  := by decide +kernel
private theorem c2614_nof4z : NoF4zChkSq 2614 := by decide +kernel
theorem C'_2614 : C' 2614 :=
  ⟨c2614_sqf, c2614_range, c2614_ell, leafNSq_of_sq c2614_nsq, leafHAr_of_sq c2614_har,
   c2614_r, c2614_e', c2614_f1, leafS2_of_sq c2614_s2, leafS3_of_sq c2614_s3,
   c2614_iso, leafR8_of_sq c2614_nof2 c2614_nof3 c2614_nof4z⟩
theorem not_tile'_2614 (D : CongruentDissection 2614) : False :=
  not_tile_of_conditions' 2614 C'_2614 D

private theorem c2615_sqf   : LeafSqf 2615   := by decide +kernel
private theorem c2615_range : LeafRange 2615  := by decide +kernel
private theorem c2615_ell   : LeafEll 2615    := by decide +kernel
private theorem c2615_nsq   : NSqChkSq 2615   := by decide +kernel
private theorem c2615_har   : HArithChkSq 2615 := by decide +kernel
private theorem c2615_r     : LeafR 2615      := by decide +kernel
private theorem c2615_e'    : LeafE' 2615     := by decide +kernel
private theorem c2615_f1    : LeafF1 2615     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2615_s2    : S2ChkSq 2615    := by decide +kernel
private theorem c2615_s3    : S3ChkSq 2615    := by decide +kernel
private theorem c2615_iso   : LeafIso 2615    := by decide +kernel
private theorem c2615_nof2  : NoF2ChkSq 2615  := by decide +kernel
private theorem c2615_nof3  : NoF3ChkSq 2615  := by decide +kernel
private theorem c2615_nof4z : NoF4zChkSq 2615 := by decide +kernel
theorem C'_2615 : C' 2615 :=
  ⟨c2615_sqf, c2615_range, c2615_ell, leafNSq_of_sq c2615_nsq, leafHAr_of_sq c2615_har,
   c2615_r, c2615_e', c2615_f1, leafS2_of_sq c2615_s2, leafS3_of_sq c2615_s3,
   c2615_iso, leafR8_of_sq c2615_nof2 c2615_nof3 c2615_nof4z⟩
theorem not_tile'_2615 (D : CongruentDissection 2615) : False :=
  not_tile_of_conditions' 2615 C'_2615 D

private theorem c2618_sqf   : LeafSqf 2618   := by decide +kernel
private theorem c2618_range : LeafRange 2618  := by decide +kernel
private theorem c2618_ell   : LeafEll 2618    := by decide +kernel
private theorem c2618_nsq   : NSqChkSq 2618   := by decide +kernel
private theorem c2618_har   : HArithChkSq 2618 := by decide +kernel
private theorem c2618_r     : LeafR 2618      := by decide +kernel
private theorem c2618_e'    : LeafE' 2618     := by decide +kernel
private theorem c2618_f1    : LeafF1 2618     := Or.inl (by decide)
private theorem c2618_s2    : S2ChkSq 2618    := by decide +kernel
private theorem c2618_s3    : S3ChkSq 2618    := by decide +kernel
private theorem c2618_iso   : LeafIso 2618    := by decide +kernel
private theorem c2618_nof2  : NoF2ChkSq 2618  := by decide +kernel
private theorem c2618_nof3  : NoF3ChkSq 2618  := by decide +kernel
private theorem c2618_nof4z : NoF4zChkSq 2618 := by decide +kernel
theorem C'_2618 : C' 2618 :=
  ⟨c2618_sqf, c2618_range, c2618_ell, leafNSq_of_sq c2618_nsq, leafHAr_of_sq c2618_har,
   c2618_r, c2618_e', c2618_f1, leafS2_of_sq c2618_s2, leafS3_of_sq c2618_s3,
   c2618_iso, leafR8_of_sq c2618_nof2 c2618_nof3 c2618_nof4z⟩
theorem not_tile'_2618 (D : CongruentDissection 2618) : False :=
  not_tile_of_conditions' 2618 C'_2618 D

private theorem c2623_sqf   : LeafSqf 2623   := by decide +kernel
private theorem c2623_range : LeafRange 2623  := by decide +kernel
private theorem c2623_ell   : LeafEll 2623    := by decide +kernel
private theorem c2623_nsq   : NSqChkSq 2623   := by decide +kernel
private theorem c2623_har   : HArithChkSq 2623 := by decide +kernel
private theorem c2623_r     : LeafR 2623      := by decide +kernel
private theorem c2623_e'    : LeafE' 2623     := by decide +kernel
private theorem c2623_f1    : LeafF1 2623     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2623_s2    : S2ChkSq 2623    := by decide +kernel
private theorem c2623_s3    : S3ChkSq 2623    := by decide +kernel
private theorem c2623_iso   : LeafIso 2623    := by decide +kernel
private theorem c2623_nof2  : NoF2ChkSq 2623  := by decide +kernel
private theorem c2623_nof3  : NoF3ChkSq 2623  := by decide +kernel
private theorem c2623_nof4z : NoF4zChkSq 2623 := by decide +kernel
theorem C'_2623 : C' 2623 :=
  ⟨c2623_sqf, c2623_range, c2623_ell, leafNSq_of_sq c2623_nsq, leafHAr_of_sq c2623_har,
   c2623_r, c2623_e', c2623_f1, leafS2_of_sq c2623_s2, leafS3_of_sq c2623_s3,
   c2623_iso, leafR8_of_sq c2623_nof2 c2623_nof3 c2623_nof4z⟩
theorem not_tile'_2623 (D : CongruentDissection 2623) : False :=
  not_tile_of_conditions' 2623 C'_2623 D

end Erdos634.Draft.AllN2

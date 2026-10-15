/- AllN2Check42: N = 1689, 1703, 1705, 1707, 1713
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1689_sqf   : LeafSqf 1689   := by decide +kernel
private theorem c1689_range : LeafRange 1689  := by decide +kernel
private theorem c1689_ell   : LeafEll 1689    := by decide +kernel
private theorem c1689_nsq   : NSqChkSq 1689   := by decide +kernel
private theorem c1689_har   : HArithChkSq 1689 := by decide +kernel
private theorem c1689_r     : LeafR 1689      := by decide +kernel
private theorem c1689_e'    : LeafE' 1689     := by decide +kernel
private theorem c1689_f1    : LeafF1 1689     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1689_s2    : S2ChkSq 1689    := by decide +kernel
private theorem c1689_s3    : S3ChkSq 1689    := by decide +kernel
private theorem c1689_iso   : LeafIso 1689    := by decide +kernel
private theorem c1689_nof2  : NoF2ChkSq 1689  := by decide +kernel
private theorem c1689_nof3  : NoF3ChkSq 1689  := by decide +kernel
private theorem c1689_nof4z : NoF4zChkSq 1689 := by decide +kernel
theorem C'_1689 : C' 1689 :=
  ⟨c1689_sqf, c1689_range, c1689_ell, leafNSq_of_sq c1689_nsq, leafHAr_of_sq c1689_har,
   c1689_r, c1689_e', c1689_f1, leafS2_of_sq c1689_s2, leafS3_of_sq c1689_s3,
   c1689_iso, leafR8_of_sq c1689_nof2 c1689_nof3 c1689_nof4z⟩
theorem not_tile'_1689 (D : CongruentDissection 1689) : False :=
  not_tile_of_conditions' 1689 C'_1689 D

private theorem c1703_sqf   : LeafSqf 1703   := by decide +kernel
private theorem c1703_range : LeafRange 1703  := by decide +kernel
private theorem c1703_ell   : LeafEll 1703    := by decide +kernel
private theorem c1703_nsq   : NSqChkSq 1703   := by decide +kernel
private theorem c1703_har   : HArithChkSq 1703 := by decide +kernel
private theorem c1703_r     : LeafR 1703      := by decide +kernel
private theorem c1703_e'    : LeafE' 1703     := by decide +kernel
private theorem c1703_f1    : LeafF1 1703     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1703_s2    : S2ChkSq 1703    := by decide +kernel
private theorem c1703_s3    : S3ChkSq 1703    := by decide +kernel
private theorem c1703_iso   : LeafIso 1703    := by decide +kernel
private theorem c1703_nof2  : NoF2ChkSq 1703  := by decide +kernel
private theorem c1703_nof3  : NoF3ChkSq 1703  := by decide +kernel
private theorem c1703_nof4z : NoF4zChkSq 1703 := by decide +kernel
theorem C'_1703 : C' 1703 :=
  ⟨c1703_sqf, c1703_range, c1703_ell, leafNSq_of_sq c1703_nsq, leafHAr_of_sq c1703_har,
   c1703_r, c1703_e', c1703_f1, leafS2_of_sq c1703_s2, leafS3_of_sq c1703_s3,
   c1703_iso, leafR8_of_sq c1703_nof2 c1703_nof3 c1703_nof4z⟩
theorem not_tile'_1703 (D : CongruentDissection 1703) : False :=
  not_tile_of_conditions' 1703 C'_1703 D

private theorem c1705_sqf   : LeafSqf 1705   := by decide +kernel
private theorem c1705_range : LeafRange 1705  := by decide +kernel
private theorem c1705_ell   : LeafEll 1705    := by decide +kernel
private theorem c1705_nsq   : NSqChkSq 1705   := by decide +kernel
private theorem c1705_har   : HArithChkSq 1705 := by decide +kernel
private theorem c1705_r     : LeafR 1705      := by decide +kernel
private theorem c1705_e'    : LeafE' 1705     := by decide +kernel
private theorem c1705_f1    : LeafF1 1705     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1705_s2    : S2ChkSq 1705    := by decide +kernel
private theorem c1705_s3    : S3ChkSq 1705    := by decide +kernel
private theorem c1705_iso   : LeafIso 1705    := by decide +kernel
private theorem c1705_nof2  : NoF2ChkSq 1705  := by decide +kernel
private theorem c1705_nof3  : NoF3ChkSq 1705  := by decide +kernel
private theorem c1705_nof4z : NoF4zChkSq 1705 := by decide +kernel
theorem C'_1705 : C' 1705 :=
  ⟨c1705_sqf, c1705_range, c1705_ell, leafNSq_of_sq c1705_nsq, leafHAr_of_sq c1705_har,
   c1705_r, c1705_e', c1705_f1, leafS2_of_sq c1705_s2, leafS3_of_sq c1705_s3,
   c1705_iso, leafR8_of_sq c1705_nof2 c1705_nof3 c1705_nof4z⟩
theorem not_tile'_1705 (D : CongruentDissection 1705) : False :=
  not_tile_of_conditions' 1705 C'_1705 D

private theorem c1707_sqf   : LeafSqf 1707   := by decide +kernel
private theorem c1707_range : LeafRange 1707  := by decide +kernel
private theorem c1707_ell   : LeafEll 1707    := by decide +kernel
private theorem c1707_nsq   : NSqChkSq 1707   := by decide +kernel
private theorem c1707_har   : HArithChkSq 1707 := by decide +kernel
private theorem c1707_r     : LeafR 1707      := by decide +kernel
private theorem c1707_e'    : LeafE' 1707     := by decide +kernel
private theorem c1707_f1    : LeafF1 1707     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1707_s2    : S2ChkSq 1707    := by decide +kernel
private theorem c1707_s3    : S3ChkSq 1707    := by decide +kernel
private theorem c1707_iso   : LeafIso 1707    := by decide +kernel
private theorem c1707_nof2  : NoF2ChkSq 1707  := by decide +kernel
private theorem c1707_nof3  : NoF3ChkSq 1707  := by decide +kernel
private theorem c1707_nof4z : NoF4zChkSq 1707 := by decide +kernel
theorem C'_1707 : C' 1707 :=
  ⟨c1707_sqf, c1707_range, c1707_ell, leafNSq_of_sq c1707_nsq, leafHAr_of_sq c1707_har,
   c1707_r, c1707_e', c1707_f1, leafS2_of_sq c1707_s2, leafS3_of_sq c1707_s3,
   c1707_iso, leafR8_of_sq c1707_nof2 c1707_nof3 c1707_nof4z⟩
theorem not_tile'_1707 (D : CongruentDissection 1707) : False :=
  not_tile_of_conditions' 1707 C'_1707 D

private theorem c1713_sqf   : LeafSqf 1713   := by decide +kernel
private theorem c1713_range : LeafRange 1713  := by decide +kernel
private theorem c1713_ell   : LeafEll 1713    := by decide +kernel
private theorem c1713_nsq   : NSqChkSq 1713   := by decide +kernel
private theorem c1713_har   : HArithChkSq 1713 := by decide +kernel
private theorem c1713_r     : LeafR 1713      := by decide +kernel
private theorem c1713_e'    : LeafE' 1713     := by decide +kernel
private theorem c1713_f1    : LeafF1 1713     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1713_s2    : S2ChkSq 1713    := by decide +kernel
private theorem c1713_s3    : S3ChkSq 1713    := by decide +kernel
private theorem c1713_iso   : LeafIso 1713    := by decide +kernel
private theorem c1713_nof2  : NoF2ChkSq 1713  := by decide +kernel
private theorem c1713_nof3  : NoF3ChkSq 1713  := by decide +kernel
private theorem c1713_nof4z : NoF4zChkSq 1713 := by decide +kernel
theorem C'_1713 : C' 1713 :=
  ⟨c1713_sqf, c1713_range, c1713_ell, leafNSq_of_sq c1713_nsq, leafHAr_of_sq c1713_har,
   c1713_r, c1713_e', c1713_f1, leafS2_of_sq c1713_s2, leafS3_of_sq c1713_s3,
   c1713_iso, leafR8_of_sq c1713_nof2 c1713_nof3 c1713_nof4z⟩
theorem not_tile'_1713 (D : CongruentDissection 1713) : False :=
  not_tile_of_conditions' 1713 C'_1713 D

end Erdos634.Draft.AllN2

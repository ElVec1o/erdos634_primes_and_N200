/- AllN2Check39: N = 1569, 1589, 1595, 1603, 1615
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1569_sqf   : LeafSqf 1569   := by decide +kernel
private theorem c1569_range : LeafRange 1569  := by decide +kernel
private theorem c1569_ell   : LeafEll 1569    := by decide +kernel
private theorem c1569_nsq   : NSqChkSq 1569   := by decide +kernel
private theorem c1569_har   : HArithChkSq 1569 := by decide +kernel
private theorem c1569_r     : LeafR 1569      := by decide +kernel
private theorem c1569_e'    : LeafE' 1569     := by decide +kernel
private theorem c1569_f1    : LeafF1 1569     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1569_s2    : S2ChkSq 1569    := by decide +kernel
private theorem c1569_s3    : S3ChkSq 1569    := by decide +kernel
private theorem c1569_iso   : LeafIso 1569    := by decide +kernel
private theorem c1569_nof2  : NoF2ChkSq 1569  := by decide +kernel
private theorem c1569_nof3  : NoF3ChkSq 1569  := by decide +kernel
private theorem c1569_nof4z : NoF4zChkSq 1569 := by decide +kernel
theorem C'_1569 : C' 1569 :=
  ⟨c1569_sqf, c1569_range, c1569_ell, leafNSq_of_sq c1569_nsq, leafHAr_of_sq c1569_har,
   c1569_r, c1569_e', c1569_f1, leafS2_of_sq c1569_s2, leafS3_of_sq c1569_s3,
   c1569_iso, leafR8_of_sq c1569_nof2 c1569_nof3 c1569_nof4z⟩
theorem not_tile'_1569 (D : CongruentDissection 1569) : False :=
  not_tile_of_conditions' 1569 C'_1569 D

private theorem c1589_sqf   : LeafSqf 1589   := by decide +kernel
private theorem c1589_range : LeafRange 1589  := by decide +kernel
private theorem c1589_ell   : LeafEll 1589    := by decide +kernel
private theorem c1589_nsq   : NSqChkSq 1589   := by decide +kernel
private theorem c1589_har   : HArithChkSq 1589 := by decide +kernel
private theorem c1589_r     : LeafR 1589      := by decide +kernel
private theorem c1589_e'    : LeafE' 1589     := by decide +kernel
private theorem c1589_f1    : LeafF1 1589     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1589_s2    : S2ChkSq 1589    := by decide +kernel
private theorem c1589_s3    : S3ChkSq 1589    := by decide +kernel
private theorem c1589_iso   : LeafIso 1589    := by decide +kernel
private theorem c1589_nof2  : NoF2ChkSq 1589  := by decide +kernel
private theorem c1589_nof3  : NoF3ChkSq 1589  := by decide +kernel
private theorem c1589_nof4z : NoF4zChkSq 1589 := by decide +kernel
theorem C'_1589 : C' 1589 :=
  ⟨c1589_sqf, c1589_range, c1589_ell, leafNSq_of_sq c1589_nsq, leafHAr_of_sq c1589_har,
   c1589_r, c1589_e', c1589_f1, leafS2_of_sq c1589_s2, leafS3_of_sq c1589_s3,
   c1589_iso, leafR8_of_sq c1589_nof2 c1589_nof3 c1589_nof4z⟩
theorem not_tile'_1589 (D : CongruentDissection 1589) : False :=
  not_tile_of_conditions' 1589 C'_1589 D

private theorem c1595_sqf   : LeafSqf 1595   := by decide +kernel
private theorem c1595_range : LeafRange 1595  := by decide +kernel
private theorem c1595_ell   : LeafEll 1595    := by decide +kernel
private theorem c1595_nsq   : NSqChkSq 1595   := by decide +kernel
private theorem c1595_har   : HArithChkSq 1595 := by decide +kernel
private theorem c1595_r     : LeafR 1595      := by decide +kernel
private theorem c1595_e'    : LeafE' 1595     := by decide +kernel
private theorem c1595_f1    : LeafF1 1595     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1595_s2    : S2ChkSq 1595    := by decide +kernel
private theorem c1595_s3    : S3ChkSq 1595    := by decide +kernel
private theorem c1595_iso   : LeafIso 1595    := by decide +kernel
private theorem c1595_nof2  : NoF2ChkSq 1595  := by decide +kernel
private theorem c1595_nof3  : NoF3ChkSq 1595  := by decide +kernel
private theorem c1595_nof4z : NoF4zChkSq 1595 := by decide +kernel
theorem C'_1595 : C' 1595 :=
  ⟨c1595_sqf, c1595_range, c1595_ell, leafNSq_of_sq c1595_nsq, leafHAr_of_sq c1595_har,
   c1595_r, c1595_e', c1595_f1, leafS2_of_sq c1595_s2, leafS3_of_sq c1595_s3,
   c1595_iso, leafR8_of_sq c1595_nof2 c1595_nof3 c1595_nof4z⟩
theorem not_tile'_1595 (D : CongruentDissection 1595) : False :=
  not_tile_of_conditions' 1595 C'_1595 D

private theorem c1603_sqf   : LeafSqf 1603   := by decide +kernel
private theorem c1603_range : LeafRange 1603  := by decide +kernel
private theorem c1603_ell   : LeafEll 1603    := by decide +kernel
private theorem c1603_nsq   : NSqChkSq 1603   := by decide +kernel
private theorem c1603_har   : HArithChkSq 1603 := by decide +kernel
private theorem c1603_r     : LeafR 1603      := by decide +kernel
private theorem c1603_e'    : LeafE' 1603     := by decide +kernel
private theorem c1603_f1    : LeafF1 1603     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1603_s2    : S2ChkSq 1603    := by decide +kernel
private theorem c1603_s3    : S3ChkSq 1603    := by decide +kernel
private theorem c1603_iso   : LeafIso 1603    := by decide +kernel
private theorem c1603_nof2  : NoF2ChkSq 1603  := by decide +kernel
private theorem c1603_nof3  : NoF3ChkSq 1603  := by decide +kernel
private theorem c1603_nof4z : NoF4zChkSq 1603 := by decide +kernel
theorem C'_1603 : C' 1603 :=
  ⟨c1603_sqf, c1603_range, c1603_ell, leafNSq_of_sq c1603_nsq, leafHAr_of_sq c1603_har,
   c1603_r, c1603_e', c1603_f1, leafS2_of_sq c1603_s2, leafS3_of_sq c1603_s3,
   c1603_iso, leafR8_of_sq c1603_nof2 c1603_nof3 c1603_nof4z⟩
theorem not_tile'_1603 (D : CongruentDissection 1603) : False :=
  not_tile_of_conditions' 1603 C'_1603 D

private theorem c1615_sqf   : LeafSqf 1615   := by decide +kernel
private theorem c1615_range : LeafRange 1615  := by decide +kernel
private theorem c1615_ell   : LeafEll 1615    := by decide +kernel
private theorem c1615_nsq   : NSqChkSq 1615   := by decide +kernel
private theorem c1615_har   : HArithChkSq 1615 := by decide +kernel
private theorem c1615_r     : LeafR 1615      := by decide +kernel
private theorem c1615_e'    : LeafE' 1615     := by decide +kernel
private theorem c1615_f1    : LeafF1 1615     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1615_s2    : S2ChkSq 1615    := by decide +kernel
private theorem c1615_s3    : S3ChkSq 1615    := by decide +kernel
private theorem c1615_iso   : LeafIso 1615    := by decide +kernel
private theorem c1615_nof2  : NoF2ChkSq 1615  := by decide +kernel
private theorem c1615_nof3  : NoF3ChkSq 1615  := by decide +kernel
private theorem c1615_nof4z : NoF4zChkSq 1615 := by decide +kernel
theorem C'_1615 : C' 1615 :=
  ⟨c1615_sqf, c1615_range, c1615_ell, leafNSq_of_sq c1615_nsq, leafHAr_of_sq c1615_har,
   c1615_r, c1615_e', c1615_f1, leafS2_of_sq c1615_s2, leafS3_of_sq c1615_s3,
   c1615_iso, leafR8_of_sq c1615_nof2 c1615_nof3 c1615_nof4z⟩
theorem not_tile'_1615 (D : CongruentDissection 1615) : False :=
  not_tile_of_conditions' 1615 C'_1615 D

end Erdos634.Draft.AllN2

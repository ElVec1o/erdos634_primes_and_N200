/- AllN2Check43: N = 1727, 1731, 1735, 1757, 1761
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1727_sqf   : LeafSqf 1727   := by decide +kernel
private theorem c1727_range : LeafRange 1727  := by decide +kernel
private theorem c1727_ell   : LeafEll 1727    := by decide +kernel
private theorem c1727_nsq   : NSqChkSq 1727   := by decide +kernel
private theorem c1727_har   : HArithChkSq 1727 := by decide +kernel
private theorem c1727_r     : LeafR 1727      := by decide +kernel
private theorem c1727_e'    : LeafE' 1727     := by decide +kernel
private theorem c1727_f1    : LeafF1 1727     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1727_s2    : S2ChkSq 1727    := by decide +kernel
private theorem c1727_s3    : S3ChkSq 1727    := by decide +kernel
private theorem c1727_iso   : LeafIso 1727    := by decide +kernel
private theorem c1727_nof2  : NoF2ChkSq 1727  := by decide +kernel
private theorem c1727_nof3  : NoF3ChkSq 1727  := by decide +kernel
private theorem c1727_nof4z : NoF4zChkSq 1727 := by decide +kernel
theorem C'_1727 : C' 1727 :=
  ⟨c1727_sqf, c1727_range, c1727_ell, leafNSq_of_sq c1727_nsq, leafHAr_of_sq c1727_har,
   c1727_r, c1727_e', c1727_f1, leafS2_of_sq c1727_s2, leafS3_of_sq c1727_s3,
   c1727_iso, leafR8_of_sq c1727_nof2 c1727_nof3 c1727_nof4z⟩
theorem not_tile'_1727 (D : CongruentDissection 1727) : False :=
  not_tile_of_conditions' 1727 C'_1727 D

private theorem c1731_sqf   : LeafSqf 1731   := by decide +kernel
private theorem c1731_range : LeafRange 1731  := by decide +kernel
private theorem c1731_ell   : LeafEll 1731    := by decide +kernel
private theorem c1731_nsq   : NSqChkSq 1731   := by decide +kernel
private theorem c1731_har   : HArithChkSq 1731 := by decide +kernel
private theorem c1731_r     : LeafR 1731      := by decide +kernel
private theorem c1731_e'    : LeafE' 1731     := by decide +kernel
private theorem c1731_f1    : LeafF1 1731     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1731_s2    : S2ChkSq 1731    := by decide +kernel
private theorem c1731_s3    : S3ChkSq 1731    := by decide +kernel
private theorem c1731_iso   : LeafIso 1731    := by decide +kernel
private theorem c1731_nof2  : NoF2ChkSq 1731  := by decide +kernel
private theorem c1731_nof3  : NoF3ChkSq 1731  := by decide +kernel
private theorem c1731_nof4z : NoF4zChkSq 1731 := by decide +kernel
theorem C'_1731 : C' 1731 :=
  ⟨c1731_sqf, c1731_range, c1731_ell, leafNSq_of_sq c1731_nsq, leafHAr_of_sq c1731_har,
   c1731_r, c1731_e', c1731_f1, leafS2_of_sq c1731_s2, leafS3_of_sq c1731_s3,
   c1731_iso, leafR8_of_sq c1731_nof2 c1731_nof3 c1731_nof4z⟩
theorem not_tile'_1731 (D : CongruentDissection 1731) : False :=
  not_tile_of_conditions' 1731 C'_1731 D

private theorem c1735_sqf   : LeafSqf 1735   := by decide +kernel
private theorem c1735_range : LeafRange 1735  := by decide +kernel
private theorem c1735_ell   : LeafEll 1735    := by decide +kernel
private theorem c1735_nsq   : NSqChkSq 1735   := by decide +kernel
private theorem c1735_har   : HArithChkSq 1735 := by decide +kernel
private theorem c1735_r     : LeafR 1735      := by decide +kernel
private theorem c1735_e'    : LeafE' 1735     := by decide +kernel
private theorem c1735_f1    : LeafF1 1735     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1735_s2    : S2ChkSq 1735    := by decide +kernel
private theorem c1735_s3    : S3ChkSq 1735    := by decide +kernel
private theorem c1735_iso   : LeafIso 1735    := by decide +kernel
private theorem c1735_nof2  : NoF2ChkSq 1735  := by decide +kernel
private theorem c1735_nof3  : NoF3ChkSq 1735  := by decide +kernel
private theorem c1735_nof4z : NoF4zChkSq 1735 := by decide +kernel
theorem C'_1735 : C' 1735 :=
  ⟨c1735_sqf, c1735_range, c1735_ell, leafNSq_of_sq c1735_nsq, leafHAr_of_sq c1735_har,
   c1735_r, c1735_e', c1735_f1, leafS2_of_sq c1735_s2, leafS3_of_sq c1735_s3,
   c1735_iso, leafR8_of_sq c1735_nof2 c1735_nof3 c1735_nof4z⟩
theorem not_tile'_1735 (D : CongruentDissection 1735) : False :=
  not_tile_of_conditions' 1735 C'_1735 D

private theorem c1757_sqf   : LeafSqf 1757   := by decide +kernel
private theorem c1757_range : LeafRange 1757  := by decide +kernel
private theorem c1757_ell   : LeafEll 1757    := by decide +kernel
private theorem c1757_nsq   : NSqChkSq 1757   := by decide +kernel
private theorem c1757_har   : HArithChkSq 1757 := by decide +kernel
private theorem c1757_r     : LeafR 1757      := by decide +kernel
private theorem c1757_e'    : LeafE' 1757     := by decide +kernel
private theorem c1757_f1    : LeafF1 1757     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1757_s2    : S2ChkSq 1757    := by decide +kernel
private theorem c1757_s3    : S3ChkSq 1757    := by decide +kernel
private theorem c1757_iso   : LeafIso 1757    := by decide +kernel
private theorem c1757_nof2  : NoF2ChkSq 1757  := by decide +kernel
private theorem c1757_nof3  : NoF3ChkSq 1757  := by decide +kernel
private theorem c1757_nof4z : NoF4zChkSq 1757 := by decide +kernel
theorem C'_1757 : C' 1757 :=
  ⟨c1757_sqf, c1757_range, c1757_ell, leafNSq_of_sq c1757_nsq, leafHAr_of_sq c1757_har,
   c1757_r, c1757_e', c1757_f1, leafS2_of_sq c1757_s2, leafS3_of_sq c1757_s3,
   c1757_iso, leafR8_of_sq c1757_nof2 c1757_nof3 c1757_nof4z⟩
theorem not_tile'_1757 (D : CongruentDissection 1757) : False :=
  not_tile_of_conditions' 1757 C'_1757 D

private theorem c1761_sqf   : LeafSqf 1761   := by decide +kernel
private theorem c1761_range : LeafRange 1761  := by decide +kernel
private theorem c1761_ell   : LeafEll 1761    := by decide +kernel
private theorem c1761_nsq   : NSqChkSq 1761   := by decide +kernel
private theorem c1761_har   : HArithChkSq 1761 := by decide +kernel
private theorem c1761_r     : LeafR 1761      := by decide +kernel
private theorem c1761_e'    : LeafE' 1761     := by decide +kernel
private theorem c1761_f1    : LeafF1 1761     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1761_s2    : S2ChkSq 1761    := by decide +kernel
private theorem c1761_s3    : S3ChkSq 1761    := by decide +kernel
private theorem c1761_iso   : LeafIso 1761    := by decide +kernel
private theorem c1761_nof2  : NoF2ChkSq 1761  := by decide +kernel
private theorem c1761_nof3  : NoF3ChkSq 1761  := by decide +kernel
private theorem c1761_nof4z : NoF4zChkSq 1761 := by decide +kernel
theorem C'_1761 : C' 1761 :=
  ⟨c1761_sqf, c1761_range, c1761_ell, leafNSq_of_sq c1761_nsq, leafHAr_of_sq c1761_har,
   c1761_r, c1761_e', c1761_f1, leafS2_of_sq c1761_s2, leafS3_of_sq c1761_s3,
   c1761_iso, leafR8_of_sq c1761_nof2 c1761_nof3 c1761_nof4z⟩
theorem not_tile'_1761 (D : CongruentDissection 1761) : False :=
  not_tile_of_conditions' 1761 C'_1761 D

end Erdos634.Draft.AllN2

/- AllN2Check45: N = 1799, 1803, 1807, 1821, 1835
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1799_sqf   : LeafSqf 1799   := by decide +kernel
private theorem c1799_range : LeafRange 1799  := by decide +kernel
private theorem c1799_ell   : LeafEll 1799    := by decide +kernel
private theorem c1799_nsq   : NSqChkSq 1799   := by decide +kernel
private theorem c1799_har   : HArithChkSq 1799 := by decide +kernel
private theorem c1799_r     : LeafR 1799      := by decide +kernel
private theorem c1799_e'    : LeafE' 1799     := by decide +kernel
private theorem c1799_f1    : LeafF1 1799     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1799_s2    : S2ChkSq 1799    := by decide +kernel
private theorem c1799_s3    : S3ChkSq 1799    := by decide +kernel
private theorem c1799_iso   : LeafIso 1799    := by decide +kernel
private theorem c1799_nof2  : NoF2ChkSq 1799  := by decide +kernel
private theorem c1799_nof3  : NoF3ChkSq 1799  := by decide +kernel
private theorem c1799_nof4z : NoF4zChkSq 1799 := by decide +kernel
theorem C'_1799 : C' 1799 :=
  ⟨c1799_sqf, c1799_range, c1799_ell, leafNSq_of_sq c1799_nsq, leafHAr_of_sq c1799_har,
   c1799_r, c1799_e', c1799_f1, leafS2_of_sq c1799_s2, leafS3_of_sq c1799_s3,
   c1799_iso, leafR8_of_sq c1799_nof2 c1799_nof3 c1799_nof4z⟩
theorem not_tile'_1799 (D : CongruentDissection 1799) : False :=
  not_tile_of_conditions' 1799 C'_1799 D

private theorem c1803_sqf   : LeafSqf 1803   := by decide +kernel
private theorem c1803_range : LeafRange 1803  := by decide +kernel
private theorem c1803_ell   : LeafEll 1803    := by decide +kernel
private theorem c1803_nsq   : NSqChkSq 1803   := by decide +kernel
private theorem c1803_har   : HArithChkSq 1803 := by decide +kernel
private theorem c1803_r     : LeafR 1803      := by decide +kernel
private theorem c1803_e'    : LeafE' 1803     := by decide +kernel
private theorem c1803_f1    : LeafF1 1803     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1803_s2    : S2ChkSq 1803    := by decide +kernel
private theorem c1803_s3    : S3ChkSq 1803    := by decide +kernel
private theorem c1803_iso   : LeafIso 1803    := by decide +kernel
private theorem c1803_nof2  : NoF2ChkSq 1803  := by decide +kernel
private theorem c1803_nof3  : NoF3ChkSq 1803  := by decide +kernel
private theorem c1803_nof4z : NoF4zChkSq 1803 := by decide +kernel
theorem C'_1803 : C' 1803 :=
  ⟨c1803_sqf, c1803_range, c1803_ell, leafNSq_of_sq c1803_nsq, leafHAr_of_sq c1803_har,
   c1803_r, c1803_e', c1803_f1, leafS2_of_sq c1803_s2, leafS3_of_sq c1803_s3,
   c1803_iso, leafR8_of_sq c1803_nof2 c1803_nof3 c1803_nof4z⟩
theorem not_tile'_1803 (D : CongruentDissection 1803) : False :=
  not_tile_of_conditions' 1803 C'_1803 D

private theorem c1807_sqf   : LeafSqf 1807   := by decide +kernel
private theorem c1807_range : LeafRange 1807  := by decide +kernel
private theorem c1807_ell   : LeafEll 1807    := by decide +kernel
private theorem c1807_nsq   : NSqChkSq 1807   := by decide +kernel
private theorem c1807_har   : HArithChkSq 1807 := by decide +kernel
private theorem c1807_r     : LeafR 1807      := by decide +kernel
private theorem c1807_e'    : LeafE' 1807     := by decide +kernel
private theorem c1807_f1    : LeafF1 1807     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1807_s2    : S2ChkSq 1807    := by decide +kernel
private theorem c1807_s3    : S3ChkSq 1807    := by decide +kernel
private theorem c1807_iso   : LeafIso 1807    := by decide +kernel
private theorem c1807_nof2  : NoF2ChkSq 1807  := by decide +kernel
private theorem c1807_nof3  : NoF3ChkSq 1807  := by decide +kernel
private theorem c1807_nof4z : NoF4zChkSq 1807 := by decide +kernel
theorem C'_1807 : C' 1807 :=
  ⟨c1807_sqf, c1807_range, c1807_ell, leafNSq_of_sq c1807_nsq, leafHAr_of_sq c1807_har,
   c1807_r, c1807_e', c1807_f1, leafS2_of_sq c1807_s2, leafS3_of_sq c1807_s3,
   c1807_iso, leafR8_of_sq c1807_nof2 c1807_nof3 c1807_nof4z⟩
theorem not_tile'_1807 (D : CongruentDissection 1807) : False :=
  not_tile_of_conditions' 1807 C'_1807 D

private theorem c1821_sqf   : LeafSqf 1821   := by decide +kernel
private theorem c1821_range : LeafRange 1821  := by decide +kernel
private theorem c1821_ell   : LeafEll 1821    := by decide +kernel
private theorem c1821_nsq   : NSqChkSq 1821   := by decide +kernel
private theorem c1821_har   : HArithChkSq 1821 := by decide +kernel
private theorem c1821_r     : LeafR 1821      := by decide +kernel
private theorem c1821_e'    : LeafE' 1821     := by decide +kernel
private theorem c1821_f1    : LeafF1 1821     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1821_s2    : S2ChkSq 1821    := by decide +kernel
private theorem c1821_s3    : S3ChkSq 1821    := by decide +kernel
private theorem c1821_iso   : LeafIso 1821    := by decide +kernel
private theorem c1821_nof2  : NoF2ChkSq 1821  := by decide +kernel
private theorem c1821_nof3  : NoF3ChkSq 1821  := by decide +kernel
private theorem c1821_nof4z : NoF4zChkSq 1821 := by decide +kernel
theorem C'_1821 : C' 1821 :=
  ⟨c1821_sqf, c1821_range, c1821_ell, leafNSq_of_sq c1821_nsq, leafHAr_of_sq c1821_har,
   c1821_r, c1821_e', c1821_f1, leafS2_of_sq c1821_s2, leafS3_of_sq c1821_s3,
   c1821_iso, leafR8_of_sq c1821_nof2 c1821_nof3 c1821_nof4z⟩
theorem not_tile'_1821 (D : CongruentDissection 1821) : False :=
  not_tile_of_conditions' 1821 C'_1821 D

private theorem c1835_sqf   : LeafSqf 1835   := by decide +kernel
private theorem c1835_range : LeafRange 1835  := by decide +kernel
private theorem c1835_ell   : LeafEll 1835    := by decide +kernel
private theorem c1835_nsq   : NSqChkSq 1835   := by decide +kernel
private theorem c1835_har   : HArithChkSq 1835 := by decide +kernel
private theorem c1835_r     : LeafR 1835      := by decide +kernel
private theorem c1835_e'    : LeafE' 1835     := by decide +kernel
private theorem c1835_f1    : LeafF1 1835     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1835_s2    : S2ChkSq 1835    := by decide +kernel
private theorem c1835_s3    : S3ChkSq 1835    := by decide +kernel
private theorem c1835_iso   : LeafIso 1835    := by decide +kernel
private theorem c1835_nof2  : NoF2ChkSq 1835  := by decide +kernel
private theorem c1835_nof3  : NoF3ChkSq 1835  := by decide +kernel
private theorem c1835_nof4z : NoF4zChkSq 1835 := by decide +kernel
theorem C'_1835 : C' 1835 :=
  ⟨c1835_sqf, c1835_range, c1835_ell, leafNSq_of_sq c1835_nsq, leafHAr_of_sq c1835_har,
   c1835_r, c1835_e', c1835_f1, leafS2_of_sq c1835_s2, leafS3_of_sq c1835_s3,
   c1835_iso, leafR8_of_sq c1835_nof2 c1835_nof3 c1835_nof4z⟩
theorem not_tile'_1835 (D : CongruentDissection 1835) : False :=
  not_tile_of_conditions' 1835 C'_1835 D

end Erdos634.Draft.AllN2

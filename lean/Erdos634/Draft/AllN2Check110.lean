/- AllN2Check110: N = 2737, 2742, 2743, 2747, 2755
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2737_sqf   : LeafSqf 2737   := by decide +kernel
private theorem c2737_range : LeafRange 2737  := by decide +kernel
private theorem c2737_ell   : LeafEll 2737    := by decide +kernel
private theorem c2737_nsq   : NSqChkSq 2737   := by decide +kernel
private theorem c2737_har   : HArithChkSq 2737 := by decide +kernel
private theorem c2737_r     : LeafR 2737      := by decide +kernel
private theorem c2737_e'    : LeafE' 2737     := by decide +kernel
private theorem c2737_f1    : LeafF1 2737     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2737_s2    : S2ChkSq 2737    := by decide +kernel
private theorem c2737_s3    : S3ChkSq 2737    := by decide +kernel
private theorem c2737_iso   : LeafIso 2737    := by decide +kernel
private theorem c2737_nof2  : NoF2ChkSq 2737  := by decide +kernel
private theorem c2737_nof3  : NoF3ChkSq 2737  := by decide +kernel
private theorem c2737_nof4z : NoF4zChkSq 2737 := by decide +kernel
theorem C'_2737 : C' 2737 :=
  ⟨c2737_sqf, c2737_range, c2737_ell, leafNSq_of_sq c2737_nsq, leafHAr_of_sq c2737_har,
   c2737_r, c2737_e', c2737_f1, leafS2_of_sq c2737_s2, leafS3_of_sq c2737_s3,
   c2737_iso, leafR8_of_sq c2737_nof2 c2737_nof3 c2737_nof4z⟩
theorem not_tile'_2737 (D : CongruentDissection 2737) : False :=
  not_tile_of_conditions' 2737 C'_2737 D

private theorem c2742_sqf   : LeafSqf 2742   := by decide +kernel
private theorem c2742_range : LeafRange 2742  := by decide +kernel
private theorem c2742_ell   : LeafEll 2742    := by decide +kernel
private theorem c2742_nsq   : NSqChkSq 2742   := by decide +kernel
private theorem c2742_har   : HArithChkSq 2742 := by decide +kernel
private theorem c2742_r     : LeafR 2742      := by decide +kernel
private theorem c2742_e'    : LeafE' 2742     := by decide +kernel
private theorem c2742_f1    : LeafF1 2742     := Or.inl (by decide)
private theorem c2742_s2    : S2ChkSq 2742    := by decide +kernel
private theorem c2742_s3    : S3ChkSq 2742    := by decide +kernel
private theorem c2742_iso   : LeafIso 2742    := by decide +kernel
private theorem c2742_nof2  : NoF2ChkSq 2742  := by decide +kernel
private theorem c2742_nof3  : NoF3ChkSq 2742  := by decide +kernel
private theorem c2742_nof4z : NoF4zChkSq 2742 := by decide +kernel
theorem C'_2742 : C' 2742 :=
  ⟨c2742_sqf, c2742_range, c2742_ell, leafNSq_of_sq c2742_nsq, leafHAr_of_sq c2742_har,
   c2742_r, c2742_e', c2742_f1, leafS2_of_sq c2742_s2, leafS3_of_sq c2742_s3,
   c2742_iso, leafR8_of_sq c2742_nof2 c2742_nof3 c2742_nof4z⟩
theorem not_tile'_2742 (D : CongruentDissection 2742) : False :=
  not_tile_of_conditions' 2742 C'_2742 D

private theorem c2743_sqf   : LeafSqf 2743   := by decide +kernel
private theorem c2743_range : LeafRange 2743  := by decide +kernel
private theorem c2743_ell   : LeafEll 2743    := by decide +kernel
private theorem c2743_nsq   : NSqChkSq 2743   := by decide +kernel
private theorem c2743_har   : HArithChkSq 2743 := by decide +kernel
private theorem c2743_r     : LeafR 2743      := by decide +kernel
private theorem c2743_e'    : LeafE' 2743     := by decide +kernel
private theorem c2743_f1    : LeafF1 2743     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2743_s2    : S2ChkSq 2743    := by decide +kernel
private theorem c2743_s3    : S3ChkSq 2743    := by decide +kernel
private theorem c2743_iso   : LeafIso 2743    := by decide +kernel
private theorem c2743_nof2  : NoF2ChkSq 2743  := by decide +kernel
private theorem c2743_nof3  : NoF3ChkSq 2743  := by decide +kernel
private theorem c2743_nof4z : NoF4zChkSq 2743 := by decide +kernel
theorem C'_2743 : C' 2743 :=
  ⟨c2743_sqf, c2743_range, c2743_ell, leafNSq_of_sq c2743_nsq, leafHAr_of_sq c2743_har,
   c2743_r, c2743_e', c2743_f1, leafS2_of_sq c2743_s2, leafS3_of_sq c2743_s3,
   c2743_iso, leafR8_of_sq c2743_nof2 c2743_nof3 c2743_nof4z⟩
theorem not_tile'_2743 (D : CongruentDissection 2743) : False :=
  not_tile_of_conditions' 2743 C'_2743 D

private theorem c2747_sqf   : LeafSqf 2747   := by decide +kernel
private theorem c2747_range : LeafRange 2747  := by decide +kernel
private theorem c2747_ell   : LeafEll 2747    := by decide +kernel
private theorem c2747_nsq   : NSqChkSq 2747   := by decide +kernel
private theorem c2747_har   : HArithChkSq 2747 := by decide +kernel
private theorem c2747_r     : LeafR 2747      := by decide +kernel
private theorem c2747_e'    : LeafE' 2747     := by decide +kernel
private theorem c2747_f1    : LeafF1 2747     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2747_s2    : S2ChkSq 2747    := by decide +kernel
private theorem c2747_s3    : S3ChkSq 2747    := by decide +kernel
private theorem c2747_iso   : LeafIso 2747    := by decide +kernel
private theorem c2747_nof2  : NoF2ChkSq 2747  := by decide +kernel
private theorem c2747_nof3  : NoF3ChkSq 2747  := by decide +kernel
private theorem c2747_nof4z : NoF4zChkSq 2747 := by decide +kernel
theorem C'_2747 : C' 2747 :=
  ⟨c2747_sqf, c2747_range, c2747_ell, leafNSq_of_sq c2747_nsq, leafHAr_of_sq c2747_har,
   c2747_r, c2747_e', c2747_f1, leafS2_of_sq c2747_s2, leafS3_of_sq c2747_s3,
   c2747_iso, leafR8_of_sq c2747_nof2 c2747_nof3 c2747_nof4z⟩
theorem not_tile'_2747 (D : CongruentDissection 2747) : False :=
  not_tile_of_conditions' 2747 C'_2747 D

private theorem c2755_sqf   : LeafSqf 2755   := by decide +kernel
private theorem c2755_range : LeafRange 2755  := by decide +kernel
private theorem c2755_ell   : LeafEll 2755    := by decide +kernel
private theorem c2755_nsq   : NSqChkSq 2755   := by decide +kernel
private theorem c2755_har   : HArithChkSq 2755 := by decide +kernel
private theorem c2755_r     : LeafR 2755      := by decide +kernel
private theorem c2755_e'    : LeafE' 2755     := by decide +kernel
private theorem c2755_f1    : LeafF1 2755     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2755_s2    : S2ChkSq 2755    := by decide +kernel
private theorem c2755_s3    : S3ChkSq 2755    := by decide +kernel
private theorem c2755_iso   : LeafIso 2755    := by decide +kernel
private theorem c2755_nof2  : NoF2ChkSq 2755  := by decide +kernel
private theorem c2755_nof3  : NoF3ChkSq 2755  := by decide +kernel
private theorem c2755_nof4z : NoF4zChkSq 2755 := by decide +kernel
theorem C'_2755 : C' 2755 :=
  ⟨c2755_sqf, c2755_range, c2755_ell, leafNSq_of_sq c2755_nsq, leafHAr_of_sq c2755_har,
   c2755_r, c2755_e', c2755_f1, leafS2_of_sq c2755_s2, leafS3_of_sq c2755_s3,
   c2755_iso, leafR8_of_sq c2755_nof2 c2755_nof3 c2755_nof4z⟩
theorem not_tile'_2755 (D : CongruentDissection 2755) : False :=
  not_tile_of_conditions' 2755 C'_2755 D

end Erdos634.Draft.AllN2

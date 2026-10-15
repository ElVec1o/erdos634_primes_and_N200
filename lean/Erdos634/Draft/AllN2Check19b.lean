/- AllN2Check19b: N = 753, 755, 759, 763, 771
   Squarefree exclusions via C' with sqrt-bounded checks (Wave-2 OOM fix). -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c753_sqf   : LeafSqf 753   := by decide +kernel
private theorem c753_range : LeafRange 753  := by decide +kernel
private theorem c753_ell   : LeafEll 753    := by decide +kernel
private theorem c753_nsq   : NSqChkSq 753   := by decide +kernel
private theorem c753_har   : HArithChkSq 753 := by decide +kernel
private theorem c753_r     : LeafR 753      := by decide +kernel
private theorem c753_e'    : LeafE' 753     := by decide +kernel
private theorem c753_f1    : LeafF1 753     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c753_s2    : S2ChkSq 753    := by decide +kernel
private theorem c753_s3    : S3ChkSq 753    := by decide +kernel
private theorem c753_iso   : LeafIso 753    := by decide +kernel
private theorem c753_nof2  : NoF2ChkSq 753  := by decide +kernel
private theorem c753_nof3  : NoF3ChkSq 753  := by decide +kernel
private theorem c753_nof4z : NoF4zChkSq 753 := by decide +kernel
theorem C'_753 : C' 753 :=
  ⟨c753_sqf, c753_range, c753_ell, leafNSq_of_sq c753_nsq, leafHAr_of_sq c753_har,
   c753_r, c753_e', c753_f1, leafS2_of_sq c753_s2, leafS3_of_sq c753_s3,
   c753_iso, leafR8_of_sq c753_nof2 c753_nof3 c753_nof4z⟩
theorem not_tile'_753 (D : CongruentDissection 753) : False :=
  not_tile_of_conditions' 753 C'_753 D

private theorem c755_sqf   : LeafSqf 755   := by decide +kernel
private theorem c755_range : LeafRange 755  := by decide +kernel
private theorem c755_ell   : LeafEll 755    := by decide +kernel
private theorem c755_nsq   : NSqChkSq 755   := by decide +kernel
private theorem c755_har   : HArithChkSq 755 := by decide +kernel
private theorem c755_r     : LeafR 755      := by decide +kernel
private theorem c755_e'    : LeafE' 755     := by decide +kernel
private theorem c755_f1    : LeafF1 755     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c755_s2    : S2ChkSq 755    := by decide +kernel
private theorem c755_s3    : S3ChkSq 755    := by decide +kernel
private theorem c755_iso   : LeafIso 755    := by decide +kernel
private theorem c755_nof2  : NoF2ChkSq 755  := by decide +kernel
private theorem c755_nof3  : NoF3ChkSq 755  := by decide +kernel
private theorem c755_nof4z : NoF4zChkSq 755 := by decide +kernel
theorem C'_755 : C' 755 :=
  ⟨c755_sqf, c755_range, c755_ell, leafNSq_of_sq c755_nsq, leafHAr_of_sq c755_har,
   c755_r, c755_e', c755_f1, leafS2_of_sq c755_s2, leafS3_of_sq c755_s3,
   c755_iso, leafR8_of_sq c755_nof2 c755_nof3 c755_nof4z⟩
theorem not_tile'_755 (D : CongruentDissection 755) : False :=
  not_tile_of_conditions' 755 C'_755 D

private theorem c759_sqf   : LeafSqf 759   := by decide +kernel
private theorem c759_range : LeafRange 759  := by decide +kernel
private theorem c759_ell   : LeafEll 759    := by decide +kernel
private theorem c759_nsq   : NSqChkSq 759   := by decide +kernel
private theorem c759_har   : HArithChkSq 759 := by decide +kernel
private theorem c759_r     : LeafR 759      := by decide +kernel
private theorem c759_e'    : LeafE' 759     := by decide +kernel
private theorem c759_f1    : LeafF1 759     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c759_s2    : S2ChkSq 759    := by decide +kernel
private theorem c759_s3    : S3ChkSq 759    := by decide +kernel
private theorem c759_iso   : LeafIso 759    := by decide +kernel
private theorem c759_nof2  : NoF2ChkSq 759  := by decide +kernel
private theorem c759_nof3  : NoF3ChkSq 759  := by decide +kernel
private theorem c759_nof4z : NoF4zChkSq 759 := by decide +kernel
theorem C'_759 : C' 759 :=
  ⟨c759_sqf, c759_range, c759_ell, leafNSq_of_sq c759_nsq, leafHAr_of_sq c759_har,
   c759_r, c759_e', c759_f1, leafS2_of_sq c759_s2, leafS3_of_sq c759_s3,
   c759_iso, leafR8_of_sq c759_nof2 c759_nof3 c759_nof4z⟩
theorem not_tile'_759 (D : CongruentDissection 759) : False :=
  not_tile_of_conditions' 759 C'_759 D

private theorem c763_sqf   : LeafSqf 763   := by decide +kernel
private theorem c763_range : LeafRange 763  := by decide +kernel
private theorem c763_ell   : LeafEll 763    := by decide +kernel
private theorem c763_nsq   : NSqChkSq 763   := by decide +kernel
private theorem c763_har   : HArithChkSq 763 := by decide +kernel
private theorem c763_r     : LeafR 763      := by decide +kernel
private theorem c763_e'    : LeafE' 763     := by decide +kernel
private theorem c763_f1    : LeafF1 763     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c763_s2    : S2ChkSq 763    := by decide +kernel
private theorem c763_s3    : S3ChkSq 763    := by decide +kernel
private theorem c763_iso   : LeafIso 763    := by decide +kernel
private theorem c763_nof2  : NoF2ChkSq 763  := by decide +kernel
private theorem c763_nof3  : NoF3ChkSq 763  := by decide +kernel
private theorem c763_nof4z : NoF4zChkSq 763 := by decide +kernel
theorem C'_763 : C' 763 :=
  ⟨c763_sqf, c763_range, c763_ell, leafNSq_of_sq c763_nsq, leafHAr_of_sq c763_har,
   c763_r, c763_e', c763_f1, leafS2_of_sq c763_s2, leafS3_of_sq c763_s3,
   c763_iso, leafR8_of_sq c763_nof2 c763_nof3 c763_nof4z⟩
theorem not_tile'_763 (D : CongruentDissection 763) : False :=
  not_tile_of_conditions' 763 C'_763 D

private theorem c771_sqf   : LeafSqf 771   := by decide +kernel
private theorem c771_range : LeafRange 771  := by decide +kernel
private theorem c771_ell   : LeafEll 771    := by decide +kernel
private theorem c771_nsq   : NSqChkSq 771   := by decide +kernel
private theorem c771_har   : HArithChkSq 771 := by decide +kernel
private theorem c771_r     : LeafR 771      := by decide +kernel
private theorem c771_e'    : LeafE' 771     := by decide +kernel
private theorem c771_f1    : LeafF1 771     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c771_s2    : S2ChkSq 771    := by decide +kernel
private theorem c771_s3    : S3ChkSq 771    := by decide +kernel
private theorem c771_iso   : LeafIso 771    := by decide +kernel
private theorem c771_nof2  : NoF2ChkSq 771  := by decide +kernel
private theorem c771_nof3  : NoF3ChkSq 771  := by decide +kernel
private theorem c771_nof4z : NoF4zChkSq 771 := by decide +kernel
theorem C'_771 : C' 771 :=
  ⟨c771_sqf, c771_range, c771_ell, leafNSq_of_sq c771_nsq, leafHAr_of_sq c771_har,
   c771_r, c771_e', c771_f1, leafS2_of_sq c771_s2, leafS3_of_sq c771_s3,
   c771_iso, leafR8_of_sq c771_nof2 c771_nof3 c771_nof4z⟩
theorem not_tile'_771 (D : CongruentDissection 771) : False :=
  not_tile_of_conditions' 771 C'_771 D

end Erdos634.Draft.AllN2

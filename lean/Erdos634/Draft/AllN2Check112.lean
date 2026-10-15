/- AllN2Check112: N = 2766, 2767, 2771, 2773, 2774
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2766_sqf   : LeafSqf 2766   := by decide +kernel
private theorem c2766_range : LeafRange 2766  := by decide +kernel
private theorem c2766_ell   : LeafEll 2766    := by decide +kernel
private theorem c2766_nsq   : NSqChkSq 2766   := by decide +kernel
private theorem c2766_har   : HArithChkSq 2766 := by decide +kernel
private theorem c2766_r     : LeafR 2766      := by decide +kernel
private theorem c2766_e'    : LeafE' 2766     := by decide +kernel
private theorem c2766_f1    : LeafF1 2766     := Or.inl (by decide)
private theorem c2766_s2    : S2ChkSq 2766    := by decide +kernel
private theorem c2766_s3    : S3ChkSq 2766    := by decide +kernel
private theorem c2766_iso   : LeafIso 2766    := by decide +kernel
private theorem c2766_nof2  : NoF2ChkSq 2766  := by decide +kernel
private theorem c2766_nof3  : NoF3ChkSq 2766  := by decide +kernel
private theorem c2766_nof4z : NoF4zChkSq 2766 := by decide +kernel
theorem C'_2766 : C' 2766 :=
  ⟨c2766_sqf, c2766_range, c2766_ell, leafNSq_of_sq c2766_nsq, leafHAr_of_sq c2766_har,
   c2766_r, c2766_e', c2766_f1, leafS2_of_sq c2766_s2, leafS3_of_sq c2766_s3,
   c2766_iso, leafR8_of_sq c2766_nof2 c2766_nof3 c2766_nof4z⟩
theorem not_tile'_2766 (D : CongruentDissection 2766) : False :=
  not_tile_of_conditions' 2766 C'_2766 D

private theorem c2767_sqf   : LeafSqf 2767   := by decide +kernel
private theorem c2767_range : LeafRange 2767  := by decide +kernel
private theorem c2767_ell   : LeafEll 2767    := by decide +kernel
private theorem c2767_nsq   : NSqChkSq 2767   := by decide +kernel
private theorem c2767_har   : HArithChkSq 2767 := by decide +kernel
private theorem c2767_r     : LeafR 2767      := by decide +kernel
private theorem c2767_e'    : LeafE' 2767     := by decide +kernel
private theorem c2767_f1    : LeafF1 2767     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2767_s2    : S2ChkSq 2767    := by decide +kernel
private theorem c2767_s3    : S3ChkSq 2767    := by decide +kernel
private theorem c2767_iso   : LeafIso 2767    := by decide +kernel
private theorem c2767_nof2  : NoF2ChkSq 2767  := by decide +kernel
private theorem c2767_nof3  : NoF3ChkSq 2767  := by decide +kernel
private theorem c2767_nof4z : NoF4zChkSq 2767 := by decide +kernel
theorem C'_2767 : C' 2767 :=
  ⟨c2767_sqf, c2767_range, c2767_ell, leafNSq_of_sq c2767_nsq, leafHAr_of_sq c2767_har,
   c2767_r, c2767_e', c2767_f1, leafS2_of_sq c2767_s2, leafS3_of_sq c2767_s3,
   c2767_iso, leafR8_of_sq c2767_nof2 c2767_nof3 c2767_nof4z⟩
theorem not_tile'_2767 (D : CongruentDissection 2767) : False :=
  not_tile_of_conditions' 2767 C'_2767 D

private theorem c2771_sqf   : LeafSqf 2771   := by decide +kernel
private theorem c2771_range : LeafRange 2771  := by decide +kernel
private theorem c2771_ell   : LeafEll 2771    := by decide +kernel
private theorem c2771_nsq   : NSqChkSq 2771   := by decide +kernel
private theorem c2771_har   : HArithChkSq 2771 := by decide +kernel
private theorem c2771_r     : LeafR 2771      := by decide +kernel
private theorem c2771_e'    : LeafE' 2771     := by decide +kernel
private theorem c2771_f1    : LeafF1 2771     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2771_s2    : S2ChkSq 2771    := by decide +kernel
private theorem c2771_s3    : S3ChkSq 2771    := by decide +kernel
private theorem c2771_iso   : LeafIso 2771    := by decide +kernel
private theorem c2771_nof2  : NoF2ChkSq 2771  := by decide +kernel
private theorem c2771_nof3  : NoF3ChkSq 2771  := by decide +kernel
private theorem c2771_nof4z : NoF4zChkSq 2771 := by decide +kernel
theorem C'_2771 : C' 2771 :=
  ⟨c2771_sqf, c2771_range, c2771_ell, leafNSq_of_sq c2771_nsq, leafHAr_of_sq c2771_har,
   c2771_r, c2771_e', c2771_f1, leafS2_of_sq c2771_s2, leafS3_of_sq c2771_s3,
   c2771_iso, leafR8_of_sq c2771_nof2 c2771_nof3 c2771_nof4z⟩
theorem not_tile'_2771 (D : CongruentDissection 2771) : False :=
  not_tile_of_conditions' 2771 C'_2771 D

private theorem c2773_sqf   : LeafSqf 2773   := by decide +kernel
private theorem c2773_range : LeafRange 2773  := by decide +kernel
private theorem c2773_ell   : LeafEll 2773    := by decide +kernel
private theorem c2773_nsq   : NSqChkSq 2773   := by decide +kernel
private theorem c2773_har   : HArithChkSq 2773 := by decide +kernel
private theorem c2773_r     : LeafR 2773      := by decide +kernel
private theorem c2773_e'    : LeafE' 2773     := by decide +kernel
private theorem c2773_f1    : LeafF1 2773     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2773_s2    : S2ChkSq 2773    := by decide +kernel
private theorem c2773_s3    : S3ChkSq 2773    := by decide +kernel
private theorem c2773_iso   : LeafIso 2773    := by decide +kernel
private theorem c2773_nof2  : NoF2ChkSq 2773  := by decide +kernel
private theorem c2773_nof3  : NoF3ChkSq 2773  := by decide +kernel
private theorem c2773_nof4z : NoF4zChkSq 2773 := by decide +kernel
theorem C'_2773 : C' 2773 :=
  ⟨c2773_sqf, c2773_range, c2773_ell, leafNSq_of_sq c2773_nsq, leafHAr_of_sq c2773_har,
   c2773_r, c2773_e', c2773_f1, leafS2_of_sq c2773_s2, leafS3_of_sq c2773_s3,
   c2773_iso, leafR8_of_sq c2773_nof2 c2773_nof3 c2773_nof4z⟩
theorem not_tile'_2773 (D : CongruentDissection 2773) : False :=
  not_tile_of_conditions' 2773 C'_2773 D

private theorem c2774_sqf   : LeafSqf 2774   := by decide +kernel
private theorem c2774_range : LeafRange 2774  := by decide +kernel
private theorem c2774_ell   : LeafEll 2774    := by decide +kernel
private theorem c2774_nsq   : NSqChkSq 2774   := by decide +kernel
private theorem c2774_har   : HArithChkSq 2774 := by decide +kernel
private theorem c2774_r     : LeafR 2774      := by decide +kernel
private theorem c2774_e'    : LeafE' 2774     := by decide +kernel
private theorem c2774_f1    : LeafF1 2774     := Or.inl (by decide)
private theorem c2774_s2    : S2ChkSq 2774    := by decide +kernel
private theorem c2774_s3    : S3ChkSq 2774    := by decide +kernel
private theorem c2774_iso   : LeafIso 2774    := by decide +kernel
private theorem c2774_nof2  : NoF2ChkSq 2774  := by decide +kernel
private theorem c2774_nof3  : NoF3ChkSq 2774  := by decide +kernel
private theorem c2774_nof4z : NoF4zChkSq 2774 := by decide +kernel
theorem C'_2774 : C' 2774 :=
  ⟨c2774_sqf, c2774_range, c2774_ell, leafNSq_of_sq c2774_nsq, leafHAr_of_sq c2774_har,
   c2774_r, c2774_e', c2774_f1, leafS2_of_sq c2774_s2, leafS3_of_sq c2774_s3,
   c2774_iso, leafR8_of_sq c2774_nof2 c2774_nof3 c2774_nof4z⟩
theorem not_tile'_2774 (D : CongruentDissection 2774) : False :=
  not_tile_of_conditions' 2774 C'_2774 D

end Erdos634.Draft.AllN2

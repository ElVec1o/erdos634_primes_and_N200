/- AllN2Check96: N = 2562, 2563, 2566, 2567, 2569
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2562_sqf   : LeafSqf 2562   := by decide +kernel
private theorem c2562_range : LeafRange 2562  := by decide +kernel
private theorem c2562_ell   : LeafEll 2562    := by decide +kernel
private theorem c2562_nsq   : NSqChkSq 2562   := by decide +kernel
private theorem c2562_har   : HArithChkSq 2562 := by decide +kernel
private theorem c2562_r     : LeafR 2562      := by decide +kernel
private theorem c2562_e'    : LeafE' 2562     := by decide +kernel
private theorem c2562_f1    : LeafF1 2562     := Or.inl (by decide)
private theorem c2562_s2    : S2ChkSq 2562    := by decide +kernel
private theorem c2562_s3    : S3ChkSq 2562    := by decide +kernel
private theorem c2562_iso   : LeafIso 2562    := by decide +kernel
private theorem c2562_nof2  : NoF2ChkSq 2562  := by decide +kernel
private theorem c2562_nof3  : NoF3ChkSq 2562  := by decide +kernel
private theorem c2562_nof4z : NoF4zChkSq 2562 := by decide +kernel
theorem C'_2562 : C' 2562 :=
  ⟨c2562_sqf, c2562_range, c2562_ell, leafNSq_of_sq c2562_nsq, leafHAr_of_sq c2562_har,
   c2562_r, c2562_e', c2562_f1, leafS2_of_sq c2562_s2, leafS3_of_sq c2562_s3,
   c2562_iso, leafR8_of_sq c2562_nof2 c2562_nof3 c2562_nof4z⟩
theorem not_tile'_2562 (D : CongruentDissection 2562) : False :=
  not_tile_of_conditions' 2562 C'_2562 D

private theorem c2563_sqf   : LeafSqf 2563   := by decide +kernel
private theorem c2563_range : LeafRange 2563  := by decide +kernel
private theorem c2563_ell   : LeafEll 2563    := by decide +kernel
private theorem c2563_nsq   : NSqChkSq 2563   := by decide +kernel
private theorem c2563_har   : HArithChkSq 2563 := by decide +kernel
private theorem c2563_r     : LeafR 2563      := by decide +kernel
private theorem c2563_e'    : LeafE' 2563     := by decide +kernel
private theorem c2563_f1    : LeafF1 2563     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2563_s2    : S2ChkSq 2563    := by decide +kernel
private theorem c2563_s3    : S3ChkSq 2563    := by decide +kernel
private theorem c2563_iso   : LeafIso 2563    := by decide +kernel
private theorem c2563_nof2  : NoF2ChkSq 2563  := by decide +kernel
private theorem c2563_nof3  : NoF3ChkSq 2563  := by decide +kernel
private theorem c2563_nof4z : NoF4zChkSq 2563 := by decide +kernel
theorem C'_2563 : C' 2563 :=
  ⟨c2563_sqf, c2563_range, c2563_ell, leafNSq_of_sq c2563_nsq, leafHAr_of_sq c2563_har,
   c2563_r, c2563_e', c2563_f1, leafS2_of_sq c2563_s2, leafS3_of_sq c2563_s3,
   c2563_iso, leafR8_of_sq c2563_nof2 c2563_nof3 c2563_nof4z⟩
theorem not_tile'_2563 (D : CongruentDissection 2563) : False :=
  not_tile_of_conditions' 2563 C'_2563 D

private theorem c2566_sqf   : LeafSqf 2566   := by decide +kernel
private theorem c2566_range : LeafRange 2566  := by decide +kernel
private theorem c2566_ell   : LeafEll 2566    := by decide +kernel
private theorem c2566_nsq   : NSqChkSq 2566   := by decide +kernel
private theorem c2566_har   : HArithChkSq 2566 := by decide +kernel
private theorem c2566_r     : LeafR 2566      := by decide +kernel
private theorem c2566_e'    : LeafE' 2566     := by decide +kernel
private theorem c2566_f1    : LeafF1 2566     := Or.inl (by decide)
private theorem c2566_s2    : S2ChkSq 2566    := by decide +kernel
private theorem c2566_s3    : S3ChkSq 2566    := by decide +kernel
private theorem c2566_iso   : LeafIso 2566    := by decide +kernel
private theorem c2566_nof2  : NoF2ChkSq 2566  := by decide +kernel
private theorem c2566_nof3  : NoF3ChkSq 2566  := by decide +kernel
private theorem c2566_nof4z : NoF4zChkSq 2566 := by decide +kernel
theorem C'_2566 : C' 2566 :=
  ⟨c2566_sqf, c2566_range, c2566_ell, leafNSq_of_sq c2566_nsq, leafHAr_of_sq c2566_har,
   c2566_r, c2566_e', c2566_f1, leafS2_of_sq c2566_s2, leafS3_of_sq c2566_s3,
   c2566_iso, leafR8_of_sq c2566_nof2 c2566_nof3 c2566_nof4z⟩
theorem not_tile'_2566 (D : CongruentDissection 2566) : False :=
  not_tile_of_conditions' 2566 C'_2566 D

private theorem c2567_sqf   : LeafSqf 2567   := by decide +kernel
private theorem c2567_range : LeafRange 2567  := by decide +kernel
private theorem c2567_ell   : LeafEll 2567    := by decide +kernel
private theorem c2567_nsq   : NSqChkSq 2567   := by decide +kernel
private theorem c2567_har   : HArithChkSq 2567 := by decide +kernel
private theorem c2567_r     : LeafR 2567      := by decide +kernel
private theorem c2567_e'    : LeafE' 2567     := by decide +kernel
private theorem c2567_f1    : LeafF1 2567     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2567_s2    : S2ChkSq 2567    := by decide +kernel
private theorem c2567_s3    : S3ChkSq 2567    := by decide +kernel
private theorem c2567_iso   : LeafIso 2567    := by decide +kernel
private theorem c2567_nof2  : NoF2ChkSq 2567  := by decide +kernel
private theorem c2567_nof3  : NoF3ChkSq 2567  := by decide +kernel
private theorem c2567_nof4z : NoF4zChkSq 2567 := by decide +kernel
theorem C'_2567 : C' 2567 :=
  ⟨c2567_sqf, c2567_range, c2567_ell, leafNSq_of_sq c2567_nsq, leafHAr_of_sq c2567_har,
   c2567_r, c2567_e', c2567_f1, leafS2_of_sq c2567_s2, leafS3_of_sq c2567_s3,
   c2567_iso, leafR8_of_sq c2567_nof2 c2567_nof3 c2567_nof4z⟩
theorem not_tile'_2567 (D : CongruentDissection 2567) : False :=
  not_tile_of_conditions' 2567 C'_2567 D

private theorem c2569_sqf   : LeafSqf 2569   := by decide +kernel
private theorem c2569_range : LeafRange 2569  := by decide +kernel
private theorem c2569_ell   : LeafEll 2569    := by decide +kernel
private theorem c2569_nsq   : NSqChkSq 2569   := by decide +kernel
private theorem c2569_har   : HArithChkSq 2569 := by decide +kernel
private theorem c2569_r     : LeafR 2569      := by decide +kernel
private theorem c2569_e'    : LeafE' 2569     := by decide +kernel
private theorem c2569_f1    : LeafF1 2569     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2569_s2    : S2ChkSq 2569    := by decide +kernel
private theorem c2569_s3    : S3ChkSq 2569    := by decide +kernel
private theorem c2569_iso   : LeafIso 2569    := by decide +kernel
private theorem c2569_nof2  : NoF2ChkSq 2569  := by decide +kernel
private theorem c2569_nof3  : NoF3ChkSq 2569  := by decide +kernel
private theorem c2569_nof4z : NoF4zChkSq 2569 := by decide +kernel
theorem C'_2569 : C' 2569 :=
  ⟨c2569_sqf, c2569_range, c2569_ell, leafNSq_of_sq c2569_nsq, leafHAr_of_sq c2569_har,
   c2569_r, c2569_e', c2569_f1, leafS2_of_sq c2569_s2, leafS3_of_sq c2569_s3,
   c2569_iso, leafR8_of_sq c2569_nof2 c2569_nof3 c2569_nof4z⟩
theorem not_tile'_2569 (D : CongruentDissection 2569) : False :=
  not_tile_of_conditions' 2569 C'_2569 D

end Erdos634.Draft.AllN2

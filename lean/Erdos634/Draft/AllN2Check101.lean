/- AllN2Check101: N = 2627, 2629, 2630, 2631, 2634
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2627_sqf   : LeafSqf 2627   := by decide +kernel
private theorem c2627_range : LeafRange 2627  := by decide +kernel
private theorem c2627_ell   : LeafEll 2627    := by decide +kernel
private theorem c2627_nsq   : NSqChkSq 2627   := by decide +kernel
private theorem c2627_har   : HArithChkSq 2627 := by decide +kernel
private theorem c2627_r     : LeafR 2627      := by decide +kernel
private theorem c2627_e'    : LeafE' 2627     := by decide +kernel
private theorem c2627_f1    : LeafF1 2627     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2627_s2    : S2ChkSq 2627    := by decide +kernel
private theorem c2627_s3    : S3ChkSq 2627    := by decide +kernel
private theorem c2627_iso   : LeafIso 2627    := by decide +kernel
private theorem c2627_nof2  : NoF2ChkSq 2627  := by decide +kernel
private theorem c2627_nof3  : NoF3ChkSq 2627  := by decide +kernel
private theorem c2627_nof4z : NoF4zChkSq 2627 := by decide +kernel
theorem C'_2627 : C' 2627 :=
  ⟨c2627_sqf, c2627_range, c2627_ell, leafNSq_of_sq c2627_nsq, leafHAr_of_sq c2627_har,
   c2627_r, c2627_e', c2627_f1, leafS2_of_sq c2627_s2, leafS3_of_sq c2627_s3,
   c2627_iso, leafR8_of_sq c2627_nof2 c2627_nof3 c2627_nof4z⟩
theorem not_tile'_2627 (D : CongruentDissection 2627) : False :=
  not_tile_of_conditions' 2627 C'_2627 D

private theorem c2629_sqf   : LeafSqf 2629   := by decide +kernel
private theorem c2629_range : LeafRange 2629  := by decide +kernel
private theorem c2629_ell   : LeafEll 2629    := by decide +kernel
private theorem c2629_nsq   : NSqChkSq 2629   := by decide +kernel
private theorem c2629_har   : HArithChkSq 2629 := by decide +kernel
private theorem c2629_r     : LeafR 2629      := by decide +kernel
private theorem c2629_e'    : LeafE' 2629     := by decide +kernel
private theorem c2629_f1    : LeafF1 2629     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2629_s2    : S2ChkSq 2629    := by decide +kernel
private theorem c2629_s3    : S3ChkSq 2629    := by decide +kernel
private theorem c2629_iso   : LeafIso 2629    := by decide +kernel
private theorem c2629_nof2  : NoF2ChkSq 2629  := by decide +kernel
private theorem c2629_nof3  : NoF3ChkSq 2629  := by decide +kernel
private theorem c2629_nof4z : NoF4zChkSq 2629 := by decide +kernel
theorem C'_2629 : C' 2629 :=
  ⟨c2629_sqf, c2629_range, c2629_ell, leafNSq_of_sq c2629_nsq, leafHAr_of_sq c2629_har,
   c2629_r, c2629_e', c2629_f1, leafS2_of_sq c2629_s2, leafS3_of_sq c2629_s3,
   c2629_iso, leafR8_of_sq c2629_nof2 c2629_nof3 c2629_nof4z⟩
theorem not_tile'_2629 (D : CongruentDissection 2629) : False :=
  not_tile_of_conditions' 2629 C'_2629 D

private theorem c2630_sqf   : LeafSqf 2630   := by decide +kernel
private theorem c2630_range : LeafRange 2630  := by decide +kernel
private theorem c2630_ell   : LeafEll 2630    := by decide +kernel
private theorem c2630_nsq   : NSqChkSq 2630   := by decide +kernel
private theorem c2630_har   : HArithChkSq 2630 := by decide +kernel
private theorem c2630_r     : LeafR 2630      := by decide +kernel
private theorem c2630_e'    : LeafE' 2630     := by decide +kernel
private theorem c2630_f1    : LeafF1 2630     := Or.inl (by decide)
private theorem c2630_s2    : S2ChkSq 2630    := by decide +kernel
private theorem c2630_s3    : S3ChkSq 2630    := by decide +kernel
private theorem c2630_iso   : LeafIso 2630    := by decide +kernel
private theorem c2630_nof2  : NoF2ChkSq 2630  := by decide +kernel
private theorem c2630_nof3  : NoF3ChkSq 2630  := by decide +kernel
private theorem c2630_nof4z : NoF4zChkSq 2630 := by decide +kernel
theorem C'_2630 : C' 2630 :=
  ⟨c2630_sqf, c2630_range, c2630_ell, leafNSq_of_sq c2630_nsq, leafHAr_of_sq c2630_har,
   c2630_r, c2630_e', c2630_f1, leafS2_of_sq c2630_s2, leafS3_of_sq c2630_s3,
   c2630_iso, leafR8_of_sq c2630_nof2 c2630_nof3 c2630_nof4z⟩
theorem not_tile'_2630 (D : CongruentDissection 2630) : False :=
  not_tile_of_conditions' 2630 C'_2630 D

private theorem c2631_sqf   : LeafSqf 2631   := by decide +kernel
private theorem c2631_range : LeafRange 2631  := by decide +kernel
private theorem c2631_ell   : LeafEll 2631    := by decide +kernel
private theorem c2631_nsq   : NSqChkSq 2631   := by decide +kernel
private theorem c2631_har   : HArithChkSq 2631 := by decide +kernel
private theorem c2631_r     : LeafR 2631      := by decide +kernel
private theorem c2631_e'    : LeafE' 2631     := by decide +kernel
private theorem c2631_f1    : LeafF1 2631     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2631_s2    : S2ChkSq 2631    := by decide +kernel
private theorem c2631_s3    : S3ChkSq 2631    := by decide +kernel
private theorem c2631_iso   : LeafIso 2631    := by decide +kernel
private theorem c2631_nof2  : NoF2ChkSq 2631  := by decide +kernel
private theorem c2631_nof3  : NoF3ChkSq 2631  := by decide +kernel
private theorem c2631_nof4z : NoF4zChkSq 2631 := by decide +kernel
theorem C'_2631 : C' 2631 :=
  ⟨c2631_sqf, c2631_range, c2631_ell, leafNSq_of_sq c2631_nsq, leafHAr_of_sq c2631_har,
   c2631_r, c2631_e', c2631_f1, leafS2_of_sq c2631_s2, leafS3_of_sq c2631_s3,
   c2631_iso, leafR8_of_sq c2631_nof2 c2631_nof3 c2631_nof4z⟩
theorem not_tile'_2631 (D : CongruentDissection 2631) : False :=
  not_tile_of_conditions' 2631 C'_2631 D

private theorem c2634_sqf   : LeafSqf 2634   := by decide +kernel
private theorem c2634_range : LeafRange 2634  := by decide +kernel
private theorem c2634_ell   : LeafEll 2634    := by decide +kernel
private theorem c2634_nsq   : NSqChkSq 2634   := by decide +kernel
private theorem c2634_har   : HArithChkSq 2634 := by decide +kernel
private theorem c2634_r     : LeafR 2634      := by decide +kernel
private theorem c2634_e'    : LeafE' 2634     := by decide +kernel
private theorem c2634_f1    : LeafF1 2634     := Or.inl (by decide)
private theorem c2634_s2    : S2ChkSq 2634    := by decide +kernel
private theorem c2634_s3    : S3ChkSq 2634    := by decide +kernel
private theorem c2634_iso   : LeafIso 2634    := by decide +kernel
private theorem c2634_nof2  : NoF2ChkSq 2634  := by decide +kernel
private theorem c2634_nof3  : NoF3ChkSq 2634  := by decide +kernel
private theorem c2634_nof4z : NoF4zChkSq 2634 := by decide +kernel
theorem C'_2634 : C' 2634 :=
  ⟨c2634_sqf, c2634_range, c2634_ell, leafNSq_of_sq c2634_nsq, leafHAr_of_sq c2634_har,
   c2634_r, c2634_e', c2634_f1, leafS2_of_sq c2634_s2, leafS3_of_sq c2634_s3,
   c2634_iso, leafR8_of_sq c2634_nof2 c2634_nof3 c2634_nof4z⟩
theorem not_tile'_2634 (D : CongruentDissection 2634) : False :=
  not_tile_of_conditions' 2634 C'_2634 D

end Erdos634.Draft.AllN2

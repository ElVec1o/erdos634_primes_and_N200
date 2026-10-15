/- AllN2Check257: N = 4630, 4631, 4634, 4638, 4639
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4630_sqf   : LeafSqf 4630   := by decide +kernel
private theorem c4630_range : LeafRange 4630  := by decide +kernel
private theorem c4630_ell   : LeafEll 4630    := by decide +kernel
private theorem c4630_nsq   : NSqChkSq 4630   := by decide +kernel
private theorem c4630_har   : HArithChkSq 4630 := by decide +kernel
private theorem c4630_r     : LeafR 4630      := by decide +kernel
private theorem c4630_e'    : LeafE' 4630     := by decide +kernel
private theorem c4630_f1    : LeafF1 4630     := Or.inl (by decide)
private theorem c4630_s2    : S2ChkSq 4630    := by decide +kernel
private theorem c4630_s3    : S3ChkSq 4630    := by decide +kernel
private theorem c4630_iso   : LeafIso 4630    := by decide +kernel
private theorem c4630_nof2  : NoF2ChkSq 4630  := by decide +kernel
private theorem c4630_nof3  : NoF3ChkSq 4630  := by decide +kernel
private theorem c4630_nof4z : NoF4zChkSq 4630 := by decide +kernel
theorem C'_4630 : C' 4630 :=
  ⟨c4630_sqf, c4630_range, c4630_ell, leafNSq_of_sq c4630_nsq, leafHAr_of_sq c4630_har,
   c4630_r, c4630_e', c4630_f1, leafS2_of_sq c4630_s2, leafS3_of_sq c4630_s3,
   c4630_iso, leafR8_of_sq c4630_nof2 c4630_nof3 c4630_nof4z⟩
theorem not_tile'_4630 (D : CongruentDissection 4630) : False :=
  not_tile_of_conditions' 4630 C'_4630 D

private theorem c4631_sqf   : LeafSqf 4631   := by decide +kernel
private theorem c4631_range : LeafRange 4631  := by decide +kernel
private theorem c4631_ell   : LeafEll 4631    := by decide +kernel
private theorem c4631_nsq   : NSqChkSq 4631   := by decide +kernel
private theorem c4631_har   : HArithChkSq 4631 := by decide +kernel
private theorem c4631_r     : LeafR 4631      := by decide +kernel
private theorem c4631_e'    : LeafE' 4631     := by decide +kernel
private theorem c4631_f1    : LeafF1 4631     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4631_s2    : S2ChkSq 4631    := by decide +kernel
private theorem c4631_s3    : S3ChkSq 4631    := by decide +kernel
private theorem c4631_iso   : LeafIso 4631    := by decide +kernel
private theorem c4631_nof2  : NoF2ChkSq 4631  := by decide +kernel
private theorem c4631_nof3  : NoF3ChkSq 4631  := by decide +kernel
private theorem c4631_nof4z : NoF4zChkSq 4631 := by decide +kernel
theorem C'_4631 : C' 4631 :=
  ⟨c4631_sqf, c4631_range, c4631_ell, leafNSq_of_sq c4631_nsq, leafHAr_of_sq c4631_har,
   c4631_r, c4631_e', c4631_f1, leafS2_of_sq c4631_s2, leafS3_of_sq c4631_s3,
   c4631_iso, leafR8_of_sq c4631_nof2 c4631_nof3 c4631_nof4z⟩
theorem not_tile'_4631 (D : CongruentDissection 4631) : False :=
  not_tile_of_conditions' 4631 C'_4631 D

private theorem c4634_sqf   : LeafSqf 4634   := by decide +kernel
private theorem c4634_range : LeafRange 4634  := by decide +kernel
private theorem c4634_ell   : LeafEll 4634    := by decide +kernel
private theorem c4634_nsq   : NSqChkSq 4634   := by decide +kernel
private theorem c4634_har   : HArithChkSq 4634 := by decide +kernel
private theorem c4634_r     : LeafR 4634      := by decide +kernel
private theorem c4634_e'    : LeafE' 4634     := by decide +kernel
private theorem c4634_f1    : LeafF1 4634     := Or.inl (by decide)
private theorem c4634_s2    : S2ChkSq 4634    := by decide +kernel
private theorem c4634_s3    : S3ChkSq 4634    := by decide +kernel
private theorem c4634_iso   : LeafIso 4634    := by decide +kernel
private theorem c4634_nof2  : NoF2ChkSq 4634  := by decide +kernel
private theorem c4634_nof3  : NoF3ChkSq 4634  := by decide +kernel
private theorem c4634_nof4z : NoF4zChkSq 4634 := by decide +kernel
theorem C'_4634 : C' 4634 :=
  ⟨c4634_sqf, c4634_range, c4634_ell, leafNSq_of_sq c4634_nsq, leafHAr_of_sq c4634_har,
   c4634_r, c4634_e', c4634_f1, leafS2_of_sq c4634_s2, leafS3_of_sq c4634_s3,
   c4634_iso, leafR8_of_sq c4634_nof2 c4634_nof3 c4634_nof4z⟩
theorem not_tile'_4634 (D : CongruentDissection 4634) : False :=
  not_tile_of_conditions' 4634 C'_4634 D

private theorem c4638_sqf   : LeafSqf 4638   := by decide +kernel
private theorem c4638_range : LeafRange 4638  := by decide +kernel
private theorem c4638_ell   : LeafEll 4638    := by decide +kernel
private theorem c4638_nsq   : NSqChkSq 4638   := by decide +kernel
private theorem c4638_har   : HArithChkSq 4638 := by decide +kernel
private theorem c4638_r     : LeafR 4638      := by decide +kernel
private theorem c4638_e'    : LeafE' 4638     := by decide +kernel
private theorem c4638_f1    : LeafF1 4638     := Or.inl (by decide)
private theorem c4638_s2    : S2ChkSq 4638    := by decide +kernel
private theorem c4638_s3    : S3ChkSq 4638    := by decide +kernel
private theorem c4638_iso   : LeafIso 4638    := by decide +kernel
private theorem c4638_nof2  : NoF2ChkSq 4638  := by decide +kernel
private theorem c4638_nof3  : NoF3ChkSq 4638  := by decide +kernel
private theorem c4638_nof4z : NoF4zChkSq 4638 := by decide +kernel
theorem C'_4638 : C' 4638 :=
  ⟨c4638_sqf, c4638_range, c4638_ell, leafNSq_of_sq c4638_nsq, leafHAr_of_sq c4638_har,
   c4638_r, c4638_e', c4638_f1, leafS2_of_sq c4638_s2, leafS3_of_sq c4638_s3,
   c4638_iso, leafR8_of_sq c4638_nof2 c4638_nof3 c4638_nof4z⟩
theorem not_tile'_4638 (D : CongruentDissection 4638) : False :=
  not_tile_of_conditions' 4638 C'_4638 D

private theorem c4639_sqf   : LeafSqf 4639   := by decide +kernel
private theorem c4639_range : LeafRange 4639  := by decide +kernel
private theorem c4639_ell   : LeafEll 4639    := by decide +kernel
private theorem c4639_nsq   : NSqChkSq 4639   := by decide +kernel
private theorem c4639_har   : HArithChkSq 4639 := by decide +kernel
private theorem c4639_r     : LeafR 4639      := by decide +kernel
private theorem c4639_e'    : LeafE' 4639     := by decide +kernel
private theorem c4639_f1    : LeafF1 4639     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4639_s2    : S2ChkSq 4639    := by decide +kernel
private theorem c4639_s3    : S3ChkSq 4639    := by decide +kernel
private theorem c4639_iso   : LeafIso 4639    := by decide +kernel
private theorem c4639_nof2  : NoF2ChkSq 4639  := by decide +kernel
private theorem c4639_nof3  : NoF3ChkSq 4639  := by decide +kernel
private theorem c4639_nof4z : NoF4zChkSq 4639 := by decide +kernel
theorem C'_4639 : C' 4639 :=
  ⟨c4639_sqf, c4639_range, c4639_ell, leafNSq_of_sq c4639_nsq, leafHAr_of_sq c4639_har,
   c4639_r, c4639_e', c4639_f1, leafS2_of_sq c4639_s2, leafS3_of_sq c4639_s3,
   c4639_iso, leafR8_of_sq c4639_nof2 c4639_nof3 c4639_nof4z⟩
theorem not_tile'_4639 (D : CongruentDissection 4639) : False :=
  not_tile_of_conditions' 4639 C'_4639 D

end Erdos634.Draft.AllN2

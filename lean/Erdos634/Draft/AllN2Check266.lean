/- AllN2Check266: N = 4741, 4742, 4746, 4747, 4749
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4741_sqf   : LeafSqf 4741   := by decide +kernel
private theorem c4741_range : LeafRange 4741  := by decide +kernel
private theorem c4741_ell   : LeafEll 4741    := by decide +kernel
private theorem c4741_nsq   : NSqChkSq 4741   := by decide +kernel
private theorem c4741_har   : HArithChkSq 4741 := by decide +kernel
private theorem c4741_r     : LeafR 4741      := by decide +kernel
private theorem c4741_e'    : LeafE' 4741     := by decide +kernel
private theorem c4741_f1    : LeafF1 4741     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4741_s2    : S2ChkSq 4741    := by decide +kernel
private theorem c4741_s3    : S3ChkSq 4741    := by decide +kernel
private theorem c4741_iso   : LeafIso 4741    := by decide +kernel
private theorem c4741_nof2  : NoF2ChkSq 4741  := by decide +kernel
private theorem c4741_nof3  : NoF3ChkSq 4741  := by decide +kernel
private theorem c4741_nof4z : NoF4zChkSq 4741 := by decide +kernel
theorem C'_4741 : C' 4741 :=
  ⟨c4741_sqf, c4741_range, c4741_ell, leafNSq_of_sq c4741_nsq, leafHAr_of_sq c4741_har,
   c4741_r, c4741_e', c4741_f1, leafS2_of_sq c4741_s2, leafS3_of_sq c4741_s3,
   c4741_iso, leafR8_of_sq c4741_nof2 c4741_nof3 c4741_nof4z⟩
theorem not_tile'_4741 (D : CongruentDissection 4741) : False :=
  not_tile_of_conditions' 4741 C'_4741 D

private theorem c4742_sqf   : LeafSqf 4742   := by decide +kernel
private theorem c4742_range : LeafRange 4742  := by decide +kernel
private theorem c4742_ell   : LeafEll 4742    := by decide +kernel
private theorem c4742_nsq   : NSqChkSq 4742   := by decide +kernel
private theorem c4742_har   : HArithChkSq 4742 := by decide +kernel
private theorem c4742_r     : LeafR 4742      := by decide +kernel
private theorem c4742_e'    : LeafE' 4742     := by decide +kernel
private theorem c4742_f1    : LeafF1 4742     := Or.inl (by decide)
private theorem c4742_s2    : S2ChkSq 4742    := by decide +kernel
private theorem c4742_s3    : S3ChkSq 4742    := by decide +kernel
private theorem c4742_iso   : LeafIso 4742    := by decide +kernel
private theorem c4742_nof2  : NoF2ChkSq 4742  := by decide +kernel
private theorem c4742_nof3  : NoF3ChkSq 4742  := by decide +kernel
private theorem c4742_nof4z : NoF4zChkSq 4742 := by decide +kernel
theorem C'_4742 : C' 4742 :=
  ⟨c4742_sqf, c4742_range, c4742_ell, leafNSq_of_sq c4742_nsq, leafHAr_of_sq c4742_har,
   c4742_r, c4742_e', c4742_f1, leafS2_of_sq c4742_s2, leafS3_of_sq c4742_s3,
   c4742_iso, leafR8_of_sq c4742_nof2 c4742_nof3 c4742_nof4z⟩
theorem not_tile'_4742 (D : CongruentDissection 4742) : False :=
  not_tile_of_conditions' 4742 C'_4742 D

private theorem c4746_sqf   : LeafSqf 4746   := by decide +kernel
private theorem c4746_range : LeafRange 4746  := by decide +kernel
private theorem c4746_ell   : LeafEll 4746    := by decide +kernel
private theorem c4746_nsq   : NSqChkSq 4746   := by decide +kernel
private theorem c4746_har   : HArithChkSq 4746 := by decide +kernel
private theorem c4746_r     : LeafR 4746      := by decide +kernel
private theorem c4746_e'    : LeafE' 4746     := by decide +kernel
private theorem c4746_f1    : LeafF1 4746     := Or.inl (by decide)
private theorem c4746_s2    : S2ChkSq 4746    := by decide +kernel
private theorem c4746_s3    : S3ChkSq 4746    := by decide +kernel
private theorem c4746_iso   : LeafIso 4746    := by decide +kernel
private theorem c4746_nof2  : NoF2ChkSq 4746  := by decide +kernel
private theorem c4746_nof3  : NoF3ChkSq 4746  := by decide +kernel
private theorem c4746_nof4z : NoF4zChkSq 4746 := by decide +kernel
theorem C'_4746 : C' 4746 :=
  ⟨c4746_sqf, c4746_range, c4746_ell, leafNSq_of_sq c4746_nsq, leafHAr_of_sq c4746_har,
   c4746_r, c4746_e', c4746_f1, leafS2_of_sq c4746_s2, leafS3_of_sq c4746_s3,
   c4746_iso, leafR8_of_sq c4746_nof2 c4746_nof3 c4746_nof4z⟩
theorem not_tile'_4746 (D : CongruentDissection 4746) : False :=
  not_tile_of_conditions' 4746 C'_4746 D

private theorem c4747_sqf   : LeafSqf 4747   := by decide +kernel
private theorem c4747_range : LeafRange 4747  := by decide +kernel
private theorem c4747_ell   : LeafEll 4747    := by decide +kernel
private theorem c4747_nsq   : NSqChkSq 4747   := by decide +kernel
private theorem c4747_har   : HArithChkSq 4747 := by decide +kernel
private theorem c4747_r     : LeafR 4747      := by decide +kernel
private theorem c4747_e'    : LeafE' 4747     := by decide +kernel
private theorem c4747_f1    : LeafF1 4747     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4747_s2    : S2ChkSq 4747    := by decide +kernel
private theorem c4747_s3    : S3ChkSq 4747    := by decide +kernel
private theorem c4747_iso   : LeafIso 4747    := by decide +kernel
private theorem c4747_nof2  : NoF2ChkSq 4747  := by decide +kernel
private theorem c4747_nof3  : NoF3ChkSq 4747  := by decide +kernel
private theorem c4747_nof4z : NoF4zChkSq 4747 := by decide +kernel
theorem C'_4747 : C' 4747 :=
  ⟨c4747_sqf, c4747_range, c4747_ell, leafNSq_of_sq c4747_nsq, leafHAr_of_sq c4747_har,
   c4747_r, c4747_e', c4747_f1, leafS2_of_sq c4747_s2, leafS3_of_sq c4747_s3,
   c4747_iso, leafR8_of_sq c4747_nof2 c4747_nof3 c4747_nof4z⟩
theorem not_tile'_4747 (D : CongruentDissection 4747) : False :=
  not_tile_of_conditions' 4747 C'_4747 D

private theorem c4749_sqf   : LeafSqf 4749   := by decide +kernel
private theorem c4749_range : LeafRange 4749  := by decide +kernel
private theorem c4749_ell   : LeafEll 4749    := by decide +kernel
private theorem c4749_nsq   : NSqChkSq 4749   := by decide +kernel
private theorem c4749_har   : HArithChkSq 4749 := by decide +kernel
private theorem c4749_r     : LeafR 4749      := by decide +kernel
private theorem c4749_e'    : LeafE' 4749     := by decide +kernel
private theorem c4749_f1    : LeafF1 4749     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4749_s2    : S2ChkSq 4749    := by decide +kernel
private theorem c4749_s3    : S3ChkSq 4749    := by decide +kernel
private theorem c4749_iso   : LeafIso 4749    := by decide +kernel
private theorem c4749_nof2  : NoF2ChkSq 4749  := by decide +kernel
private theorem c4749_nof3  : NoF3ChkSq 4749  := by decide +kernel
private theorem c4749_nof4z : NoF4zChkSq 4749 := by decide +kernel
theorem C'_4749 : C' 4749 :=
  ⟨c4749_sqf, c4749_range, c4749_ell, leafNSq_of_sq c4749_nsq, leafHAr_of_sq c4749_har,
   c4749_r, c4749_e', c4749_f1, leafS2_of_sq c4749_s2, leafS3_of_sq c4749_s3,
   c4749_iso, leafR8_of_sq c4749_nof2 c4749_nof3 c4749_nof4z⟩
theorem not_tile'_4749 (D : CongruentDissection 4749) : False :=
  not_tile_of_conditions' 4749 C'_4749 D

end Erdos634.Draft.AllN2

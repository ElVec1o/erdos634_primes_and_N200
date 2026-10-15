/- AllN2Check188: N = 3742, 3743, 3745, 3747, 3749
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3742_sqf   : LeafSqf 3742   := by decide +kernel
private theorem c3742_range : LeafRange 3742  := by decide +kernel
private theorem c3742_ell   : LeafEll 3742    := by decide +kernel
private theorem c3742_nsq   : NSqChkSq 3742   := by decide +kernel
private theorem c3742_har   : HArithChkSq 3742 := by decide +kernel
private theorem c3742_r     : LeafR 3742      := by decide +kernel
private theorem c3742_e'    : LeafE' 3742     := by decide +kernel
private theorem c3742_f1    : LeafF1 3742     := Or.inl (by decide)
private theorem c3742_s2    : S2ChkSq 3742    := by decide +kernel
private theorem c3742_s3    : S3ChkSq 3742    := by decide +kernel
private theorem c3742_iso   : LeafIso 3742    := by decide +kernel
private theorem c3742_nof2  : NoF2ChkSq 3742  := by decide +kernel
private theorem c3742_nof3  : NoF3ChkSq 3742  := by decide +kernel
private theorem c3742_nof4z : NoF4zChkSq 3742 := by decide +kernel
theorem C'_3742 : C' 3742 :=
  ⟨c3742_sqf, c3742_range, c3742_ell, leafNSq_of_sq c3742_nsq, leafHAr_of_sq c3742_har,
   c3742_r, c3742_e', c3742_f1, leafS2_of_sq c3742_s2, leafS3_of_sq c3742_s3,
   c3742_iso, leafR8_of_sq c3742_nof2 c3742_nof3 c3742_nof4z⟩
theorem not_tile'_3742 (D : CongruentDissection 3742) : False :=
  not_tile_of_conditions' 3742 C'_3742 D

private theorem c3743_sqf   : LeafSqf 3743   := by decide +kernel
private theorem c3743_range : LeafRange 3743  := by decide +kernel
private theorem c3743_ell   : LeafEll 3743    := by decide +kernel
private theorem c3743_nsq   : NSqChkSq 3743   := by decide +kernel
private theorem c3743_har   : HArithChkSq 3743 := by decide +kernel
private theorem c3743_r     : LeafR 3743      := by decide +kernel
private theorem c3743_e'    : LeafE' 3743     := by decide +kernel
private theorem c3743_f1    : LeafF1 3743     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3743_s2    : S2ChkSq 3743    := by decide +kernel
private theorem c3743_s3    : S3ChkSq 3743    := by decide +kernel
private theorem c3743_iso   : LeafIso 3743    := by decide +kernel
private theorem c3743_nof2  : NoF2ChkSq 3743  := by decide +kernel
private theorem c3743_nof3  : NoF3ChkSq 3743  := by decide +kernel
private theorem c3743_nof4z : NoF4zChkSq 3743 := by decide +kernel
theorem C'_3743 : C' 3743 :=
  ⟨c3743_sqf, c3743_range, c3743_ell, leafNSq_of_sq c3743_nsq, leafHAr_of_sq c3743_har,
   c3743_r, c3743_e', c3743_f1, leafS2_of_sq c3743_s2, leafS3_of_sq c3743_s3,
   c3743_iso, leafR8_of_sq c3743_nof2 c3743_nof3 c3743_nof4z⟩
theorem not_tile'_3743 (D : CongruentDissection 3743) : False :=
  not_tile_of_conditions' 3743 C'_3743 D

private theorem c3745_sqf   : LeafSqf 3745   := by decide +kernel
private theorem c3745_range : LeafRange 3745  := by decide +kernel
private theorem c3745_ell   : LeafEll 3745    := by decide +kernel
private theorem c3745_nsq   : NSqChkSq 3745   := by decide +kernel
private theorem c3745_har   : HArithChkSq 3745 := by decide +kernel
private theorem c3745_r     : LeafR 3745      := by decide +kernel
private theorem c3745_e'    : LeafE' 3745     := by decide +kernel
private theorem c3745_f1    : LeafF1 3745     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3745_s2    : S2ChkSq 3745    := by decide +kernel
private theorem c3745_s3    : S3ChkSq 3745    := by decide +kernel
private theorem c3745_iso   : LeafIso 3745    := by decide +kernel
private theorem c3745_nof2  : NoF2ChkSq 3745  := by decide +kernel
private theorem c3745_nof3  : NoF3ChkSq 3745  := by decide +kernel
private theorem c3745_nof4z : NoF4zChkSq 3745 := by decide +kernel
theorem C'_3745 : C' 3745 :=
  ⟨c3745_sqf, c3745_range, c3745_ell, leafNSq_of_sq c3745_nsq, leafHAr_of_sq c3745_har,
   c3745_r, c3745_e', c3745_f1, leafS2_of_sq c3745_s2, leafS3_of_sq c3745_s3,
   c3745_iso, leafR8_of_sq c3745_nof2 c3745_nof3 c3745_nof4z⟩
theorem not_tile'_3745 (D : CongruentDissection 3745) : False :=
  not_tile_of_conditions' 3745 C'_3745 D

private theorem c3747_sqf   : LeafSqf 3747   := by decide +kernel
private theorem c3747_range : LeafRange 3747  := by decide +kernel
private theorem c3747_ell   : LeafEll 3747    := by decide +kernel
private theorem c3747_nsq   : NSqChkSq 3747   := by decide +kernel
private theorem c3747_har   : HArithChkSq 3747 := by decide +kernel
private theorem c3747_r     : LeafR 3747      := by decide +kernel
private theorem c3747_e'    : LeafE' 3747     := by decide +kernel
private theorem c3747_f1    : LeafF1 3747     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3747_s2    : S2ChkSq 3747    := by decide +kernel
private theorem c3747_s3    : S3ChkSq 3747    := by decide +kernel
private theorem c3747_iso   : LeafIso 3747    := by decide +kernel
private theorem c3747_nof2  : NoF2ChkSq 3747  := by decide +kernel
private theorem c3747_nof3  : NoF3ChkSq 3747  := by decide +kernel
private theorem c3747_nof4z : NoF4zChkSq 3747 := by decide +kernel
theorem C'_3747 : C' 3747 :=
  ⟨c3747_sqf, c3747_range, c3747_ell, leafNSq_of_sq c3747_nsq, leafHAr_of_sq c3747_har,
   c3747_r, c3747_e', c3747_f1, leafS2_of_sq c3747_s2, leafS3_of_sq c3747_s3,
   c3747_iso, leafR8_of_sq c3747_nof2 c3747_nof3 c3747_nof4z⟩
theorem not_tile'_3747 (D : CongruentDissection 3747) : False :=
  not_tile_of_conditions' 3747 C'_3747 D

private theorem c3749_sqf   : LeafSqf 3749   := by decide +kernel
private theorem c3749_range : LeafRange 3749  := by decide +kernel
private theorem c3749_ell   : LeafEll 3749    := by decide +kernel
private theorem c3749_nsq   : NSqChkSq 3749   := by decide +kernel
private theorem c3749_har   : HArithChkSq 3749 := by decide +kernel
private theorem c3749_r     : LeafR 3749      := by decide +kernel
private theorem c3749_e'    : LeafE' 3749     := by decide +kernel
private theorem c3749_f1    : LeafF1 3749     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3749_s2    : S2ChkSq 3749    := by decide +kernel
private theorem c3749_s3    : S3ChkSq 3749    := by decide +kernel
private theorem c3749_iso   : LeafIso 3749    := by decide +kernel
private theorem c3749_nof2  : NoF2ChkSq 3749  := by decide +kernel
private theorem c3749_nof3  : NoF3ChkSq 3749  := by decide +kernel
private theorem c3749_nof4z : NoF4zChkSq 3749 := by decide +kernel
theorem C'_3749 : C' 3749 :=
  ⟨c3749_sqf, c3749_range, c3749_ell, leafNSq_of_sq c3749_nsq, leafHAr_of_sq c3749_har,
   c3749_r, c3749_e', c3749_f1, leafS2_of_sq c3749_s2, leafS3_of_sq c3749_s3,
   c3749_iso, leafR8_of_sq c3749_nof2 c3749_nof3 c3749_nof4z⟩
theorem not_tile'_3749 (D : CongruentDissection 3749) : False :=
  not_tile_of_conditions' 3749 C'_3749 D

end Erdos634.Draft.AllN2

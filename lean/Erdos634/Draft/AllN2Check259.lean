/- AllN2Check259: N = 4654, 4659, 4661, 4663, 4667
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4654_sqf   : LeafSqf 4654   := by decide +kernel
private theorem c4654_range : LeafRange 4654  := by decide +kernel
private theorem c4654_ell   : LeafEll 4654    := by decide +kernel
private theorem c4654_nsq   : NSqChkSq 4654   := by decide +kernel
private theorem c4654_har   : HArithChkSq 4654 := by decide +kernel
private theorem c4654_r     : LeafR 4654      := by decide +kernel
private theorem c4654_e'    : LeafE' 4654     := by decide +kernel
private theorem c4654_f1    : LeafF1 4654     := Or.inl (by decide)
private theorem c4654_s2    : S2ChkSq 4654    := by decide +kernel
private theorem c4654_s3    : S3ChkSq 4654    := by decide +kernel
private theorem c4654_iso   : LeafIso 4654    := by decide +kernel
private theorem c4654_nof2  : NoF2ChkSq 4654  := by decide +kernel
private theorem c4654_nof3  : NoF3ChkSq 4654  := by decide +kernel
private theorem c4654_nof4z : NoF4zChkSq 4654 := by decide +kernel
theorem C'_4654 : C' 4654 :=
  ⟨c4654_sqf, c4654_range, c4654_ell, leafNSq_of_sq c4654_nsq, leafHAr_of_sq c4654_har,
   c4654_r, c4654_e', c4654_f1, leafS2_of_sq c4654_s2, leafS3_of_sq c4654_s3,
   c4654_iso, leafR8_of_sq c4654_nof2 c4654_nof3 c4654_nof4z⟩
theorem not_tile'_4654 (D : CongruentDissection 4654) : False :=
  not_tile_of_conditions' 4654 C'_4654 D

private theorem c4659_sqf   : LeafSqf 4659   := by decide +kernel
private theorem c4659_range : LeafRange 4659  := by decide +kernel
private theorem c4659_ell   : LeafEll 4659    := by decide +kernel
private theorem c4659_nsq   : NSqChkSq 4659   := by decide +kernel
private theorem c4659_har   : HArithChkSq 4659 := by decide +kernel
private theorem c4659_r     : LeafR 4659      := by decide +kernel
private theorem c4659_e'    : LeafE' 4659     := by decide +kernel
private theorem c4659_f1    : LeafF1 4659     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4659_s2    : S2ChkSq 4659    := by decide +kernel
private theorem c4659_s3    : S3ChkSq 4659    := by decide +kernel
private theorem c4659_iso   : LeafIso 4659    := by decide +kernel
private theorem c4659_nof2  : NoF2ChkSq 4659  := by decide +kernel
private theorem c4659_nof3  : NoF3ChkSq 4659  := by decide +kernel
private theorem c4659_nof4z : NoF4zChkSq 4659 := by decide +kernel
theorem C'_4659 : C' 4659 :=
  ⟨c4659_sqf, c4659_range, c4659_ell, leafNSq_of_sq c4659_nsq, leafHAr_of_sq c4659_har,
   c4659_r, c4659_e', c4659_f1, leafS2_of_sq c4659_s2, leafS3_of_sq c4659_s3,
   c4659_iso, leafR8_of_sq c4659_nof2 c4659_nof3 c4659_nof4z⟩
theorem not_tile'_4659 (D : CongruentDissection 4659) : False :=
  not_tile_of_conditions' 4659 C'_4659 D

private theorem c4661_sqf   : LeafSqf 4661   := by decide +kernel
private theorem c4661_range : LeafRange 4661  := by decide +kernel
private theorem c4661_ell   : LeafEll 4661    := by decide +kernel
private theorem c4661_nsq   : NSqChkSq 4661   := by decide +kernel
private theorem c4661_har   : HArithChkSq 4661 := by decide +kernel
private theorem c4661_r     : LeafR 4661      := by decide +kernel
private theorem c4661_e'    : LeafE' 4661     := by decide +kernel
private theorem c4661_f1    : LeafF1 4661     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4661_s2    : S2ChkSq 4661    := by decide +kernel
private theorem c4661_s3    : S3ChkSq 4661    := by decide +kernel
private theorem c4661_iso   : LeafIso 4661    := by decide +kernel
private theorem c4661_nof2  : NoF2ChkSq 4661  := by decide +kernel
private theorem c4661_nof3  : NoF3ChkSq 4661  := by decide +kernel
private theorem c4661_nof4z : NoF4zChkSq 4661 := by decide +kernel
theorem C'_4661 : C' 4661 :=
  ⟨c4661_sqf, c4661_range, c4661_ell, leafNSq_of_sq c4661_nsq, leafHAr_of_sq c4661_har,
   c4661_r, c4661_e', c4661_f1, leafS2_of_sq c4661_s2, leafS3_of_sq c4661_s3,
   c4661_iso, leafR8_of_sq c4661_nof2 c4661_nof3 c4661_nof4z⟩
theorem not_tile'_4661 (D : CongruentDissection 4661) : False :=
  not_tile_of_conditions' 4661 C'_4661 D

private theorem c4663_sqf   : LeafSqf 4663   := by decide +kernel
private theorem c4663_range : LeafRange 4663  := by decide +kernel
private theorem c4663_ell   : LeafEll 4663    := by decide +kernel
private theorem c4663_nsq   : NSqChkSq 4663   := by decide +kernel
private theorem c4663_har   : HArithChkSq 4663 := by decide +kernel
private theorem c4663_r     : LeafR 4663      := by decide +kernel
private theorem c4663_e'    : LeafE' 4663     := by decide +kernel
private theorem c4663_f1    : LeafF1 4663     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4663_s2    : S2ChkSq 4663    := by decide +kernel
private theorem c4663_s3    : S3ChkSq 4663    := by decide +kernel
private theorem c4663_iso   : LeafIso 4663    := by decide +kernel
private theorem c4663_nof2  : NoF2ChkSq 4663  := by decide +kernel
private theorem c4663_nof3  : NoF3ChkSq 4663  := by decide +kernel
private theorem c4663_nof4z : NoF4zChkSq 4663 := by decide +kernel
theorem C'_4663 : C' 4663 :=
  ⟨c4663_sqf, c4663_range, c4663_ell, leafNSq_of_sq c4663_nsq, leafHAr_of_sq c4663_har,
   c4663_r, c4663_e', c4663_f1, leafS2_of_sq c4663_s2, leafS3_of_sq c4663_s3,
   c4663_iso, leafR8_of_sq c4663_nof2 c4663_nof3 c4663_nof4z⟩
theorem not_tile'_4663 (D : CongruentDissection 4663) : False :=
  not_tile_of_conditions' 4663 C'_4663 D

private theorem c4667_sqf   : LeafSqf 4667   := by decide +kernel
private theorem c4667_range : LeafRange 4667  := by decide +kernel
private theorem c4667_ell   : LeafEll 4667    := by decide +kernel
private theorem c4667_nsq   : NSqChkSq 4667   := by decide +kernel
private theorem c4667_har   : HArithChkSq 4667 := by decide +kernel
private theorem c4667_r     : LeafR 4667      := by decide +kernel
private theorem c4667_e'    : LeafE' 4667     := by decide +kernel
private theorem c4667_f1    : LeafF1 4667     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4667_s2    : S2ChkSq 4667    := by decide +kernel
private theorem c4667_s3    : S3ChkSq 4667    := by decide +kernel
private theorem c4667_iso   : LeafIso 4667    := by decide +kernel
private theorem c4667_nof2  : NoF2ChkSq 4667  := by decide +kernel
private theorem c4667_nof3  : NoF3ChkSq 4667  := by decide +kernel
private theorem c4667_nof4z : NoF4zChkSq 4667 := by decide +kernel
theorem C'_4667 : C' 4667 :=
  ⟨c4667_sqf, c4667_range, c4667_ell, leafNSq_of_sq c4667_nsq, leafHAr_of_sq c4667_har,
   c4667_r, c4667_e', c4667_f1, leafS2_of_sq c4667_s2, leafS3_of_sq c4667_s3,
   c4667_iso, leafR8_of_sq c4667_nof2 c4667_nof3 c4667_nof4z⟩
theorem not_tile'_4667 (D : CongruentDissection 4667) : False :=
  not_tile_of_conditions' 4667 C'_4667 D

end Erdos634.Draft.AllN2

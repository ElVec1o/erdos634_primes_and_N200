/- AllN2Check41: N = 1655, 1661, 1671, 1673, 1687
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1655_sqf   : LeafSqf 1655   := by decide +kernel
private theorem c1655_range : LeafRange 1655  := by decide +kernel
private theorem c1655_ell   : LeafEll 1655    := by decide +kernel
private theorem c1655_nsq   : NSqChkSq 1655   := by decide +kernel
private theorem c1655_har   : HArithChkSq 1655 := by decide +kernel
private theorem c1655_r     : LeafR 1655      := by decide +kernel
private theorem c1655_e'    : LeafE' 1655     := by decide +kernel
private theorem c1655_f1    : LeafF1 1655     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1655_s2    : S2ChkSq 1655    := by decide +kernel
private theorem c1655_s3    : S3ChkSq 1655    := by decide +kernel
private theorem c1655_iso   : LeafIso 1655    := by decide +kernel
private theorem c1655_nof2  : NoF2ChkSq 1655  := by decide +kernel
private theorem c1655_nof3  : NoF3ChkSq 1655  := by decide +kernel
private theorem c1655_nof4z : NoF4zChkSq 1655 := by decide +kernel
theorem C'_1655 : C' 1655 :=
  ⟨c1655_sqf, c1655_range, c1655_ell, leafNSq_of_sq c1655_nsq, leafHAr_of_sq c1655_har,
   c1655_r, c1655_e', c1655_f1, leafS2_of_sq c1655_s2, leafS3_of_sq c1655_s3,
   c1655_iso, leafR8_of_sq c1655_nof2 c1655_nof3 c1655_nof4z⟩
theorem not_tile'_1655 (D : CongruentDissection 1655) : False :=
  not_tile_of_conditions' 1655 C'_1655 D

private theorem c1661_sqf   : LeafSqf 1661   := by decide +kernel
private theorem c1661_range : LeafRange 1661  := by decide +kernel
private theorem c1661_ell   : LeafEll 1661    := by decide +kernel
private theorem c1661_nsq   : NSqChkSq 1661   := by decide +kernel
private theorem c1661_har   : HArithChkSq 1661 := by decide +kernel
private theorem c1661_r     : LeafR 1661      := by decide +kernel
private theorem c1661_e'    : LeafE' 1661     := by decide +kernel
private theorem c1661_f1    : LeafF1 1661     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1661_s2    : S2ChkSq 1661    := by decide +kernel
private theorem c1661_s3    : S3ChkSq 1661    := by decide +kernel
private theorem c1661_iso   : LeafIso 1661    := by decide +kernel
private theorem c1661_nof2  : NoF2ChkSq 1661  := by decide +kernel
private theorem c1661_nof3  : NoF3ChkSq 1661  := by decide +kernel
private theorem c1661_nof4z : NoF4zChkSq 1661 := by decide +kernel
theorem C'_1661 : C' 1661 :=
  ⟨c1661_sqf, c1661_range, c1661_ell, leafNSq_of_sq c1661_nsq, leafHAr_of_sq c1661_har,
   c1661_r, c1661_e', c1661_f1, leafS2_of_sq c1661_s2, leafS3_of_sq c1661_s3,
   c1661_iso, leafR8_of_sq c1661_nof2 c1661_nof3 c1661_nof4z⟩
theorem not_tile'_1661 (D : CongruentDissection 1661) : False :=
  not_tile_of_conditions' 1661 C'_1661 D

private theorem c1671_sqf   : LeafSqf 1671   := by decide +kernel
private theorem c1671_range : LeafRange 1671  := by decide +kernel
private theorem c1671_ell   : LeafEll 1671    := by decide +kernel
private theorem c1671_nsq   : NSqChkSq 1671   := by decide +kernel
private theorem c1671_har   : HArithChkSq 1671 := by decide +kernel
private theorem c1671_r     : LeafR 1671      := by decide +kernel
private theorem c1671_e'    : LeafE' 1671     := by decide +kernel
private theorem c1671_f1    : LeafF1 1671     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1671_s2    : S2ChkSq 1671    := by decide +kernel
private theorem c1671_s3    : S3ChkSq 1671    := by decide +kernel
private theorem c1671_iso   : LeafIso 1671    := by decide +kernel
private theorem c1671_nof2  : NoF2ChkSq 1671  := by decide +kernel
private theorem c1671_nof3  : NoF3ChkSq 1671  := by decide +kernel
private theorem c1671_nof4z : NoF4zChkSq 1671 := by decide +kernel
theorem C'_1671 : C' 1671 :=
  ⟨c1671_sqf, c1671_range, c1671_ell, leafNSq_of_sq c1671_nsq, leafHAr_of_sq c1671_har,
   c1671_r, c1671_e', c1671_f1, leafS2_of_sq c1671_s2, leafS3_of_sq c1671_s3,
   c1671_iso, leafR8_of_sq c1671_nof2 c1671_nof3 c1671_nof4z⟩
theorem not_tile'_1671 (D : CongruentDissection 1671) : False :=
  not_tile_of_conditions' 1671 C'_1671 D

private theorem c1673_sqf   : LeafSqf 1673   := by decide +kernel
private theorem c1673_range : LeafRange 1673  := by decide +kernel
private theorem c1673_ell   : LeafEll 1673    := by decide +kernel
private theorem c1673_nsq   : NSqChkSq 1673   := by decide +kernel
private theorem c1673_har   : HArithChkSq 1673 := by decide +kernel
private theorem c1673_r     : LeafR 1673      := by decide +kernel
private theorem c1673_e'    : LeafE' 1673     := by decide +kernel
private theorem c1673_f1    : LeafF1 1673     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1673_s2    : S2ChkSq 1673    := by decide +kernel
private theorem c1673_s3    : S3ChkSq 1673    := by decide +kernel
private theorem c1673_iso   : LeafIso 1673    := by decide +kernel
private theorem c1673_nof2  : NoF2ChkSq 1673  := by decide +kernel
private theorem c1673_nof3  : NoF3ChkSq 1673  := by decide +kernel
private theorem c1673_nof4z : NoF4zChkSq 1673 := by decide +kernel
theorem C'_1673 : C' 1673 :=
  ⟨c1673_sqf, c1673_range, c1673_ell, leafNSq_of_sq c1673_nsq, leafHAr_of_sq c1673_har,
   c1673_r, c1673_e', c1673_f1, leafS2_of_sq c1673_s2, leafS3_of_sq c1673_s3,
   c1673_iso, leafR8_of_sq c1673_nof2 c1673_nof3 c1673_nof4z⟩
theorem not_tile'_1673 (D : CongruentDissection 1673) : False :=
  not_tile_of_conditions' 1673 C'_1673 D

private theorem c1687_sqf   : LeafSqf 1687   := by decide +kernel
private theorem c1687_range : LeafRange 1687  := by decide +kernel
private theorem c1687_ell   : LeafEll 1687    := by decide +kernel
private theorem c1687_nsq   : NSqChkSq 1687   := by decide +kernel
private theorem c1687_har   : HArithChkSq 1687 := by decide +kernel
private theorem c1687_r     : LeafR 1687      := by decide +kernel
private theorem c1687_e'    : LeafE' 1687     := by decide +kernel
private theorem c1687_f1    : LeafF1 1687     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1687_s2    : S2ChkSq 1687    := by decide +kernel
private theorem c1687_s3    : S3ChkSq 1687    := by decide +kernel
private theorem c1687_iso   : LeafIso 1687    := by decide +kernel
private theorem c1687_nof2  : NoF2ChkSq 1687  := by decide +kernel
private theorem c1687_nof3  : NoF3ChkSq 1687  := by decide +kernel
private theorem c1687_nof4z : NoF4zChkSq 1687 := by decide +kernel
theorem C'_1687 : C' 1687 :=
  ⟨c1687_sqf, c1687_range, c1687_ell, leafNSq_of_sq c1687_nsq, leafHAr_of_sq c1687_har,
   c1687_r, c1687_e', c1687_f1, leafS2_of_sq c1687_s2, leafS3_of_sq c1687_s3,
   c1687_iso, leafR8_of_sq c1687_nof2 c1687_nof3 c1687_nof4z⟩
theorem not_tile'_1687 (D : CongruentDissection 1687) : False :=
  not_tile_of_conditions' 1687 C'_1687 D

end Erdos634.Draft.AllN2

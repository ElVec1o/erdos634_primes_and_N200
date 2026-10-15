/- AllN2Check178: N = 3622, 3623, 3629, 3631, 3634
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3622_sqf   : LeafSqf 3622   := by decide +kernel
private theorem c3622_range : LeafRange 3622  := by decide +kernel
private theorem c3622_ell   : LeafEll 3622    := by decide +kernel
private theorem c3622_nsq   : NSqChkSq 3622   := by decide +kernel
private theorem c3622_har   : HArithChkSq 3622 := by decide +kernel
private theorem c3622_r     : LeafR 3622      := by decide +kernel
private theorem c3622_e'    : LeafE' 3622     := by decide +kernel
private theorem c3622_f1    : LeafF1 3622     := Or.inl (by decide)
private theorem c3622_s2    : S2ChkSq 3622    := by decide +kernel
private theorem c3622_s3    : S3ChkSq 3622    := by decide +kernel
private theorem c3622_iso   : LeafIso 3622    := by decide +kernel
private theorem c3622_nof2  : NoF2ChkSq 3622  := by decide +kernel
private theorem c3622_nof3  : NoF3ChkSq 3622  := by decide +kernel
private theorem c3622_nof4z : NoF4zChkSq 3622 := by decide +kernel
theorem C'_3622 : C' 3622 :=
  ⟨c3622_sqf, c3622_range, c3622_ell, leafNSq_of_sq c3622_nsq, leafHAr_of_sq c3622_har,
   c3622_r, c3622_e', c3622_f1, leafS2_of_sq c3622_s2, leafS3_of_sq c3622_s3,
   c3622_iso, leafR8_of_sq c3622_nof2 c3622_nof3 c3622_nof4z⟩
theorem not_tile'_3622 (D : CongruentDissection 3622) : False :=
  not_tile_of_conditions' 3622 C'_3622 D

private theorem c3623_sqf   : LeafSqf 3623   := by decide +kernel
private theorem c3623_range : LeafRange 3623  := by decide +kernel
private theorem c3623_ell   : LeafEll 3623    := by decide +kernel
private theorem c3623_nsq   : NSqChkSq 3623   := by decide +kernel
private theorem c3623_har   : HArithChkSq 3623 := by decide +kernel
private theorem c3623_r     : LeafR 3623      := by decide +kernel
private theorem c3623_e'    : LeafE' 3623     := by decide +kernel
private theorem c3623_f1    : LeafF1 3623     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3623_s2    : S2ChkSq 3623    := by decide +kernel
private theorem c3623_s3    : S3ChkSq 3623    := by decide +kernel
private theorem c3623_iso   : LeafIso 3623    := by decide +kernel
private theorem c3623_nof2  : NoF2ChkSq 3623  := by decide +kernel
private theorem c3623_nof3  : NoF3ChkSq 3623  := by decide +kernel
private theorem c3623_nof4z : NoF4zChkSq 3623 := by decide +kernel
theorem C'_3623 : C' 3623 :=
  ⟨c3623_sqf, c3623_range, c3623_ell, leafNSq_of_sq c3623_nsq, leafHAr_of_sq c3623_har,
   c3623_r, c3623_e', c3623_f1, leafS2_of_sq c3623_s2, leafS3_of_sq c3623_s3,
   c3623_iso, leafR8_of_sq c3623_nof2 c3623_nof3 c3623_nof4z⟩
theorem not_tile'_3623 (D : CongruentDissection 3623) : False :=
  not_tile_of_conditions' 3623 C'_3623 D

private theorem c3629_sqf   : LeafSqf 3629   := by decide +kernel
private theorem c3629_range : LeafRange 3629  := by decide +kernel
private theorem c3629_ell   : LeafEll 3629    := by decide +kernel
private theorem c3629_nsq   : NSqChkSq 3629   := by decide +kernel
private theorem c3629_har   : HArithChkSq 3629 := by decide +kernel
private theorem c3629_r     : LeafR 3629      := by decide +kernel
private theorem c3629_e'    : LeafE' 3629     := by decide +kernel
private theorem c3629_f1    : LeafF1 3629     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3629_s2    : S2ChkSq 3629    := by decide +kernel
private theorem c3629_s3    : S3ChkSq 3629    := by decide +kernel
private theorem c3629_iso   : LeafIso 3629    := by decide +kernel
private theorem c3629_nof2  : NoF2ChkSq 3629  := by decide +kernel
private theorem c3629_nof3  : NoF3ChkSq 3629  := by decide +kernel
private theorem c3629_nof4z : NoF4zChkSq 3629 := by decide +kernel
theorem C'_3629 : C' 3629 :=
  ⟨c3629_sqf, c3629_range, c3629_ell, leafNSq_of_sq c3629_nsq, leafHAr_of_sq c3629_har,
   c3629_r, c3629_e', c3629_f1, leafS2_of_sq c3629_s2, leafS3_of_sq c3629_s3,
   c3629_iso, leafR8_of_sq c3629_nof2 c3629_nof3 c3629_nof4z⟩
theorem not_tile'_3629 (D : CongruentDissection 3629) : False :=
  not_tile_of_conditions' 3629 C'_3629 D

private theorem c3631_sqf   : LeafSqf 3631   := by decide +kernel
private theorem c3631_range : LeafRange 3631  := by decide +kernel
private theorem c3631_ell   : LeafEll 3631    := by decide +kernel
private theorem c3631_nsq   : NSqChkSq 3631   := by decide +kernel
private theorem c3631_har   : HArithChkSq 3631 := by decide +kernel
private theorem c3631_r     : LeafR 3631      := by decide +kernel
private theorem c3631_e'    : LeafE' 3631     := by decide +kernel
private theorem c3631_f1    : LeafF1 3631     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3631_s2    : S2ChkSq 3631    := by decide +kernel
private theorem c3631_s3    : S3ChkSq 3631    := by decide +kernel
private theorem c3631_iso   : LeafIso 3631    := by decide +kernel
private theorem c3631_nof2  : NoF2ChkSq 3631  := by decide +kernel
private theorem c3631_nof3  : NoF3ChkSq 3631  := by decide +kernel
private theorem c3631_nof4z : NoF4zChkSq 3631 := by decide +kernel
theorem C'_3631 : C' 3631 :=
  ⟨c3631_sqf, c3631_range, c3631_ell, leafNSq_of_sq c3631_nsq, leafHAr_of_sq c3631_har,
   c3631_r, c3631_e', c3631_f1, leafS2_of_sq c3631_s2, leafS3_of_sq c3631_s3,
   c3631_iso, leafR8_of_sq c3631_nof2 c3631_nof3 c3631_nof4z⟩
theorem not_tile'_3631 (D : CongruentDissection 3631) : False :=
  not_tile_of_conditions' 3631 C'_3631 D

private theorem c3634_sqf   : LeafSqf 3634   := by decide +kernel
private theorem c3634_range : LeafRange 3634  := by decide +kernel
private theorem c3634_ell   : LeafEll 3634    := by decide +kernel
private theorem c3634_nsq   : NSqChkSq 3634   := by decide +kernel
private theorem c3634_har   : HArithChkSq 3634 := by decide +kernel
private theorem c3634_r     : LeafR 3634      := by decide +kernel
private theorem c3634_e'    : LeafE' 3634     := by decide +kernel
private theorem c3634_f1    : LeafF1 3634     := Or.inl (by decide)
private theorem c3634_s2    : S2ChkSq 3634    := by decide +kernel
private theorem c3634_s3    : S3ChkSq 3634    := by decide +kernel
private theorem c3634_iso   : LeafIso 3634    := by decide +kernel
private theorem c3634_nof2  : NoF2ChkSq 3634  := by decide +kernel
private theorem c3634_nof3  : NoF3ChkSq 3634  := by decide +kernel
private theorem c3634_nof4z : NoF4zChkSq 3634 := by decide +kernel
theorem C'_3634 : C' 3634 :=
  ⟨c3634_sqf, c3634_range, c3634_ell, leafNSq_of_sq c3634_nsq, leafHAr_of_sq c3634_har,
   c3634_r, c3634_e', c3634_f1, leafS2_of_sq c3634_s2, leafS3_of_sq c3634_s3,
   c3634_iso, leafR8_of_sq c3634_nof2 c3634_nof3 c3634_nof4z⟩
theorem not_tile'_3634 (D : CongruentDissection 3634) : False :=
  not_tile_of_conditions' 3634 C'_3634 D

end Erdos634.Draft.AllN2

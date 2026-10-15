/- AllN2Check256: N = 4619, 4622, 4623, 4627, 4629
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4619_sqf   : LeafSqf 4619   := by decide +kernel
private theorem c4619_range : LeafRange 4619  := by decide +kernel
private theorem c4619_ell   : LeafEll 4619    := by decide +kernel
private theorem c4619_nsq   : NSqChkSq 4619   := by decide +kernel
private theorem c4619_har   : HArithChkSq 4619 := by decide +kernel
private theorem c4619_r     : LeafR 4619      := by decide +kernel
private theorem c4619_e'    : LeafE' 4619     := by decide +kernel
private theorem c4619_f1    : LeafF1 4619     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4619_s2    : S2ChkSq 4619    := by decide +kernel
private theorem c4619_s3    : S3ChkSq 4619    := by decide +kernel
private theorem c4619_iso   : LeafIso 4619    := by decide +kernel
private theorem c4619_nof2  : NoF2ChkSq 4619  := by decide +kernel
private theorem c4619_nof3  : NoF3ChkSq 4619  := by decide +kernel
private theorem c4619_nof4z : NoF4zChkSq 4619 := by decide +kernel
theorem C'_4619 : C' 4619 :=
  ⟨c4619_sqf, c4619_range, c4619_ell, leafNSq_of_sq c4619_nsq, leafHAr_of_sq c4619_har,
   c4619_r, c4619_e', c4619_f1, leafS2_of_sq c4619_s2, leafS3_of_sq c4619_s3,
   c4619_iso, leafR8_of_sq c4619_nof2 c4619_nof3 c4619_nof4z⟩
theorem not_tile'_4619 (D : CongruentDissection 4619) : False :=
  not_tile_of_conditions' 4619 C'_4619 D

private theorem c4622_sqf   : LeafSqf 4622   := by decide +kernel
private theorem c4622_range : LeafRange 4622  := by decide +kernel
private theorem c4622_ell   : LeafEll 4622    := by decide +kernel
private theorem c4622_nsq   : NSqChkSq 4622   := by decide +kernel
private theorem c4622_har   : HArithChkSq 4622 := by decide +kernel
private theorem c4622_r     : LeafR 4622      := by decide +kernel
private theorem c4622_e'    : LeafE' 4622     := by decide +kernel
private theorem c4622_f1    : LeafF1 4622     := Or.inl (by decide)
private theorem c4622_s2    : S2ChkSq 4622    := by decide +kernel
private theorem c4622_s3    : S3ChkSq 4622    := by decide +kernel
private theorem c4622_iso   : LeafIso 4622    := by decide +kernel
private theorem c4622_nof2  : NoF2ChkSq 4622  := by decide +kernel
private theorem c4622_nof3  : NoF3ChkSq 4622  := by decide +kernel
private theorem c4622_nof4z : NoF4zChkSq 4622 := by decide +kernel
theorem C'_4622 : C' 4622 :=
  ⟨c4622_sqf, c4622_range, c4622_ell, leafNSq_of_sq c4622_nsq, leafHAr_of_sq c4622_har,
   c4622_r, c4622_e', c4622_f1, leafS2_of_sq c4622_s2, leafS3_of_sq c4622_s3,
   c4622_iso, leafR8_of_sq c4622_nof2 c4622_nof3 c4622_nof4z⟩
theorem not_tile'_4622 (D : CongruentDissection 4622) : False :=
  not_tile_of_conditions' 4622 C'_4622 D

private theorem c4623_sqf   : LeafSqf 4623   := by decide +kernel
private theorem c4623_range : LeafRange 4623  := by decide +kernel
private theorem c4623_ell   : LeafEll 4623    := by decide +kernel
private theorem c4623_nsq   : NSqChkSq 4623   := by decide +kernel
private theorem c4623_har   : HArithChkSq 4623 := by decide +kernel
private theorem c4623_r     : LeafR 4623      := by decide +kernel
private theorem c4623_e'    : LeafE' 4623     := by decide +kernel
private theorem c4623_f1    : LeafF1 4623     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4623_s2    : S2ChkSq 4623    := by decide +kernel
private theorem c4623_s3    : S3ChkSq 4623    := by decide +kernel
private theorem c4623_iso   : LeafIso 4623    := by decide +kernel
private theorem c4623_nof2  : NoF2ChkSq 4623  := by decide +kernel
private theorem c4623_nof3  : NoF3ChkSq 4623  := by decide +kernel
private theorem c4623_nof4z : NoF4zChkSq 4623 := by decide +kernel
theorem C'_4623 : C' 4623 :=
  ⟨c4623_sqf, c4623_range, c4623_ell, leafNSq_of_sq c4623_nsq, leafHAr_of_sq c4623_har,
   c4623_r, c4623_e', c4623_f1, leafS2_of_sq c4623_s2, leafS3_of_sq c4623_s3,
   c4623_iso, leafR8_of_sq c4623_nof2 c4623_nof3 c4623_nof4z⟩
theorem not_tile'_4623 (D : CongruentDissection 4623) : False :=
  not_tile_of_conditions' 4623 C'_4623 D

private theorem c4627_sqf   : LeafSqf 4627   := by decide +kernel
private theorem c4627_range : LeafRange 4627  := by decide +kernel
private theorem c4627_ell   : LeafEll 4627    := by decide +kernel
private theorem c4627_nsq   : NSqChkSq 4627   := by decide +kernel
private theorem c4627_har   : HArithChkSq 4627 := by decide +kernel
private theorem c4627_r     : LeafR 4627      := by decide +kernel
private theorem c4627_e'    : LeafE' 4627     := by decide +kernel
private theorem c4627_f1    : LeafF1 4627     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4627_s2    : S2ChkSq 4627    := by decide +kernel
private theorem c4627_s3    : S3ChkSq 4627    := by decide +kernel
private theorem c4627_iso   : LeafIso 4627    := by decide +kernel
private theorem c4627_nof2  : NoF2ChkSq 4627  := by decide +kernel
private theorem c4627_nof3  : NoF3ChkSq 4627  := by decide +kernel
private theorem c4627_nof4z : NoF4zChkSq 4627 := by decide +kernel
theorem C'_4627 : C' 4627 :=
  ⟨c4627_sqf, c4627_range, c4627_ell, leafNSq_of_sq c4627_nsq, leafHAr_of_sq c4627_har,
   c4627_r, c4627_e', c4627_f1, leafS2_of_sq c4627_s2, leafS3_of_sq c4627_s3,
   c4627_iso, leafR8_of_sq c4627_nof2 c4627_nof3 c4627_nof4z⟩
theorem not_tile'_4627 (D : CongruentDissection 4627) : False :=
  not_tile_of_conditions' 4627 C'_4627 D

private theorem c4629_sqf   : LeafSqf 4629   := by decide +kernel
private theorem c4629_range : LeafRange 4629  := by decide +kernel
private theorem c4629_ell   : LeafEll 4629    := by decide +kernel
private theorem c4629_nsq   : NSqChkSq 4629   := by decide +kernel
private theorem c4629_har   : HArithChkSq 4629 := by decide +kernel
private theorem c4629_r     : LeafR 4629      := by decide +kernel
private theorem c4629_e'    : LeafE' 4629     := by decide +kernel
private theorem c4629_f1    : LeafF1 4629     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4629_s2    : S2ChkSq 4629    := by decide +kernel
private theorem c4629_s3    : S3ChkSq 4629    := by decide +kernel
private theorem c4629_iso   : LeafIso 4629    := by decide +kernel
private theorem c4629_nof2  : NoF2ChkSq 4629  := by decide +kernel
private theorem c4629_nof3  : NoF3ChkSq 4629  := by decide +kernel
private theorem c4629_nof4z : NoF4zChkSq 4629 := by decide +kernel
theorem C'_4629 : C' 4629 :=
  ⟨c4629_sqf, c4629_range, c4629_ell, leafNSq_of_sq c4629_nsq, leafHAr_of_sq c4629_har,
   c4629_r, c4629_e', c4629_f1, leafS2_of_sq c4629_s2, leafS3_of_sq c4629_s3,
   c4629_iso, leafR8_of_sq c4629_nof2 c4629_nof3 c4629_nof4z⟩
theorem not_tile'_4629 (D : CongruentDissection 4629) : False :=
  not_tile_of_conditions' 4629 C'_4629 D

end Erdos634.Draft.AllN2

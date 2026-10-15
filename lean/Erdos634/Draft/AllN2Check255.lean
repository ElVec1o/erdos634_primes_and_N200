/- AllN2Check255: N = 4607, 4609, 4613, 4614, 4615
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4607_sqf   : LeafSqf 4607   := by decide +kernel
private theorem c4607_range : LeafRange 4607  := by decide +kernel
private theorem c4607_ell   : LeafEll 4607    := by decide +kernel
private theorem c4607_nsq   : NSqChkSq 4607   := by decide +kernel
private theorem c4607_har   : HArithChkSq 4607 := by decide +kernel
private theorem c4607_r     : LeafR 4607      := by decide +kernel
private theorem c4607_e'    : LeafE' 4607     := by decide +kernel
private theorem c4607_f1    : LeafF1 4607     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4607_s2    : S2ChkSq 4607    := by decide +kernel
private theorem c4607_s3    : S3ChkSq 4607    := by decide +kernel
private theorem c4607_iso   : LeafIso 4607    := by decide +kernel
private theorem c4607_nof2  : NoF2ChkSq 4607  := by decide +kernel
private theorem c4607_nof3  : NoF3ChkSq 4607  := by decide +kernel
private theorem c4607_nof4z : NoF4zChkSq 4607 := by decide +kernel
theorem C'_4607 : C' 4607 :=
  ⟨c4607_sqf, c4607_range, c4607_ell, leafNSq_of_sq c4607_nsq, leafHAr_of_sq c4607_har,
   c4607_r, c4607_e', c4607_f1, leafS2_of_sq c4607_s2, leafS3_of_sq c4607_s3,
   c4607_iso, leafR8_of_sq c4607_nof2 c4607_nof3 c4607_nof4z⟩
theorem not_tile'_4607 (D : CongruentDissection 4607) : False :=
  not_tile_of_conditions' 4607 C'_4607 D

private theorem c4609_sqf   : LeafSqf 4609   := by decide +kernel
private theorem c4609_range : LeafRange 4609  := by decide +kernel
private theorem c4609_ell   : LeafEll 4609    := by decide +kernel
private theorem c4609_nsq   : NSqChkSq 4609   := by decide +kernel
private theorem c4609_har   : HArithChkSq 4609 := by decide +kernel
private theorem c4609_r     : LeafR 4609      := by decide +kernel
private theorem c4609_e'    : LeafE' 4609     := by decide +kernel
private theorem c4609_f1    : LeafF1 4609     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4609_s2    : S2ChkSq 4609    := by decide +kernel
private theorem c4609_s3    : S3ChkSq 4609    := by decide +kernel
private theorem c4609_iso   : LeafIso 4609    := by decide +kernel
private theorem c4609_nof2  : NoF2ChkSq 4609  := by decide +kernel
private theorem c4609_nof3  : NoF3ChkSq 4609  := by decide +kernel
private theorem c4609_nof4z : NoF4zChkSq 4609 := by decide +kernel
theorem C'_4609 : C' 4609 :=
  ⟨c4609_sqf, c4609_range, c4609_ell, leafNSq_of_sq c4609_nsq, leafHAr_of_sq c4609_har,
   c4609_r, c4609_e', c4609_f1, leafS2_of_sq c4609_s2, leafS3_of_sq c4609_s3,
   c4609_iso, leafR8_of_sq c4609_nof2 c4609_nof3 c4609_nof4z⟩
theorem not_tile'_4609 (D : CongruentDissection 4609) : False :=
  not_tile_of_conditions' 4609 C'_4609 D

private theorem c4613_sqf   : LeafSqf 4613   := by decide +kernel
private theorem c4613_range : LeafRange 4613  := by decide +kernel
private theorem c4613_ell   : LeafEll 4613    := by decide +kernel
private theorem c4613_nsq   : NSqChkSq 4613   := by decide +kernel
private theorem c4613_har   : HArithChkSq 4613 := by decide +kernel
private theorem c4613_r     : LeafR 4613      := by decide +kernel
private theorem c4613_e'    : LeafE' 4613     := by decide +kernel
private theorem c4613_f1    : LeafF1 4613     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4613_s2    : S2ChkSq 4613    := by decide +kernel
private theorem c4613_s3    : S3ChkSq 4613    := by decide +kernel
private theorem c4613_iso   : LeafIso 4613    := by decide +kernel
private theorem c4613_nof2  : NoF2ChkSq 4613  := by decide +kernel
private theorem c4613_nof3  : NoF3ChkSq 4613  := by decide +kernel
private theorem c4613_nof4z : NoF4zChkSq 4613 := by decide +kernel
theorem C'_4613 : C' 4613 :=
  ⟨c4613_sqf, c4613_range, c4613_ell, leafNSq_of_sq c4613_nsq, leafHAr_of_sq c4613_har,
   c4613_r, c4613_e', c4613_f1, leafS2_of_sq c4613_s2, leafS3_of_sq c4613_s3,
   c4613_iso, leafR8_of_sq c4613_nof2 c4613_nof3 c4613_nof4z⟩
theorem not_tile'_4613 (D : CongruentDissection 4613) : False :=
  not_tile_of_conditions' 4613 C'_4613 D

private theorem c4614_sqf   : LeafSqf 4614   := by decide +kernel
private theorem c4614_range : LeafRange 4614  := by decide +kernel
private theorem c4614_ell   : LeafEll 4614    := by decide +kernel
private theorem c4614_nsq   : NSqChkSq 4614   := by decide +kernel
private theorem c4614_har   : HArithChkSq 4614 := by decide +kernel
private theorem c4614_r     : LeafR 4614      := by decide +kernel
private theorem c4614_e'    : LeafE' 4614     := by decide +kernel
private theorem c4614_f1    : LeafF1 4614     := Or.inl (by decide)
private theorem c4614_s2    : S2ChkSq 4614    := by decide +kernel
private theorem c4614_s3    : S3ChkSq 4614    := by decide +kernel
private theorem c4614_iso   : LeafIso 4614    := by decide +kernel
private theorem c4614_nof2  : NoF2ChkSq 4614  := by decide +kernel
private theorem c4614_nof3  : NoF3ChkSq 4614  := by decide +kernel
private theorem c4614_nof4z : NoF4zChkSq 4614 := by decide +kernel
theorem C'_4614 : C' 4614 :=
  ⟨c4614_sqf, c4614_range, c4614_ell, leafNSq_of_sq c4614_nsq, leafHAr_of_sq c4614_har,
   c4614_r, c4614_e', c4614_f1, leafS2_of_sq c4614_s2, leafS3_of_sq c4614_s3,
   c4614_iso, leafR8_of_sq c4614_nof2 c4614_nof3 c4614_nof4z⟩
theorem not_tile'_4614 (D : CongruentDissection 4614) : False :=
  not_tile_of_conditions' 4614 C'_4614 D

private theorem c4615_sqf   : LeafSqf 4615   := by decide +kernel
private theorem c4615_range : LeafRange 4615  := by decide +kernel
private theorem c4615_ell   : LeafEll 4615    := by decide +kernel
private theorem c4615_nsq   : NSqChkSq 4615   := by decide +kernel
private theorem c4615_har   : HArithChkSq 4615 := by decide +kernel
private theorem c4615_r     : LeafR 4615      := by decide +kernel
private theorem c4615_e'    : LeafE' 4615     := by decide +kernel
private theorem c4615_f1    : LeafF1 4615     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4615_s2    : S2ChkSq 4615    := by decide +kernel
private theorem c4615_s3    : S3ChkSq 4615    := by decide +kernel
private theorem c4615_iso   : LeafIso 4615    := by decide +kernel
private theorem c4615_nof2  : NoF2ChkSq 4615  := by decide +kernel
private theorem c4615_nof3  : NoF3ChkSq 4615  := by decide +kernel
private theorem c4615_nof4z : NoF4zChkSq 4615 := by decide +kernel
theorem C'_4615 : C' 4615 :=
  ⟨c4615_sqf, c4615_range, c4615_ell, leafNSq_of_sq c4615_nsq, leafHAr_of_sq c4615_har,
   c4615_r, c4615_e', c4615_f1, leafS2_of_sq c4615_s2, leafS3_of_sq c4615_s3,
   c4615_iso, leafR8_of_sq c4615_nof2 c4615_nof3 c4615_nof4z⟩
theorem not_tile'_4615 (D : CongruentDissection 4615) : False :=
  not_tile_of_conditions' 4615 C'_4615 D

end Erdos634.Draft.AllN2

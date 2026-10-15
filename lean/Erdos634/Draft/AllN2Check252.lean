/- AllN2Check252: N = 4569, 4571, 4574, 4577, 4578
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4569_sqf   : LeafSqf 4569   := by decide +kernel
private theorem c4569_range : LeafRange 4569  := by decide +kernel
private theorem c4569_ell   : LeafEll 4569    := by decide +kernel
private theorem c4569_nsq   : NSqChkSq 4569   := by decide +kernel
private theorem c4569_har   : HArithChkSq 4569 := by decide +kernel
private theorem c4569_r     : LeafR 4569      := by decide +kernel
private theorem c4569_e'    : LeafE' 4569     := by decide +kernel
private theorem c4569_f1    : LeafF1 4569     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4569_s2    : S2ChkSq 4569    := by decide +kernel
private theorem c4569_s3    : S3ChkSq 4569    := by decide +kernel
private theorem c4569_iso   : LeafIso 4569    := by decide +kernel
private theorem c4569_nof2  : NoF2ChkSq 4569  := by decide +kernel
private theorem c4569_nof3  : NoF3ChkSq 4569  := by decide +kernel
private theorem c4569_nof4z : NoF4zChkSq 4569 := by decide +kernel
theorem C'_4569 : C' 4569 :=
  ⟨c4569_sqf, c4569_range, c4569_ell, leafNSq_of_sq c4569_nsq, leafHAr_of_sq c4569_har,
   c4569_r, c4569_e', c4569_f1, leafS2_of_sq c4569_s2, leafS3_of_sq c4569_s3,
   c4569_iso, leafR8_of_sq c4569_nof2 c4569_nof3 c4569_nof4z⟩
theorem not_tile'_4569 (D : CongruentDissection 4569) : False :=
  not_tile_of_conditions' 4569 C'_4569 D

private theorem c4571_sqf   : LeafSqf 4571   := by decide +kernel
private theorem c4571_range : LeafRange 4571  := by decide +kernel
private theorem c4571_ell   : LeafEll 4571    := by decide +kernel
private theorem c4571_nsq   : NSqChkSq 4571   := by decide +kernel
private theorem c4571_har   : HArithChkSq 4571 := by decide +kernel
private theorem c4571_r     : LeafR 4571      := by decide +kernel
private theorem c4571_e'    : LeafE' 4571     := by decide +kernel
private theorem c4571_f1    : LeafF1 4571     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4571_s2    : S2ChkSq 4571    := by decide +kernel
private theorem c4571_s3    : S3ChkSq 4571    := by decide +kernel
private theorem c4571_iso   : LeafIso 4571    := by decide +kernel
private theorem c4571_nof2  : NoF2ChkSq 4571  := by decide +kernel
private theorem c4571_nof3  : NoF3ChkSq 4571  := by decide +kernel
private theorem c4571_nof4z : NoF4zChkSq 4571 := by decide +kernel
theorem C'_4571 : C' 4571 :=
  ⟨c4571_sqf, c4571_range, c4571_ell, leafNSq_of_sq c4571_nsq, leafHAr_of_sq c4571_har,
   c4571_r, c4571_e', c4571_f1, leafS2_of_sq c4571_s2, leafS3_of_sq c4571_s3,
   c4571_iso, leafR8_of_sq c4571_nof2 c4571_nof3 c4571_nof4z⟩
theorem not_tile'_4571 (D : CongruentDissection 4571) : False :=
  not_tile_of_conditions' 4571 C'_4571 D

private theorem c4574_sqf   : LeafSqf 4574   := by decide +kernel
private theorem c4574_range : LeafRange 4574  := by decide +kernel
private theorem c4574_ell   : LeafEll 4574    := by decide +kernel
private theorem c4574_nsq   : NSqChkSq 4574   := by decide +kernel
private theorem c4574_har   : HArithChkSq 4574 := by decide +kernel
private theorem c4574_r     : LeafR 4574      := by decide +kernel
private theorem c4574_e'    : LeafE' 4574     := by decide +kernel
private theorem c4574_f1    : LeafF1 4574     := Or.inl (by decide)
private theorem c4574_s2    : S2ChkSq 4574    := by decide +kernel
private theorem c4574_s3    : S3ChkSq 4574    := by decide +kernel
private theorem c4574_iso   : LeafIso 4574    := by decide +kernel
private theorem c4574_nof2  : NoF2ChkSq 4574  := by decide +kernel
private theorem c4574_nof3  : NoF3ChkSq 4574  := by decide +kernel
private theorem c4574_nof4z : NoF4zChkSq 4574 := by decide +kernel
theorem C'_4574 : C' 4574 :=
  ⟨c4574_sqf, c4574_range, c4574_ell, leafNSq_of_sq c4574_nsq, leafHAr_of_sq c4574_har,
   c4574_r, c4574_e', c4574_f1, leafS2_of_sq c4574_s2, leafS3_of_sq c4574_s3,
   c4574_iso, leafR8_of_sq c4574_nof2 c4574_nof3 c4574_nof4z⟩
theorem not_tile'_4574 (D : CongruentDissection 4574) : False :=
  not_tile_of_conditions' 4574 C'_4574 D

private theorem c4577_sqf   : LeafSqf 4577   := by decide +kernel
private theorem c4577_range : LeafRange 4577  := by decide +kernel
private theorem c4577_ell   : LeafEll 4577    := by decide +kernel
private theorem c4577_nsq   : NSqChkSq 4577   := by decide +kernel
private theorem c4577_har   : HArithChkSq 4577 := by decide +kernel
private theorem c4577_r     : LeafR 4577      := by decide +kernel
private theorem c4577_e'    : LeafE' 4577     := by decide +kernel
private theorem c4577_f1    : LeafF1 4577     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4577_s2    : S2ChkSq 4577    := by decide +kernel
private theorem c4577_s3    : S3ChkSq 4577    := by decide +kernel
private theorem c4577_iso   : LeafIso 4577    := by decide +kernel
private theorem c4577_nof2  : NoF2ChkSq 4577  := by decide +kernel
private theorem c4577_nof3  : NoF3ChkSq 4577  := by decide +kernel
private theorem c4577_nof4z : NoF4zChkSq 4577 := by decide +kernel
theorem C'_4577 : C' 4577 :=
  ⟨c4577_sqf, c4577_range, c4577_ell, leafNSq_of_sq c4577_nsq, leafHAr_of_sq c4577_har,
   c4577_r, c4577_e', c4577_f1, leafS2_of_sq c4577_s2, leafS3_of_sq c4577_s3,
   c4577_iso, leafR8_of_sq c4577_nof2 c4577_nof3 c4577_nof4z⟩
theorem not_tile'_4577 (D : CongruentDissection 4577) : False :=
  not_tile_of_conditions' 4577 C'_4577 D

private theorem c4578_sqf   : LeafSqf 4578   := by decide +kernel
private theorem c4578_range : LeafRange 4578  := by decide +kernel
private theorem c4578_ell   : LeafEll 4578    := by decide +kernel
private theorem c4578_nsq   : NSqChkSq 4578   := by decide +kernel
private theorem c4578_har   : HArithChkSq 4578 := by decide +kernel
private theorem c4578_r     : LeafR 4578      := by decide +kernel
private theorem c4578_e'    : LeafE' 4578     := by decide +kernel
private theorem c4578_f1    : LeafF1 4578     := Or.inl (by decide)
private theorem c4578_s2    : S2ChkSq 4578    := by decide +kernel
private theorem c4578_s3    : S3ChkSq 4578    := by decide +kernel
private theorem c4578_iso   : LeafIso 4578    := by decide +kernel
private theorem c4578_nof2  : NoF2ChkSq 4578  := by decide +kernel
private theorem c4578_nof3  : NoF3ChkSq 4578  := by decide +kernel
private theorem c4578_nof4z : NoF4zChkSq 4578 := by decide +kernel
theorem C'_4578 : C' 4578 :=
  ⟨c4578_sqf, c4578_range, c4578_ell, leafNSq_of_sq c4578_nsq, leafHAr_of_sq c4578_har,
   c4578_r, c4578_e', c4578_f1, leafS2_of_sq c4578_s2, leafS3_of_sq c4578_s3,
   c4578_iso, leafR8_of_sq c4578_nof2 c4578_nof3 c4578_nof4z⟩
theorem not_tile'_4578 (D : CongruentDissection 4578) : False :=
  not_tile_of_conditions' 4578 C'_4578 D

end Erdos634.Draft.AllN2

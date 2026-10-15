/- AllN2Check292: N = 5053, 5059, 5062, 5071, 5074
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c5053_sqf   : LeafSqf 5053   := by decide +kernel
private theorem c5053_range : LeafRange 5053  := by decide +kernel
private theorem c5053_ell   : LeafEll 5053    := by decide +kernel
private theorem c5053_nsq   : NSqChkSq 5053   := by decide +kernel
private theorem c5053_har   : HArithChkSq 5053 := by decide +kernel
private theorem c5053_r     : LeafR 5053      := by decide +kernel
private theorem c5053_e'    : LeafE' 5053     := by decide +kernel
private theorem c5053_f1    : LeafF1 5053     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c5053_s2    : S2ChkSq 5053    := by decide +kernel
private theorem c5053_s3    : S3ChkSq 5053    := by decide +kernel
private theorem c5053_iso   : LeafIso 5053    := by decide +kernel
private theorem c5053_nof2  : NoF2ChkSq 5053  := by decide +kernel
private theorem c5053_nof3  : NoF3ChkSq 5053  := by decide +kernel
private theorem c5053_nof4z : NoF4zChkSq 5053 := by decide +kernel
theorem C'_5053 : C' 5053 :=
  ⟨c5053_sqf, c5053_range, c5053_ell, leafNSq_of_sq c5053_nsq, leafHAr_of_sq c5053_har,
   c5053_r, c5053_e', c5053_f1, leafS2_of_sq c5053_s2, leafS3_of_sq c5053_s3,
   c5053_iso, leafR8_of_sq c5053_nof2 c5053_nof3 c5053_nof4z⟩
theorem not_tile'_5053 (D : CongruentDissection 5053) : False :=
  not_tile_of_conditions' 5053 C'_5053 D

private theorem c5059_sqf   : LeafSqf 5059   := by decide +kernel
private theorem c5059_range : LeafRange 5059  := by decide +kernel
private theorem c5059_ell   : LeafEll 5059    := by decide +kernel
private theorem c5059_nsq   : NSqChkSq 5059   := by decide +kernel
private theorem c5059_har   : HArithChkSq 5059 := by decide +kernel
private theorem c5059_r     : LeafR 5059      := by decide +kernel
private theorem c5059_e'    : LeafE' 5059     := by decide +kernel
private theorem c5059_f1    : LeafF1 5059     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c5059_s2    : S2ChkSq 5059    := by decide +kernel
private theorem c5059_s3    : S3ChkSq 5059    := by decide +kernel
private theorem c5059_iso   : LeafIso 5059    := by decide +kernel
private theorem c5059_nof2  : NoF2ChkSq 5059  := by decide +kernel
private theorem c5059_nof3  : NoF3ChkSq 5059  := by decide +kernel
private theorem c5059_nof4z : NoF4zChkSq 5059 := by decide +kernel
theorem C'_5059 : C' 5059 :=
  ⟨c5059_sqf, c5059_range, c5059_ell, leafNSq_of_sq c5059_nsq, leafHAr_of_sq c5059_har,
   c5059_r, c5059_e', c5059_f1, leafS2_of_sq c5059_s2, leafS3_of_sq c5059_s3,
   c5059_iso, leafR8_of_sq c5059_nof2 c5059_nof3 c5059_nof4z⟩
theorem not_tile'_5059 (D : CongruentDissection 5059) : False :=
  not_tile_of_conditions' 5059 C'_5059 D

private theorem c5062_sqf   : LeafSqf 5062   := by decide +kernel
private theorem c5062_range : LeafRange 5062  := by decide +kernel
private theorem c5062_ell   : LeafEll 5062    := by decide +kernel
private theorem c5062_nsq   : NSqChkSq 5062   := by decide +kernel
private theorem c5062_har   : HArithChkSq 5062 := by decide +kernel
private theorem c5062_r     : LeafR 5062      := by decide +kernel
private theorem c5062_e'    : LeafE' 5062     := by decide +kernel
private theorem c5062_f1    : LeafF1 5062     := Or.inl (by decide)
private theorem c5062_s2    : S2ChkSq 5062    := by decide +kernel
private theorem c5062_s3    : S3ChkSq 5062    := by decide +kernel
private theorem c5062_iso   : LeafIso 5062    := by decide +kernel
private theorem c5062_nof2  : NoF2ChkSq 5062  := by decide +kernel
private theorem c5062_nof3  : NoF3ChkSq 5062  := by decide +kernel
private theorem c5062_nof4z : NoF4zChkSq 5062 := by decide +kernel
theorem C'_5062 : C' 5062 :=
  ⟨c5062_sqf, c5062_range, c5062_ell, leafNSq_of_sq c5062_nsq, leafHAr_of_sq c5062_har,
   c5062_r, c5062_e', c5062_f1, leafS2_of_sq c5062_s2, leafS3_of_sq c5062_s3,
   c5062_iso, leafR8_of_sq c5062_nof2 c5062_nof3 c5062_nof4z⟩
theorem not_tile'_5062 (D : CongruentDissection 5062) : False :=
  not_tile_of_conditions' 5062 C'_5062 D

private theorem c5071_sqf   : LeafSqf 5071   := by decide +kernel
private theorem c5071_range : LeafRange 5071  := by decide +kernel
private theorem c5071_ell   : LeafEll 5071    := by decide +kernel
private theorem c5071_nsq   : NSqChkSq 5071   := by decide +kernel
private theorem c5071_har   : HArithChkSq 5071 := by decide +kernel
private theorem c5071_r     : LeafR 5071      := by decide +kernel
private theorem c5071_e'    : LeafE' 5071     := by decide +kernel
private theorem c5071_f1    : LeafF1 5071     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c5071_s2    : S2ChkSq 5071    := by decide +kernel
private theorem c5071_s3    : S3ChkSq 5071    := by decide +kernel
private theorem c5071_iso   : LeafIso 5071    := by decide +kernel
private theorem c5071_nof2  : NoF2ChkSq 5071  := by decide +kernel
private theorem c5071_nof3  : NoF3ChkSq 5071  := by decide +kernel
private theorem c5071_nof4z : NoF4zChkSq 5071 := by decide +kernel
theorem C'_5071 : C' 5071 :=
  ⟨c5071_sqf, c5071_range, c5071_ell, leafNSq_of_sq c5071_nsq, leafHAr_of_sq c5071_har,
   c5071_r, c5071_e', c5071_f1, leafS2_of_sq c5071_s2, leafS3_of_sq c5071_s3,
   c5071_iso, leafR8_of_sq c5071_nof2 c5071_nof3 c5071_nof4z⟩
theorem not_tile'_5071 (D : CongruentDissection 5071) : False :=
  not_tile_of_conditions' 5071 C'_5071 D

private theorem c5074_sqf   : LeafSqf 5074   := by decide +kernel
private theorem c5074_range : LeafRange 5074  := by decide +kernel
private theorem c5074_ell   : LeafEll 5074    := by decide +kernel
private theorem c5074_nsq   : NSqChkSq 5074   := by decide +kernel
private theorem c5074_har   : HArithChkSq 5074 := by decide +kernel
private theorem c5074_r     : LeafR 5074      := by decide +kernel
private theorem c5074_e'    : LeafE' 5074     := by decide +kernel
private theorem c5074_f1    : LeafF1 5074     := Or.inl (by decide)
private theorem c5074_s2    : S2ChkSq 5074    := by decide +kernel
private theorem c5074_s3    : S3ChkSq 5074    := by decide +kernel
private theorem c5074_iso   : LeafIso 5074    := by decide +kernel
private theorem c5074_nof2  : NoF2ChkSq 5074  := by decide +kernel
private theorem c5074_nof3  : NoF3ChkSq 5074  := by decide +kernel
private theorem c5074_nof4z : NoF4zChkSq 5074 := by decide +kernel
theorem C'_5074 : C' 5074 :=
  ⟨c5074_sqf, c5074_range, c5074_ell, leafNSq_of_sq c5074_nsq, leafHAr_of_sq c5074_har,
   c5074_r, c5074_e', c5074_f1, leafS2_of_sq c5074_s2, leafS3_of_sq c5074_s3,
   c5074_iso, leafR8_of_sq c5074_nof2 c5074_nof3 c5074_nof4z⟩
theorem not_tile'_5074 (D : CongruentDissection 5074) : False :=
  not_tile_of_conditions' 5074 C'_5074 D

end Erdos634.Draft.AllN2

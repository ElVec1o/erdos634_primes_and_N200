/- AllN2Check212: N = 4070, 4071, 4074, 4078, 4079
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4070_sqf   : LeafSqf 4070   := by decide +kernel
private theorem c4070_range : LeafRange 4070  := by decide +kernel
private theorem c4070_ell   : LeafEll 4070    := by decide +kernel
private theorem c4070_nsq   : NSqChkSq 4070   := by decide +kernel
private theorem c4070_har   : HArithChkSq 4070 := by decide +kernel
private theorem c4070_r     : LeafR 4070      := by decide +kernel
private theorem c4070_e'    : LeafE' 4070     := by decide +kernel
private theorem c4070_f1    : LeafF1 4070     := Or.inl (by decide)
private theorem c4070_s2    : S2ChkSq 4070    := by decide +kernel
private theorem c4070_s3    : S3ChkSq 4070    := by decide +kernel
private theorem c4070_iso   : LeafIso 4070    := by decide +kernel
private theorem c4070_nof2  : NoF2ChkSq 4070  := by decide +kernel
private theorem c4070_nof3  : NoF3ChkSq 4070  := by decide +kernel
private theorem c4070_nof4z : NoF4zChkSq 4070 := by decide +kernel
theorem C'_4070 : C' 4070 :=
  ⟨c4070_sqf, c4070_range, c4070_ell, leafNSq_of_sq c4070_nsq, leafHAr_of_sq c4070_har,
   c4070_r, c4070_e', c4070_f1, leafS2_of_sq c4070_s2, leafS3_of_sq c4070_s3,
   c4070_iso, leafR8_of_sq c4070_nof2 c4070_nof3 c4070_nof4z⟩
theorem not_tile'_4070 (D : CongruentDissection 4070) : False :=
  not_tile_of_conditions' 4070 C'_4070 D

private theorem c4071_sqf   : LeafSqf 4071   := by decide +kernel
private theorem c4071_range : LeafRange 4071  := by decide +kernel
private theorem c4071_ell   : LeafEll 4071    := by decide +kernel
private theorem c4071_nsq   : NSqChkSq 4071   := by decide +kernel
private theorem c4071_har   : HArithChkSq 4071 := by decide +kernel
private theorem c4071_r     : LeafR 4071      := by decide +kernel
private theorem c4071_e'    : LeafE' 4071     := by decide +kernel
private theorem c4071_f1    : LeafF1 4071     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4071_s2    : S2ChkSq 4071    := by decide +kernel
private theorem c4071_s3    : S3ChkSq 4071    := by decide +kernel
private theorem c4071_iso   : LeafIso 4071    := by decide +kernel
private theorem c4071_nof2  : NoF2ChkSq 4071  := by decide +kernel
private theorem c4071_nof3  : NoF3ChkSq 4071  := by decide +kernel
private theorem c4071_nof4z : NoF4zChkSq 4071 := by decide +kernel
theorem C'_4071 : C' 4071 :=
  ⟨c4071_sqf, c4071_range, c4071_ell, leafNSq_of_sq c4071_nsq, leafHAr_of_sq c4071_har,
   c4071_r, c4071_e', c4071_f1, leafS2_of_sq c4071_s2, leafS3_of_sq c4071_s3,
   c4071_iso, leafR8_of_sq c4071_nof2 c4071_nof3 c4071_nof4z⟩
theorem not_tile'_4071 (D : CongruentDissection 4071) : False :=
  not_tile_of_conditions' 4071 C'_4071 D

private theorem c4074_sqf   : LeafSqf 4074   := by decide +kernel
private theorem c4074_range : LeafRange 4074  := by decide +kernel
private theorem c4074_ell   : LeafEll 4074    := by decide +kernel
private theorem c4074_nsq   : NSqChkSq 4074   := by decide +kernel
private theorem c4074_har   : HArithChkSq 4074 := by decide +kernel
private theorem c4074_r     : LeafR 4074      := by decide +kernel
private theorem c4074_e'    : LeafE' 4074     := by decide +kernel
private theorem c4074_f1    : LeafF1 4074     := Or.inl (by decide)
private theorem c4074_s2    : S2ChkSq 4074    := by decide +kernel
private theorem c4074_s3    : S3ChkSq 4074    := by decide +kernel
private theorem c4074_iso   : LeafIso 4074    := by decide +kernel
private theorem c4074_nof2  : NoF2ChkSq 4074  := by decide +kernel
private theorem c4074_nof3  : NoF3ChkSq 4074  := by decide +kernel
private theorem c4074_nof4z : NoF4zChkSq 4074 := by decide +kernel
theorem C'_4074 : C' 4074 :=
  ⟨c4074_sqf, c4074_range, c4074_ell, leafNSq_of_sq c4074_nsq, leafHAr_of_sq c4074_har,
   c4074_r, c4074_e', c4074_f1, leafS2_of_sq c4074_s2, leafS3_of_sq c4074_s3,
   c4074_iso, leafR8_of_sq c4074_nof2 c4074_nof3 c4074_nof4z⟩
theorem not_tile'_4074 (D : CongruentDissection 4074) : False :=
  not_tile_of_conditions' 4074 C'_4074 D

private theorem c4078_sqf   : LeafSqf 4078   := by decide +kernel
private theorem c4078_range : LeafRange 4078  := by decide +kernel
private theorem c4078_ell   : LeafEll 4078    := by decide +kernel
private theorem c4078_nsq   : NSqChkSq 4078   := by decide +kernel
private theorem c4078_har   : HArithChkSq 4078 := by decide +kernel
private theorem c4078_r     : LeafR 4078      := by decide +kernel
private theorem c4078_e'    : LeafE' 4078     := by decide +kernel
private theorem c4078_f1    : LeafF1 4078     := Or.inl (by decide)
private theorem c4078_s2    : S2ChkSq 4078    := by decide +kernel
private theorem c4078_s3    : S3ChkSq 4078    := by decide +kernel
private theorem c4078_iso   : LeafIso 4078    := by decide +kernel
private theorem c4078_nof2  : NoF2ChkSq 4078  := by decide +kernel
private theorem c4078_nof3  : NoF3ChkSq 4078  := by decide +kernel
private theorem c4078_nof4z : NoF4zChkSq 4078 := by decide +kernel
theorem C'_4078 : C' 4078 :=
  ⟨c4078_sqf, c4078_range, c4078_ell, leafNSq_of_sq c4078_nsq, leafHAr_of_sq c4078_har,
   c4078_r, c4078_e', c4078_f1, leafS2_of_sq c4078_s2, leafS3_of_sq c4078_s3,
   c4078_iso, leafR8_of_sq c4078_nof2 c4078_nof3 c4078_nof4z⟩
theorem not_tile'_4078 (D : CongruentDissection 4078) : False :=
  not_tile_of_conditions' 4078 C'_4078 D

private theorem c4079_sqf   : LeafSqf 4079   := by decide +kernel
private theorem c4079_range : LeafRange 4079  := by decide +kernel
private theorem c4079_ell   : LeafEll 4079    := by decide +kernel
private theorem c4079_nsq   : NSqChkSq 4079   := by decide +kernel
private theorem c4079_har   : HArithChkSq 4079 := by decide +kernel
private theorem c4079_r     : LeafR 4079      := by decide +kernel
private theorem c4079_e'    : LeafE' 4079     := by decide +kernel
private theorem c4079_f1    : LeafF1 4079     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4079_s2    : S2ChkSq 4079    := by decide +kernel
private theorem c4079_s3    : S3ChkSq 4079    := by decide +kernel
private theorem c4079_iso   : LeafIso 4079    := by decide +kernel
private theorem c4079_nof2  : NoF2ChkSq 4079  := by decide +kernel
private theorem c4079_nof3  : NoF3ChkSq 4079  := by decide +kernel
private theorem c4079_nof4z : NoF4zChkSq 4079 := by decide +kernel
theorem C'_4079 : C' 4079 :=
  ⟨c4079_sqf, c4079_range, c4079_ell, leafNSq_of_sq c4079_nsq, leafHAr_of_sq c4079_har,
   c4079_r, c4079_e', c4079_f1, leafS2_of_sq c4079_s2, leafS3_of_sq c4079_s3,
   c4079_iso, leafR8_of_sq c4079_nof2 c4079_nof3 c4079_nof4z⟩
theorem not_tile'_4079 (D : CongruentDissection 4079) : False :=
  not_tile_of_conditions' 4079 C'_4079 D

end Erdos634.Draft.AllN2

/- AllN2Check56: N = 2054, 2059, 2062, 2063, 2071
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2054_sqf   : LeafSqf 2054   := by decide +kernel
private theorem c2054_range : LeafRange 2054  := by decide +kernel
private theorem c2054_ell   : LeafEll 2054    := by decide +kernel
private theorem c2054_nsq   : NSqChkSq 2054   := by decide +kernel
private theorem c2054_har   : HArithChkSq 2054 := by decide +kernel
private theorem c2054_r     : LeafR 2054      := by decide +kernel
private theorem c2054_e'    : LeafE' 2054     := by decide +kernel
private theorem c2054_f1    : LeafF1 2054     := Or.inl (by decide)
private theorem c2054_s2    : S2ChkSq 2054    := by decide +kernel
private theorem c2054_s3    : S3ChkSq 2054    := by decide +kernel
private theorem c2054_iso   : LeafIso 2054    := by decide +kernel
private theorem c2054_nof2  : NoF2ChkSq 2054  := by decide +kernel
private theorem c2054_nof3  : NoF3ChkSq 2054  := by decide +kernel
private theorem c2054_nof4z : NoF4zChkSq 2054 := by decide +kernel
theorem C'_2054 : C' 2054 :=
  ⟨c2054_sqf, c2054_range, c2054_ell, leafNSq_of_sq c2054_nsq, leafHAr_of_sq c2054_har,
   c2054_r, c2054_e', c2054_f1, leafS2_of_sq c2054_s2, leafS3_of_sq c2054_s3,
   c2054_iso, leafR8_of_sq c2054_nof2 c2054_nof3 c2054_nof4z⟩
theorem not_tile'_2054 (D : CongruentDissection 2054) : False :=
  not_tile_of_conditions' 2054 C'_2054 D

private theorem c2059_sqf   : LeafSqf 2059   := by decide +kernel
private theorem c2059_range : LeafRange 2059  := by decide +kernel
private theorem c2059_ell   : LeafEll 2059    := by decide +kernel
private theorem c2059_nsq   : NSqChkSq 2059   := by decide +kernel
private theorem c2059_har   : HArithChkSq 2059 := by decide +kernel
private theorem c2059_r     : LeafR 2059      := by decide +kernel
private theorem c2059_e'    : LeafE' 2059     := by decide +kernel
private theorem c2059_f1    : LeafF1 2059     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2059_s2    : S2ChkSq 2059    := by decide +kernel
private theorem c2059_s3    : S3ChkSq 2059    := by decide +kernel
private theorem c2059_iso   : LeafIso 2059    := by decide +kernel
private theorem c2059_nof2  : NoF2ChkSq 2059  := by decide +kernel
private theorem c2059_nof3  : NoF3ChkSq 2059  := by decide +kernel
private theorem c2059_nof4z : NoF4zChkSq 2059 := by decide +kernel
theorem C'_2059 : C' 2059 :=
  ⟨c2059_sqf, c2059_range, c2059_ell, leafNSq_of_sq c2059_nsq, leafHAr_of_sq c2059_har,
   c2059_r, c2059_e', c2059_f1, leafS2_of_sq c2059_s2, leafS3_of_sq c2059_s3,
   c2059_iso, leafR8_of_sq c2059_nof2 c2059_nof3 c2059_nof4z⟩
theorem not_tile'_2059 (D : CongruentDissection 2059) : False :=
  not_tile_of_conditions' 2059 C'_2059 D

private theorem c2062_sqf   : LeafSqf 2062   := by decide +kernel
private theorem c2062_range : LeafRange 2062  := by decide +kernel
private theorem c2062_ell   : LeafEll 2062    := by decide +kernel
private theorem c2062_nsq   : NSqChkSq 2062   := by decide +kernel
private theorem c2062_har   : HArithChkSq 2062 := by decide +kernel
private theorem c2062_r     : LeafR 2062      := by decide +kernel
private theorem c2062_e'    : LeafE' 2062     := by decide +kernel
private theorem c2062_f1    : LeafF1 2062     := Or.inl (by decide)
private theorem c2062_s2    : S2ChkSq 2062    := by decide +kernel
private theorem c2062_s3    : S3ChkSq 2062    := by decide +kernel
private theorem c2062_iso   : LeafIso 2062    := by decide +kernel
private theorem c2062_nof2  : NoF2ChkSq 2062  := by decide +kernel
private theorem c2062_nof3  : NoF3ChkSq 2062  := by decide +kernel
private theorem c2062_nof4z : NoF4zChkSq 2062 := by decide +kernel
theorem C'_2062 : C' 2062 :=
  ⟨c2062_sqf, c2062_range, c2062_ell, leafNSq_of_sq c2062_nsq, leafHAr_of_sq c2062_har,
   c2062_r, c2062_e', c2062_f1, leafS2_of_sq c2062_s2, leafS3_of_sq c2062_s3,
   c2062_iso, leafR8_of_sq c2062_nof2 c2062_nof3 c2062_nof4z⟩
theorem not_tile'_2062 (D : CongruentDissection 2062) : False :=
  not_tile_of_conditions' 2062 C'_2062 D

private theorem c2063_sqf   : LeafSqf 2063   := by decide +kernel
private theorem c2063_range : LeafRange 2063  := by decide +kernel
private theorem c2063_ell   : LeafEll 2063    := by decide +kernel
private theorem c2063_nsq   : NSqChkSq 2063   := by decide +kernel
private theorem c2063_har   : HArithChkSq 2063 := by decide +kernel
private theorem c2063_r     : LeafR 2063      := by decide +kernel
private theorem c2063_e'    : LeafE' 2063     := by decide +kernel
private theorem c2063_f1    : LeafF1 2063     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2063_s2    : S2ChkSq 2063    := by decide +kernel
private theorem c2063_s3    : S3ChkSq 2063    := by decide +kernel
private theorem c2063_iso   : LeafIso 2063    := by decide +kernel
private theorem c2063_nof2  : NoF2ChkSq 2063  := by decide +kernel
private theorem c2063_nof3  : NoF3ChkSq 2063  := by decide +kernel
private theorem c2063_nof4z : NoF4zChkSq 2063 := by decide +kernel
theorem C'_2063 : C' 2063 :=
  ⟨c2063_sqf, c2063_range, c2063_ell, leafNSq_of_sq c2063_nsq, leafHAr_of_sq c2063_har,
   c2063_r, c2063_e', c2063_f1, leafS2_of_sq c2063_s2, leafS3_of_sq c2063_s3,
   c2063_iso, leafR8_of_sq c2063_nof2 c2063_nof3 c2063_nof4z⟩
theorem not_tile'_2063 (D : CongruentDissection 2063) : False :=
  not_tile_of_conditions' 2063 C'_2063 D

private theorem c2071_sqf   : LeafSqf 2071   := by decide +kernel
private theorem c2071_range : LeafRange 2071  := by decide +kernel
private theorem c2071_ell   : LeafEll 2071    := by decide +kernel
private theorem c2071_nsq   : NSqChkSq 2071   := by decide +kernel
private theorem c2071_har   : HArithChkSq 2071 := by decide +kernel
private theorem c2071_r     : LeafR 2071      := by decide +kernel
private theorem c2071_e'    : LeafE' 2071     := by decide +kernel
private theorem c2071_f1    : LeafF1 2071     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2071_s2    : S2ChkSq 2071    := by decide +kernel
private theorem c2071_s3    : S3ChkSq 2071    := by decide +kernel
private theorem c2071_iso   : LeafIso 2071    := by decide +kernel
private theorem c2071_nof2  : NoF2ChkSq 2071  := by decide +kernel
private theorem c2071_nof3  : NoF3ChkSq 2071  := by decide +kernel
private theorem c2071_nof4z : NoF4zChkSq 2071 := by decide +kernel
theorem C'_2071 : C' 2071 :=
  ⟨c2071_sqf, c2071_range, c2071_ell, leafNSq_of_sq c2071_nsq, leafHAr_of_sq c2071_har,
   c2071_r, c2071_e', c2071_f1, leafS2_of_sq c2071_s2, leafS3_of_sq c2071_s3,
   c2071_iso, leafR8_of_sq c2071_nof2 c2071_nof3 c2071_nof4z⟩
theorem not_tile'_2071 (D : CongruentDissection 2071) : False :=
  not_tile_of_conditions' 2071 C'_2071 D

end Erdos634.Draft.AllN2

/- AllN2Check59: N = 2094, 2095, 2099, 2101, 2102
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2094_sqf   : LeafSqf 2094   := by decide +kernel
private theorem c2094_range : LeafRange 2094  := by decide +kernel
private theorem c2094_ell   : LeafEll 2094    := by decide +kernel
private theorem c2094_nsq   : NSqChkSq 2094   := by decide +kernel
private theorem c2094_har   : HArithChkSq 2094 := by decide +kernel
private theorem c2094_r     : LeafR 2094      := by decide +kernel
private theorem c2094_e'    : LeafE' 2094     := by decide +kernel
private theorem c2094_f1    : LeafF1 2094     := Or.inl (by decide)
private theorem c2094_s2    : S2ChkSq 2094    := by decide +kernel
private theorem c2094_s3    : S3ChkSq 2094    := by decide +kernel
private theorem c2094_iso   : LeafIso 2094    := by decide +kernel
private theorem c2094_nof2  : NoF2ChkSq 2094  := by decide +kernel
private theorem c2094_nof3  : NoF3ChkSq 2094  := by decide +kernel
private theorem c2094_nof4z : NoF4zChkSq 2094 := by decide +kernel
theorem C'_2094 : C' 2094 :=
  ⟨c2094_sqf, c2094_range, c2094_ell, leafNSq_of_sq c2094_nsq, leafHAr_of_sq c2094_har,
   c2094_r, c2094_e', c2094_f1, leafS2_of_sq c2094_s2, leafS3_of_sq c2094_s3,
   c2094_iso, leafR8_of_sq c2094_nof2 c2094_nof3 c2094_nof4z⟩
theorem not_tile'_2094 (D : CongruentDissection 2094) : False :=
  not_tile_of_conditions' 2094 C'_2094 D

private theorem c2095_sqf   : LeafSqf 2095   := by decide +kernel
private theorem c2095_range : LeafRange 2095  := by decide +kernel
private theorem c2095_ell   : LeafEll 2095    := by decide +kernel
private theorem c2095_nsq   : NSqChkSq 2095   := by decide +kernel
private theorem c2095_har   : HArithChkSq 2095 := by decide +kernel
private theorem c2095_r     : LeafR 2095      := by decide +kernel
private theorem c2095_e'    : LeafE' 2095     := by decide +kernel
private theorem c2095_f1    : LeafF1 2095     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2095_s2    : S2ChkSq 2095    := by decide +kernel
private theorem c2095_s3    : S3ChkSq 2095    := by decide +kernel
private theorem c2095_iso   : LeafIso 2095    := by decide +kernel
private theorem c2095_nof2  : NoF2ChkSq 2095  := by decide +kernel
private theorem c2095_nof3  : NoF3ChkSq 2095  := by decide +kernel
private theorem c2095_nof4z : NoF4zChkSq 2095 := by decide +kernel
theorem C'_2095 : C' 2095 :=
  ⟨c2095_sqf, c2095_range, c2095_ell, leafNSq_of_sq c2095_nsq, leafHAr_of_sq c2095_har,
   c2095_r, c2095_e', c2095_f1, leafS2_of_sq c2095_s2, leafS3_of_sq c2095_s3,
   c2095_iso, leafR8_of_sq c2095_nof2 c2095_nof3 c2095_nof4z⟩
theorem not_tile'_2095 (D : CongruentDissection 2095) : False :=
  not_tile_of_conditions' 2095 C'_2095 D

private theorem c2099_sqf   : LeafSqf 2099   := by decide +kernel
private theorem c2099_range : LeafRange 2099  := by decide +kernel
private theorem c2099_ell   : LeafEll 2099    := by decide +kernel
private theorem c2099_nsq   : NSqChkSq 2099   := by decide +kernel
private theorem c2099_har   : HArithChkSq 2099 := by decide +kernel
private theorem c2099_r     : LeafR 2099      := by decide +kernel
private theorem c2099_e'    : LeafE' 2099     := by decide +kernel
private theorem c2099_f1    : LeafF1 2099     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2099_s2    : S2ChkSq 2099    := by decide +kernel
private theorem c2099_s3    : S3ChkSq 2099    := by decide +kernel
private theorem c2099_iso   : LeafIso 2099    := by decide +kernel
private theorem c2099_nof2  : NoF2ChkSq 2099  := by decide +kernel
private theorem c2099_nof3  : NoF3ChkSq 2099  := by decide +kernel
private theorem c2099_nof4z : NoF4zChkSq 2099 := by decide +kernel
theorem C'_2099 : C' 2099 :=
  ⟨c2099_sqf, c2099_range, c2099_ell, leafNSq_of_sq c2099_nsq, leafHAr_of_sq c2099_har,
   c2099_r, c2099_e', c2099_f1, leafS2_of_sq c2099_s2, leafS3_of_sq c2099_s3,
   c2099_iso, leafR8_of_sq c2099_nof2 c2099_nof3 c2099_nof4z⟩
theorem not_tile'_2099 (D : CongruentDissection 2099) : False :=
  not_tile_of_conditions' 2099 C'_2099 D

private theorem c2101_sqf   : LeafSqf 2101   := by decide +kernel
private theorem c2101_range : LeafRange 2101  := by decide +kernel
private theorem c2101_ell   : LeafEll 2101    := by decide +kernel
private theorem c2101_nsq   : NSqChkSq 2101   := by decide +kernel
private theorem c2101_har   : HArithChkSq 2101 := by decide +kernel
private theorem c2101_r     : LeafR 2101      := by decide +kernel
private theorem c2101_e'    : LeafE' 2101     := by decide +kernel
private theorem c2101_f1    : LeafF1 2101     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2101_s2    : S2ChkSq 2101    := by decide +kernel
private theorem c2101_s3    : S3ChkSq 2101    := by decide +kernel
private theorem c2101_iso   : LeafIso 2101    := by decide +kernel
private theorem c2101_nof2  : NoF2ChkSq 2101  := by decide +kernel
private theorem c2101_nof3  : NoF3ChkSq 2101  := by decide +kernel
private theorem c2101_nof4z : NoF4zChkSq 2101 := by decide +kernel
theorem C'_2101 : C' 2101 :=
  ⟨c2101_sqf, c2101_range, c2101_ell, leafNSq_of_sq c2101_nsq, leafHAr_of_sq c2101_har,
   c2101_r, c2101_e', c2101_f1, leafS2_of_sq c2101_s2, leafS3_of_sq c2101_s3,
   c2101_iso, leafR8_of_sq c2101_nof2 c2101_nof3 c2101_nof4z⟩
theorem not_tile'_2101 (D : CongruentDissection 2101) : False :=
  not_tile_of_conditions' 2101 C'_2101 D

private theorem c2102_sqf   : LeafSqf 2102   := by decide +kernel
private theorem c2102_range : LeafRange 2102  := by decide +kernel
private theorem c2102_ell   : LeafEll 2102    := by decide +kernel
private theorem c2102_nsq   : NSqChkSq 2102   := by decide +kernel
private theorem c2102_har   : HArithChkSq 2102 := by decide +kernel
private theorem c2102_r     : LeafR 2102      := by decide +kernel
private theorem c2102_e'    : LeafE' 2102     := by decide +kernel
private theorem c2102_f1    : LeafF1 2102     := Or.inl (by decide)
private theorem c2102_s2    : S2ChkSq 2102    := by decide +kernel
private theorem c2102_s3    : S3ChkSq 2102    := by decide +kernel
private theorem c2102_iso   : LeafIso 2102    := by decide +kernel
private theorem c2102_nof2  : NoF2ChkSq 2102  := by decide +kernel
private theorem c2102_nof3  : NoF3ChkSq 2102  := by decide +kernel
private theorem c2102_nof4z : NoF4zChkSq 2102 := by decide +kernel
theorem C'_2102 : C' 2102 :=
  ⟨c2102_sqf, c2102_range, c2102_ell, leafNSq_of_sq c2102_nsq, leafHAr_of_sq c2102_har,
   c2102_r, c2102_e', c2102_f1, leafS2_of_sq c2102_s2, leafS3_of_sq c2102_s3,
   c2102_iso, leafR8_of_sq c2102_nof2 c2102_nof3 c2102_nof4z⟩
theorem not_tile'_2102 (D : CongruentDissection 2102) : False :=
  not_tile_of_conditions' 2102 C'_2102 D

end Erdos634.Draft.AllN2

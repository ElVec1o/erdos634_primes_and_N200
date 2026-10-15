/- AllN2Check138: N = 3095, 3097, 3099, 3101, 3102
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3095_sqf   : LeafSqf 3095   := by decide +kernel
private theorem c3095_range : LeafRange 3095  := by decide +kernel
private theorem c3095_ell   : LeafEll 3095    := by decide +kernel
private theorem c3095_nsq   : NSqChkSq 3095   := by decide +kernel
private theorem c3095_har   : HArithChkSq 3095 := by decide +kernel
private theorem c3095_r     : LeafR 3095      := by decide +kernel
private theorem c3095_e'    : LeafE' 3095     := by decide +kernel
private theorem c3095_f1    : LeafF1 3095     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3095_s2    : S2ChkSq 3095    := by decide +kernel
private theorem c3095_s3    : S3ChkSq 3095    := by decide +kernel
private theorem c3095_iso   : LeafIso 3095    := by decide +kernel
private theorem c3095_nof2  : NoF2ChkSq 3095  := by decide +kernel
private theorem c3095_nof3  : NoF3ChkSq 3095  := by decide +kernel
private theorem c3095_nof4z : NoF4zChkSq 3095 := by decide +kernel
theorem C'_3095 : C' 3095 :=
  ⟨c3095_sqf, c3095_range, c3095_ell, leafNSq_of_sq c3095_nsq, leafHAr_of_sq c3095_har,
   c3095_r, c3095_e', c3095_f1, leafS2_of_sq c3095_s2, leafS3_of_sq c3095_s3,
   c3095_iso, leafR8_of_sq c3095_nof2 c3095_nof3 c3095_nof4z⟩
theorem not_tile'_3095 (D : CongruentDissection 3095) : False :=
  not_tile_of_conditions' 3095 C'_3095 D

private theorem c3097_sqf   : LeafSqf 3097   := by decide +kernel
private theorem c3097_range : LeafRange 3097  := by decide +kernel
private theorem c3097_ell   : LeafEll 3097    := by decide +kernel
private theorem c3097_nsq   : NSqChkSq 3097   := by decide +kernel
private theorem c3097_har   : HArithChkSq 3097 := by decide +kernel
private theorem c3097_r     : LeafR 3097      := by decide +kernel
private theorem c3097_e'    : LeafE' 3097     := by decide +kernel
private theorem c3097_f1    : LeafF1 3097     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3097_s2    : S2ChkSq 3097    := by decide +kernel
private theorem c3097_s3    : S3ChkSq 3097    := by decide +kernel
private theorem c3097_iso   : LeafIso 3097    := by decide +kernel
private theorem c3097_nof2  : NoF2ChkSq 3097  := by decide +kernel
private theorem c3097_nof3  : NoF3ChkSq 3097  := by decide +kernel
private theorem c3097_nof4z : NoF4zChkSq 3097 := by decide +kernel
theorem C'_3097 : C' 3097 :=
  ⟨c3097_sqf, c3097_range, c3097_ell, leafNSq_of_sq c3097_nsq, leafHAr_of_sq c3097_har,
   c3097_r, c3097_e', c3097_f1, leafS2_of_sq c3097_s2, leafS3_of_sq c3097_s3,
   c3097_iso, leafR8_of_sq c3097_nof2 c3097_nof3 c3097_nof4z⟩
theorem not_tile'_3097 (D : CongruentDissection 3097) : False :=
  not_tile_of_conditions' 3097 C'_3097 D

private theorem c3099_sqf   : LeafSqf 3099   := by decide +kernel
private theorem c3099_range : LeafRange 3099  := by decide +kernel
private theorem c3099_ell   : LeafEll 3099    := by decide +kernel
private theorem c3099_nsq   : NSqChkSq 3099   := by decide +kernel
private theorem c3099_har   : HArithChkSq 3099 := by decide +kernel
private theorem c3099_r     : LeafR 3099      := by decide +kernel
private theorem c3099_e'    : LeafE' 3099     := by decide +kernel
private theorem c3099_f1    : LeafF1 3099     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3099_s2    : S2ChkSq 3099    := by decide +kernel
private theorem c3099_s3    : S3ChkSq 3099    := by decide +kernel
private theorem c3099_iso   : LeafIso 3099    := by decide +kernel
private theorem c3099_nof2  : NoF2ChkSq 3099  := by decide +kernel
private theorem c3099_nof3  : NoF3ChkSq 3099  := by decide +kernel
private theorem c3099_nof4z : NoF4zChkSq 3099 := by decide +kernel
theorem C'_3099 : C' 3099 :=
  ⟨c3099_sqf, c3099_range, c3099_ell, leafNSq_of_sq c3099_nsq, leafHAr_of_sq c3099_har,
   c3099_r, c3099_e', c3099_f1, leafS2_of_sq c3099_s2, leafS3_of_sq c3099_s3,
   c3099_iso, leafR8_of_sq c3099_nof2 c3099_nof3 c3099_nof4z⟩
theorem not_tile'_3099 (D : CongruentDissection 3099) : False :=
  not_tile_of_conditions' 3099 C'_3099 D

private theorem c3101_sqf   : LeafSqf 3101   := by decide +kernel
private theorem c3101_range : LeafRange 3101  := by decide +kernel
private theorem c3101_ell   : LeafEll 3101    := by decide +kernel
private theorem c3101_nsq   : NSqChkSq 3101   := by decide +kernel
private theorem c3101_har   : HArithChkSq 3101 := by decide +kernel
private theorem c3101_r     : LeafR 3101      := by decide +kernel
private theorem c3101_e'    : LeafE' 3101     := by decide +kernel
private theorem c3101_f1    : LeafF1 3101     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3101_s2    : S2ChkSq 3101    := by decide +kernel
private theorem c3101_s3    : S3ChkSq 3101    := by decide +kernel
private theorem c3101_iso   : LeafIso 3101    := by decide +kernel
private theorem c3101_nof2  : NoF2ChkSq 3101  := by decide +kernel
private theorem c3101_nof3  : NoF3ChkSq 3101  := by decide +kernel
private theorem c3101_nof4z : NoF4zChkSq 3101 := by decide +kernel
theorem C'_3101 : C' 3101 :=
  ⟨c3101_sqf, c3101_range, c3101_ell, leafNSq_of_sq c3101_nsq, leafHAr_of_sq c3101_har,
   c3101_r, c3101_e', c3101_f1, leafS2_of_sq c3101_s2, leafS3_of_sq c3101_s3,
   c3101_iso, leafR8_of_sq c3101_nof2 c3101_nof3 c3101_nof4z⟩
theorem not_tile'_3101 (D : CongruentDissection 3101) : False :=
  not_tile_of_conditions' 3101 C'_3101 D

private theorem c3102_sqf   : LeafSqf 3102   := by decide +kernel
private theorem c3102_range : LeafRange 3102  := by decide +kernel
private theorem c3102_ell   : LeafEll 3102    := by decide +kernel
private theorem c3102_nsq   : NSqChkSq 3102   := by decide +kernel
private theorem c3102_har   : HArithChkSq 3102 := by decide +kernel
private theorem c3102_r     : LeafR 3102      := by decide +kernel
private theorem c3102_e'    : LeafE' 3102     := by decide +kernel
private theorem c3102_f1    : LeafF1 3102     := Or.inl (by decide)
private theorem c3102_s2    : S2ChkSq 3102    := by decide +kernel
private theorem c3102_s3    : S3ChkSq 3102    := by decide +kernel
private theorem c3102_iso   : LeafIso 3102    := by decide +kernel
private theorem c3102_nof2  : NoF2ChkSq 3102  := by decide +kernel
private theorem c3102_nof3  : NoF3ChkSq 3102  := by decide +kernel
private theorem c3102_nof4z : NoF4zChkSq 3102 := by decide +kernel
theorem C'_3102 : C' 3102 :=
  ⟨c3102_sqf, c3102_range, c3102_ell, leafNSq_of_sq c3102_nsq, leafHAr_of_sq c3102_har,
   c3102_r, c3102_e', c3102_f1, leafS2_of_sq c3102_s2, leafS3_of_sq c3102_s3,
   c3102_iso, leafR8_of_sq c3102_nof2 c3102_nof3 c3102_nof4z⟩
theorem not_tile'_3102 (D : CongruentDissection 3102) : False :=
  not_tile_of_conditions' 3102 C'_3102 D

end Erdos634.Draft.AllN2

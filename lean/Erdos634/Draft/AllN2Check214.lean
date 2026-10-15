/- AllN2Check214: N = 4094, 4098, 4099, 4101, 4102
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4094_sqf   : LeafSqf 4094   := by decide +kernel
private theorem c4094_range : LeafRange 4094  := by decide +kernel
private theorem c4094_ell   : LeafEll 4094    := by decide +kernel
private theorem c4094_nsq   : NSqChkSq 4094   := by decide +kernel
private theorem c4094_har   : HArithChkSq 4094 := by decide +kernel
private theorem c4094_r     : LeafR 4094      := by decide +kernel
private theorem c4094_e'    : LeafE' 4094     := by decide +kernel
private theorem c4094_f1    : LeafF1 4094     := Or.inl (by decide)
private theorem c4094_s2    : S2ChkSq 4094    := by decide +kernel
private theorem c4094_s3    : S3ChkSq 4094    := by decide +kernel
private theorem c4094_iso   : LeafIso 4094    := by decide +kernel
private theorem c4094_nof2  : NoF2ChkSq 4094  := by decide +kernel
private theorem c4094_nof3  : NoF3ChkSq 4094  := by decide +kernel
private theorem c4094_nof4z : NoF4zChkSq 4094 := by decide +kernel
theorem C'_4094 : C' 4094 :=
  ⟨c4094_sqf, c4094_range, c4094_ell, leafNSq_of_sq c4094_nsq, leafHAr_of_sq c4094_har,
   c4094_r, c4094_e', c4094_f1, leafS2_of_sq c4094_s2, leafS3_of_sq c4094_s3,
   c4094_iso, leafR8_of_sq c4094_nof2 c4094_nof3 c4094_nof4z⟩
theorem not_tile'_4094 (D : CongruentDissection 4094) : False :=
  not_tile_of_conditions' 4094 C'_4094 D

private theorem c4098_sqf   : LeafSqf 4098   := by decide +kernel
private theorem c4098_range : LeafRange 4098  := by decide +kernel
private theorem c4098_ell   : LeafEll 4098    := by decide +kernel
private theorem c4098_nsq   : NSqChkSq 4098   := by decide +kernel
private theorem c4098_har   : HArithChkSq 4098 := by decide +kernel
private theorem c4098_r     : LeafR 4098      := by decide +kernel
private theorem c4098_e'    : LeafE' 4098     := by decide +kernel
private theorem c4098_f1    : LeafF1 4098     := Or.inl (by decide)
private theorem c4098_s2    : S2ChkSq 4098    := by decide +kernel
private theorem c4098_s3    : S3ChkSq 4098    := by decide +kernel
private theorem c4098_iso   : LeafIso 4098    := by decide +kernel
private theorem c4098_nof2  : NoF2ChkSq 4098  := by decide +kernel
private theorem c4098_nof3  : NoF3ChkSq 4098  := by decide +kernel
private theorem c4098_nof4z : NoF4zChkSq 4098 := by decide +kernel
theorem C'_4098 : C' 4098 :=
  ⟨c4098_sqf, c4098_range, c4098_ell, leafNSq_of_sq c4098_nsq, leafHAr_of_sq c4098_har,
   c4098_r, c4098_e', c4098_f1, leafS2_of_sq c4098_s2, leafS3_of_sq c4098_s3,
   c4098_iso, leafR8_of_sq c4098_nof2 c4098_nof3 c4098_nof4z⟩
theorem not_tile'_4098 (D : CongruentDissection 4098) : False :=
  not_tile_of_conditions' 4098 C'_4098 D

private theorem c4099_sqf   : LeafSqf 4099   := by decide +kernel
private theorem c4099_range : LeafRange 4099  := by decide +kernel
private theorem c4099_ell   : LeafEll 4099    := by decide +kernel
private theorem c4099_nsq   : NSqChkSq 4099   := by decide +kernel
private theorem c4099_har   : HArithChkSq 4099 := by decide +kernel
private theorem c4099_r     : LeafR 4099      := by decide +kernel
private theorem c4099_e'    : LeafE' 4099     := by decide +kernel
private theorem c4099_f1    : LeafF1 4099     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4099_s2    : S2ChkSq 4099    := by decide +kernel
private theorem c4099_s3    : S3ChkSq 4099    := by decide +kernel
private theorem c4099_iso   : LeafIso 4099    := by decide +kernel
private theorem c4099_nof2  : NoF2ChkSq 4099  := by decide +kernel
private theorem c4099_nof3  : NoF3ChkSq 4099  := by decide +kernel
private theorem c4099_nof4z : NoF4zChkSq 4099 := by decide +kernel
theorem C'_4099 : C' 4099 :=
  ⟨c4099_sqf, c4099_range, c4099_ell, leafNSq_of_sq c4099_nsq, leafHAr_of_sq c4099_har,
   c4099_r, c4099_e', c4099_f1, leafS2_of_sq c4099_s2, leafS3_of_sq c4099_s3,
   c4099_iso, leafR8_of_sq c4099_nof2 c4099_nof3 c4099_nof4z⟩
theorem not_tile'_4099 (D : CongruentDissection 4099) : False :=
  not_tile_of_conditions' 4099 C'_4099 D

private theorem c4101_sqf   : LeafSqf 4101   := by decide +kernel
private theorem c4101_range : LeafRange 4101  := by decide +kernel
private theorem c4101_ell   : LeafEll 4101    := by decide +kernel
private theorem c4101_nsq   : NSqChkSq 4101   := by decide +kernel
private theorem c4101_har   : HArithChkSq 4101 := by decide +kernel
private theorem c4101_r     : LeafR 4101      := by decide +kernel
private theorem c4101_e'    : LeafE' 4101     := by decide +kernel
private theorem c4101_f1    : LeafF1 4101     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4101_s2    : S2ChkSq 4101    := by decide +kernel
private theorem c4101_s3    : S3ChkSq 4101    := by decide +kernel
private theorem c4101_iso   : LeafIso 4101    := by decide +kernel
private theorem c4101_nof2  : NoF2ChkSq 4101  := by decide +kernel
private theorem c4101_nof3  : NoF3ChkSq 4101  := by decide +kernel
private theorem c4101_nof4z : NoF4zChkSq 4101 := by decide +kernel
theorem C'_4101 : C' 4101 :=
  ⟨c4101_sqf, c4101_range, c4101_ell, leafNSq_of_sq c4101_nsq, leafHAr_of_sq c4101_har,
   c4101_r, c4101_e', c4101_f1, leafS2_of_sq c4101_s2, leafS3_of_sq c4101_s3,
   c4101_iso, leafR8_of_sq c4101_nof2 c4101_nof3 c4101_nof4z⟩
theorem not_tile'_4101 (D : CongruentDissection 4101) : False :=
  not_tile_of_conditions' 4101 C'_4101 D

private theorem c4102_sqf   : LeafSqf 4102   := by decide +kernel
private theorem c4102_range : LeafRange 4102  := by decide +kernel
private theorem c4102_ell   : LeafEll 4102    := by decide +kernel
private theorem c4102_nsq   : NSqChkSq 4102   := by decide +kernel
private theorem c4102_har   : HArithChkSq 4102 := by decide +kernel
private theorem c4102_r     : LeafR 4102      := by decide +kernel
private theorem c4102_e'    : LeafE' 4102     := by decide +kernel
private theorem c4102_f1    : LeafF1 4102     := Or.inl (by decide)
private theorem c4102_s2    : S2ChkSq 4102    := by decide +kernel
private theorem c4102_s3    : S3ChkSq 4102    := by decide +kernel
private theorem c4102_iso   : LeafIso 4102    := by decide +kernel
private theorem c4102_nof2  : NoF2ChkSq 4102  := by decide +kernel
private theorem c4102_nof3  : NoF3ChkSq 4102  := by decide +kernel
private theorem c4102_nof4z : NoF4zChkSq 4102 := by decide +kernel
theorem C'_4102 : C' 4102 :=
  ⟨c4102_sqf, c4102_range, c4102_ell, leafNSq_of_sq c4102_nsq, leafHAr_of_sq c4102_har,
   c4102_r, c4102_e', c4102_f1, leafS2_of_sq c4102_s2, leafS3_of_sq c4102_s3,
   c4102_iso, leafR8_of_sq c4102_nof2 c4102_nof3 c4102_nof4z⟩
theorem not_tile'_4102 (D : CongruentDissection 4102) : False :=
  not_tile_of_conditions' 4102 C'_4102 D

end Erdos634.Draft.AllN2

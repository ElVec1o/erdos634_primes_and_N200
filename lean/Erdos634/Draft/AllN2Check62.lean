/- AllN2Check62: N = 2131, 2134, 2135, 2143, 2147
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2131_sqf   : LeafSqf 2131   := by decide +kernel
private theorem c2131_range : LeafRange 2131  := by decide +kernel
private theorem c2131_ell   : LeafEll 2131    := by decide +kernel
private theorem c2131_nsq   : NSqChkSq 2131   := by decide +kernel
private theorem c2131_har   : HArithChkSq 2131 := by decide +kernel
private theorem c2131_r     : LeafR 2131      := by decide +kernel
private theorem c2131_e'    : LeafE' 2131     := by decide +kernel
private theorem c2131_f1    : LeafF1 2131     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2131_s2    : S2ChkSq 2131    := by decide +kernel
private theorem c2131_s3    : S3ChkSq 2131    := by decide +kernel
private theorem c2131_iso   : LeafIso 2131    := by decide +kernel
private theorem c2131_nof2  : NoF2ChkSq 2131  := by decide +kernel
private theorem c2131_nof3  : NoF3ChkSq 2131  := by decide +kernel
private theorem c2131_nof4z : NoF4zChkSq 2131 := by decide +kernel
theorem C'_2131 : C' 2131 :=
  ⟨c2131_sqf, c2131_range, c2131_ell, leafNSq_of_sq c2131_nsq, leafHAr_of_sq c2131_har,
   c2131_r, c2131_e', c2131_f1, leafS2_of_sq c2131_s2, leafS3_of_sq c2131_s3,
   c2131_iso, leafR8_of_sq c2131_nof2 c2131_nof3 c2131_nof4z⟩
theorem not_tile'_2131 (D : CongruentDissection 2131) : False :=
  not_tile_of_conditions' 2131 C'_2131 D

private theorem c2134_sqf   : LeafSqf 2134   := by decide +kernel
private theorem c2134_range : LeafRange 2134  := by decide +kernel
private theorem c2134_ell   : LeafEll 2134    := by decide +kernel
private theorem c2134_nsq   : NSqChkSq 2134   := by decide +kernel
private theorem c2134_har   : HArithChkSq 2134 := by decide +kernel
private theorem c2134_r     : LeafR 2134      := by decide +kernel
private theorem c2134_e'    : LeafE' 2134     := by decide +kernel
private theorem c2134_f1    : LeafF1 2134     := Or.inl (by decide)
private theorem c2134_s2    : S2ChkSq 2134    := by decide +kernel
private theorem c2134_s3    : S3ChkSq 2134    := by decide +kernel
private theorem c2134_iso   : LeafIso 2134    := by decide +kernel
private theorem c2134_nof2  : NoF2ChkSq 2134  := by decide +kernel
private theorem c2134_nof3  : NoF3ChkSq 2134  := by decide +kernel
private theorem c2134_nof4z : NoF4zChkSq 2134 := by decide +kernel
theorem C'_2134 : C' 2134 :=
  ⟨c2134_sqf, c2134_range, c2134_ell, leafNSq_of_sq c2134_nsq, leafHAr_of_sq c2134_har,
   c2134_r, c2134_e', c2134_f1, leafS2_of_sq c2134_s2, leafS3_of_sq c2134_s3,
   c2134_iso, leafR8_of_sq c2134_nof2 c2134_nof3 c2134_nof4z⟩
theorem not_tile'_2134 (D : CongruentDissection 2134) : False :=
  not_tile_of_conditions' 2134 C'_2134 D

private theorem c2135_sqf   : LeafSqf 2135   := by decide +kernel
private theorem c2135_range : LeafRange 2135  := by decide +kernel
private theorem c2135_ell   : LeafEll 2135    := by decide +kernel
private theorem c2135_nsq   : NSqChkSq 2135   := by decide +kernel
private theorem c2135_har   : HArithChkSq 2135 := by decide +kernel
private theorem c2135_r     : LeafR 2135      := by decide +kernel
private theorem c2135_e'    : LeafE' 2135     := by decide +kernel
private theorem c2135_f1    : LeafF1 2135     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2135_s2    : S2ChkSq 2135    := by decide +kernel
private theorem c2135_s3    : S3ChkSq 2135    := by decide +kernel
private theorem c2135_iso   : LeafIso 2135    := by decide +kernel
private theorem c2135_nof2  : NoF2ChkSq 2135  := by decide +kernel
private theorem c2135_nof3  : NoF3ChkSq 2135  := by decide +kernel
private theorem c2135_nof4z : NoF4zChkSq 2135 := by decide +kernel
theorem C'_2135 : C' 2135 :=
  ⟨c2135_sqf, c2135_range, c2135_ell, leafNSq_of_sq c2135_nsq, leafHAr_of_sq c2135_har,
   c2135_r, c2135_e', c2135_f1, leafS2_of_sq c2135_s2, leafS3_of_sq c2135_s3,
   c2135_iso, leafR8_of_sq c2135_nof2 c2135_nof3 c2135_nof4z⟩
theorem not_tile'_2135 (D : CongruentDissection 2135) : False :=
  not_tile_of_conditions' 2135 C'_2135 D

private theorem c2143_sqf   : LeafSqf 2143   := by decide +kernel
private theorem c2143_range : LeafRange 2143  := by decide +kernel
private theorem c2143_ell   : LeafEll 2143    := by decide +kernel
private theorem c2143_nsq   : NSqChkSq 2143   := by decide +kernel
private theorem c2143_har   : HArithChkSq 2143 := by decide +kernel
private theorem c2143_r     : LeafR 2143      := by decide +kernel
private theorem c2143_e'    : LeafE' 2143     := by decide +kernel
private theorem c2143_f1    : LeafF1 2143     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2143_s2    : S2ChkSq 2143    := by decide +kernel
private theorem c2143_s3    : S3ChkSq 2143    := by decide +kernel
private theorem c2143_iso   : LeafIso 2143    := by decide +kernel
private theorem c2143_nof2  : NoF2ChkSq 2143  := by decide +kernel
private theorem c2143_nof3  : NoF3ChkSq 2143  := by decide +kernel
private theorem c2143_nof4z : NoF4zChkSq 2143 := by decide +kernel
theorem C'_2143 : C' 2143 :=
  ⟨c2143_sqf, c2143_range, c2143_ell, leafNSq_of_sq c2143_nsq, leafHAr_of_sq c2143_har,
   c2143_r, c2143_e', c2143_f1, leafS2_of_sq c2143_s2, leafS3_of_sq c2143_s3,
   c2143_iso, leafR8_of_sq c2143_nof2 c2143_nof3 c2143_nof4z⟩
theorem not_tile'_2143 (D : CongruentDissection 2143) : False :=
  not_tile_of_conditions' 2143 C'_2143 D

private theorem c2147_sqf   : LeafSqf 2147   := by decide +kernel
private theorem c2147_range : LeafRange 2147  := by decide +kernel
private theorem c2147_ell   : LeafEll 2147    := by decide +kernel
private theorem c2147_nsq   : NSqChkSq 2147   := by decide +kernel
private theorem c2147_har   : HArithChkSq 2147 := by decide +kernel
private theorem c2147_r     : LeafR 2147      := by decide +kernel
private theorem c2147_e'    : LeafE' 2147     := by decide +kernel
private theorem c2147_f1    : LeafF1 2147     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2147_s2    : S2ChkSq 2147    := by decide +kernel
private theorem c2147_s3    : S3ChkSq 2147    := by decide +kernel
private theorem c2147_iso   : LeafIso 2147    := by decide +kernel
private theorem c2147_nof2  : NoF2ChkSq 2147  := by decide +kernel
private theorem c2147_nof3  : NoF3ChkSq 2147  := by decide +kernel
private theorem c2147_nof4z : NoF4zChkSq 2147 := by decide +kernel
theorem C'_2147 : C' 2147 :=
  ⟨c2147_sqf, c2147_range, c2147_ell, leafNSq_of_sq c2147_nsq, leafHAr_of_sq c2147_har,
   c2147_r, c2147_e', c2147_f1, leafS2_of_sq c2147_s2, leafS3_of_sq c2147_s3,
   c2147_iso, leafR8_of_sq c2147_nof2 c2147_nof3 c2147_nof4z⟩
theorem not_tile'_2147 (D : CongruentDissection 2147) : False :=
  not_tile_of_conditions' 2147 C'_2147 D

end Erdos634.Draft.AllN2

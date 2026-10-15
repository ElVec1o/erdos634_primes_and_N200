/- AllN2Check58: N = 2086, 2087, 2090, 2091, 2093
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2086_sqf   : LeafSqf 2086   := by decide +kernel
private theorem c2086_range : LeafRange 2086  := by decide +kernel
private theorem c2086_ell   : LeafEll 2086    := by decide +kernel
private theorem c2086_nsq   : NSqChkSq 2086   := by decide +kernel
private theorem c2086_har   : HArithChkSq 2086 := by decide +kernel
private theorem c2086_r     : LeafR 2086      := by decide +kernel
private theorem c2086_e'    : LeafE' 2086     := by decide +kernel
private theorem c2086_f1    : LeafF1 2086     := Or.inl (by decide)
private theorem c2086_s2    : S2ChkSq 2086    := by decide +kernel
private theorem c2086_s3    : S3ChkSq 2086    := by decide +kernel
private theorem c2086_iso   : LeafIso 2086    := by decide +kernel
private theorem c2086_nof2  : NoF2ChkSq 2086  := by decide +kernel
private theorem c2086_nof3  : NoF3ChkSq 2086  := by decide +kernel
private theorem c2086_nof4z : NoF4zChkSq 2086 := by decide +kernel
theorem C'_2086 : C' 2086 :=
  ⟨c2086_sqf, c2086_range, c2086_ell, leafNSq_of_sq c2086_nsq, leafHAr_of_sq c2086_har,
   c2086_r, c2086_e', c2086_f1, leafS2_of_sq c2086_s2, leafS3_of_sq c2086_s3,
   c2086_iso, leafR8_of_sq c2086_nof2 c2086_nof3 c2086_nof4z⟩
theorem not_tile'_2086 (D : CongruentDissection 2086) : False :=
  not_tile_of_conditions' 2086 C'_2086 D

private theorem c2087_sqf   : LeafSqf 2087   := by decide +kernel
private theorem c2087_range : LeafRange 2087  := by decide +kernel
private theorem c2087_ell   : LeafEll 2087    := by decide +kernel
private theorem c2087_nsq   : NSqChkSq 2087   := by decide +kernel
private theorem c2087_har   : HArithChkSq 2087 := by decide +kernel
private theorem c2087_r     : LeafR 2087      := by decide +kernel
private theorem c2087_e'    : LeafE' 2087     := by decide +kernel
private theorem c2087_f1    : LeafF1 2087     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2087_s2    : S2ChkSq 2087    := by decide +kernel
private theorem c2087_s3    : S3ChkSq 2087    := by decide +kernel
private theorem c2087_iso   : LeafIso 2087    := by decide +kernel
private theorem c2087_nof2  : NoF2ChkSq 2087  := by decide +kernel
private theorem c2087_nof3  : NoF3ChkSq 2087  := by decide +kernel
private theorem c2087_nof4z : NoF4zChkSq 2087 := by decide +kernel
theorem C'_2087 : C' 2087 :=
  ⟨c2087_sqf, c2087_range, c2087_ell, leafNSq_of_sq c2087_nsq, leafHAr_of_sq c2087_har,
   c2087_r, c2087_e', c2087_f1, leafS2_of_sq c2087_s2, leafS3_of_sq c2087_s3,
   c2087_iso, leafR8_of_sq c2087_nof2 c2087_nof3 c2087_nof4z⟩
theorem not_tile'_2087 (D : CongruentDissection 2087) : False :=
  not_tile_of_conditions' 2087 C'_2087 D

private theorem c2090_sqf   : LeafSqf 2090   := by decide +kernel
private theorem c2090_range : LeafRange 2090  := by decide +kernel
private theorem c2090_ell   : LeafEll 2090    := by decide +kernel
private theorem c2090_nsq   : NSqChkSq 2090   := by decide +kernel
private theorem c2090_har   : HArithChkSq 2090 := by decide +kernel
private theorem c2090_r     : LeafR 2090      := by decide +kernel
private theorem c2090_e'    : LeafE' 2090     := by decide +kernel
private theorem c2090_f1    : LeafF1 2090     := Or.inl (by decide)
private theorem c2090_s2    : S2ChkSq 2090    := by decide +kernel
private theorem c2090_s3    : S3ChkSq 2090    := by decide +kernel
private theorem c2090_iso   : LeafIso 2090    := by decide +kernel
private theorem c2090_nof2  : NoF2ChkSq 2090  := by decide +kernel
private theorem c2090_nof3  : NoF3ChkSq 2090  := by decide +kernel
private theorem c2090_nof4z : NoF4zChkSq 2090 := by decide +kernel
theorem C'_2090 : C' 2090 :=
  ⟨c2090_sqf, c2090_range, c2090_ell, leafNSq_of_sq c2090_nsq, leafHAr_of_sq c2090_har,
   c2090_r, c2090_e', c2090_f1, leafS2_of_sq c2090_s2, leafS3_of_sq c2090_s3,
   c2090_iso, leafR8_of_sq c2090_nof2 c2090_nof3 c2090_nof4z⟩
theorem not_tile'_2090 (D : CongruentDissection 2090) : False :=
  not_tile_of_conditions' 2090 C'_2090 D

private theorem c2091_sqf   : LeafSqf 2091   := by decide +kernel
private theorem c2091_range : LeafRange 2091  := by decide +kernel
private theorem c2091_ell   : LeafEll 2091    := by decide +kernel
private theorem c2091_nsq   : NSqChkSq 2091   := by decide +kernel
private theorem c2091_har   : HArithChkSq 2091 := by decide +kernel
private theorem c2091_r     : LeafR 2091      := by decide +kernel
private theorem c2091_e'    : LeafE' 2091     := by decide +kernel
private theorem c2091_f1    : LeafF1 2091     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2091_s2    : S2ChkSq 2091    := by decide +kernel
private theorem c2091_s3    : S3ChkSq 2091    := by decide +kernel
private theorem c2091_iso   : LeafIso 2091    := by decide +kernel
private theorem c2091_nof2  : NoF2ChkSq 2091  := by decide +kernel
private theorem c2091_nof3  : NoF3ChkSq 2091  := by decide +kernel
private theorem c2091_nof4z : NoF4zChkSq 2091 := by decide +kernel
theorem C'_2091 : C' 2091 :=
  ⟨c2091_sqf, c2091_range, c2091_ell, leafNSq_of_sq c2091_nsq, leafHAr_of_sq c2091_har,
   c2091_r, c2091_e', c2091_f1, leafS2_of_sq c2091_s2, leafS3_of_sq c2091_s3,
   c2091_iso, leafR8_of_sq c2091_nof2 c2091_nof3 c2091_nof4z⟩
theorem not_tile'_2091 (D : CongruentDissection 2091) : False :=
  not_tile_of_conditions' 2091 C'_2091 D

private theorem c2093_sqf   : LeafSqf 2093   := by decide +kernel
private theorem c2093_range : LeafRange 2093  := by decide +kernel
private theorem c2093_ell   : LeafEll 2093    := by decide +kernel
private theorem c2093_nsq   : NSqChkSq 2093   := by decide +kernel
private theorem c2093_har   : HArithChkSq 2093 := by decide +kernel
private theorem c2093_r     : LeafR 2093      := by decide +kernel
private theorem c2093_e'    : LeafE' 2093     := by decide +kernel
private theorem c2093_f1    : LeafF1 2093     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2093_s2    : S2ChkSq 2093    := by decide +kernel
private theorem c2093_s3    : S3ChkSq 2093    := by decide +kernel
private theorem c2093_iso   : LeafIso 2093    := by decide +kernel
private theorem c2093_nof2  : NoF2ChkSq 2093  := by decide +kernel
private theorem c2093_nof3  : NoF3ChkSq 2093  := by decide +kernel
private theorem c2093_nof4z : NoF4zChkSq 2093 := by decide +kernel
theorem C'_2093 : C' 2093 :=
  ⟨c2093_sqf, c2093_range, c2093_ell, leafNSq_of_sq c2093_nsq, leafHAr_of_sq c2093_har,
   c2093_r, c2093_e', c2093_f1, leafS2_of_sq c2093_s2, leafS3_of_sq c2093_s3,
   c2093_iso, leafR8_of_sq c2093_nof2 c2093_nof3 c2093_nof4z⟩
theorem not_tile'_2093 (D : CongruentDissection 2093) : False :=
  not_tile_of_conditions' 2093 C'_2093 D

end Erdos634.Draft.AllN2

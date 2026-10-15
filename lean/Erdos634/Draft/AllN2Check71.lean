/- AllN2Check71: N = 2243, 2246, 2251, 2253, 2255
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2243_sqf   : LeafSqf 2243   := by decide +kernel
private theorem c2243_range : LeafRange 2243  := by decide +kernel
private theorem c2243_ell   : LeafEll 2243    := by decide +kernel
private theorem c2243_nsq   : NSqChkSq 2243   := by decide +kernel
private theorem c2243_har   : HArithChkSq 2243 := by decide +kernel
private theorem c2243_r     : LeafR 2243      := by decide +kernel
private theorem c2243_e'    : LeafE' 2243     := by decide +kernel
private theorem c2243_f1    : LeafF1 2243     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2243_s2    : S2ChkSq 2243    := by decide +kernel
private theorem c2243_s3    : S3ChkSq 2243    := by decide +kernel
private theorem c2243_iso   : LeafIso 2243    := by decide +kernel
private theorem c2243_nof2  : NoF2ChkSq 2243  := by decide +kernel
private theorem c2243_nof3  : NoF3ChkSq 2243  := by decide +kernel
private theorem c2243_nof4z : NoF4zChkSq 2243 := by decide +kernel
theorem C'_2243 : C' 2243 :=
  ⟨c2243_sqf, c2243_range, c2243_ell, leafNSq_of_sq c2243_nsq, leafHAr_of_sq c2243_har,
   c2243_r, c2243_e', c2243_f1, leafS2_of_sq c2243_s2, leafS3_of_sq c2243_s3,
   c2243_iso, leafR8_of_sq c2243_nof2 c2243_nof3 c2243_nof4z⟩
theorem not_tile'_2243 (D : CongruentDissection 2243) : False :=
  not_tile_of_conditions' 2243 C'_2243 D

private theorem c2246_sqf   : LeafSqf 2246   := by decide +kernel
private theorem c2246_range : LeafRange 2246  := by decide +kernel
private theorem c2246_ell   : LeafEll 2246    := by decide +kernel
private theorem c2246_nsq   : NSqChkSq 2246   := by decide +kernel
private theorem c2246_har   : HArithChkSq 2246 := by decide +kernel
private theorem c2246_r     : LeafR 2246      := by decide +kernel
private theorem c2246_e'    : LeafE' 2246     := by decide +kernel
private theorem c2246_f1    : LeafF1 2246     := Or.inl (by decide)
private theorem c2246_s2    : S2ChkSq 2246    := by decide +kernel
private theorem c2246_s3    : S3ChkSq 2246    := by decide +kernel
private theorem c2246_iso   : LeafIso 2246    := by decide +kernel
private theorem c2246_nof2  : NoF2ChkSq 2246  := by decide +kernel
private theorem c2246_nof3  : NoF3ChkSq 2246  := by decide +kernel
private theorem c2246_nof4z : NoF4zChkSq 2246 := by decide +kernel
theorem C'_2246 : C' 2246 :=
  ⟨c2246_sqf, c2246_range, c2246_ell, leafNSq_of_sq c2246_nsq, leafHAr_of_sq c2246_har,
   c2246_r, c2246_e', c2246_f1, leafS2_of_sq c2246_s2, leafS3_of_sq c2246_s3,
   c2246_iso, leafR8_of_sq c2246_nof2 c2246_nof3 c2246_nof4z⟩
theorem not_tile'_2246 (D : CongruentDissection 2246) : False :=
  not_tile_of_conditions' 2246 C'_2246 D

private theorem c2251_sqf   : LeafSqf 2251   := by decide +kernel
private theorem c2251_range : LeafRange 2251  := by decide +kernel
private theorem c2251_ell   : LeafEll 2251    := by decide +kernel
private theorem c2251_nsq   : NSqChkSq 2251   := by decide +kernel
private theorem c2251_har   : HArithChkSq 2251 := by decide +kernel
private theorem c2251_r     : LeafR 2251      := by decide +kernel
private theorem c2251_e'    : LeafE' 2251     := by decide +kernel
private theorem c2251_f1    : LeafF1 2251     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2251_s2    : S2ChkSq 2251    := by decide +kernel
private theorem c2251_s3    : S3ChkSq 2251    := by decide +kernel
private theorem c2251_iso   : LeafIso 2251    := by decide +kernel
private theorem c2251_nof2  : NoF2ChkSq 2251  := by decide +kernel
private theorem c2251_nof3  : NoF3ChkSq 2251  := by decide +kernel
private theorem c2251_nof4z : NoF4zChkSq 2251 := by decide +kernel
theorem C'_2251 : C' 2251 :=
  ⟨c2251_sqf, c2251_range, c2251_ell, leafNSq_of_sq c2251_nsq, leafHAr_of_sq c2251_har,
   c2251_r, c2251_e', c2251_f1, leafS2_of_sq c2251_s2, leafS3_of_sq c2251_s3,
   c2251_iso, leafR8_of_sq c2251_nof2 c2251_nof3 c2251_nof4z⟩
theorem not_tile'_2251 (D : CongruentDissection 2251) : False :=
  not_tile_of_conditions' 2251 C'_2251 D

private theorem c2253_sqf   : LeafSqf 2253   := by decide +kernel
private theorem c2253_range : LeafRange 2253  := by decide +kernel
private theorem c2253_ell   : LeafEll 2253    := by decide +kernel
private theorem c2253_nsq   : NSqChkSq 2253   := by decide +kernel
private theorem c2253_har   : HArithChkSq 2253 := by decide +kernel
private theorem c2253_r     : LeafR 2253      := by decide +kernel
private theorem c2253_e'    : LeafE' 2253     := by decide +kernel
private theorem c2253_f1    : LeafF1 2253     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2253_s2    : S2ChkSq 2253    := by decide +kernel
private theorem c2253_s3    : S3ChkSq 2253    := by decide +kernel
private theorem c2253_iso   : LeafIso 2253    := by decide +kernel
private theorem c2253_nof2  : NoF2ChkSq 2253  := by decide +kernel
private theorem c2253_nof3  : NoF3ChkSq 2253  := by decide +kernel
private theorem c2253_nof4z : NoF4zChkSq 2253 := by decide +kernel
theorem C'_2253 : C' 2253 :=
  ⟨c2253_sqf, c2253_range, c2253_ell, leafNSq_of_sq c2253_nsq, leafHAr_of_sq c2253_har,
   c2253_r, c2253_e', c2253_f1, leafS2_of_sq c2253_s2, leafS3_of_sq c2253_s3,
   c2253_iso, leafR8_of_sq c2253_nof2 c2253_nof3 c2253_nof4z⟩
theorem not_tile'_2253 (D : CongruentDissection 2253) : False :=
  not_tile_of_conditions' 2253 C'_2253 D

private theorem c2255_sqf   : LeafSqf 2255   := by decide +kernel
private theorem c2255_range : LeafRange 2255  := by decide +kernel
private theorem c2255_ell   : LeafEll 2255    := by decide +kernel
private theorem c2255_nsq   : NSqChkSq 2255   := by decide +kernel
private theorem c2255_har   : HArithChkSq 2255 := by decide +kernel
private theorem c2255_r     : LeafR 2255      := by decide +kernel
private theorem c2255_e'    : LeafE' 2255     := by decide +kernel
private theorem c2255_f1    : LeafF1 2255     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2255_s2    : S2ChkSq 2255    := by decide +kernel
private theorem c2255_s3    : S3ChkSq 2255    := by decide +kernel
private theorem c2255_iso   : LeafIso 2255    := by decide +kernel
private theorem c2255_nof2  : NoF2ChkSq 2255  := by decide +kernel
private theorem c2255_nof3  : NoF3ChkSq 2255  := by decide +kernel
private theorem c2255_nof4z : NoF4zChkSq 2255 := by decide +kernel
theorem C'_2255 : C' 2255 :=
  ⟨c2255_sqf, c2255_range, c2255_ell, leafNSq_of_sq c2255_nsq, leafHAr_of_sq c2255_har,
   c2255_r, c2255_e', c2255_f1, leafS2_of_sq c2255_s2, leafS3_of_sq c2255_s3,
   c2255_iso, leafR8_of_sq c2255_nof2 c2255_nof3 c2255_nof4z⟩
theorem not_tile'_2255 (D : CongruentDissection 2255) : False :=
  not_tile_of_conditions' 2255 C'_2255 D

end Erdos634.Draft.AllN2

/- AllN2Check124: N = 2922, 2923, 2926, 2927, 2931
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2922_sqf   : LeafSqf 2922   := by decide +kernel
private theorem c2922_range : LeafRange 2922  := by decide +kernel
private theorem c2922_ell   : LeafEll 2922    := by decide +kernel
private theorem c2922_nsq   : NSqChkSq 2922   := by decide +kernel
private theorem c2922_har   : HArithChkSq 2922 := by decide +kernel
private theorem c2922_r     : LeafR 2922      := by decide +kernel
private theorem c2922_e'    : LeafE' 2922     := by decide +kernel
private theorem c2922_f1    : LeafF1 2922     := Or.inl (by decide)
private theorem c2922_s2    : S2ChkSq 2922    := by decide +kernel
private theorem c2922_s3    : S3ChkSq 2922    := by decide +kernel
private theorem c2922_iso   : LeafIso 2922    := by decide +kernel
private theorem c2922_nof2  : NoF2ChkSq 2922  := by decide +kernel
private theorem c2922_nof3  : NoF3ChkSq 2922  := by decide +kernel
private theorem c2922_nof4z : NoF4zChkSq 2922 := by decide +kernel
theorem C'_2922 : C' 2922 :=
  ⟨c2922_sqf, c2922_range, c2922_ell, leafNSq_of_sq c2922_nsq, leafHAr_of_sq c2922_har,
   c2922_r, c2922_e', c2922_f1, leafS2_of_sq c2922_s2, leafS3_of_sq c2922_s3,
   c2922_iso, leafR8_of_sq c2922_nof2 c2922_nof3 c2922_nof4z⟩
theorem not_tile'_2922 (D : CongruentDissection 2922) : False :=
  not_tile_of_conditions' 2922 C'_2922 D

private theorem c2923_sqf   : LeafSqf 2923   := by decide +kernel
private theorem c2923_range : LeafRange 2923  := by decide +kernel
private theorem c2923_ell   : LeafEll 2923    := by decide +kernel
private theorem c2923_nsq   : NSqChkSq 2923   := by decide +kernel
private theorem c2923_har   : HArithChkSq 2923 := by decide +kernel
private theorem c2923_r     : LeafR 2923      := by decide +kernel
private theorem c2923_e'    : LeafE' 2923     := by decide +kernel
private theorem c2923_f1    : LeafF1 2923     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2923_s2    : S2ChkSq 2923    := by decide +kernel
private theorem c2923_s3    : S3ChkSq 2923    := by decide +kernel
private theorem c2923_iso   : LeafIso 2923    := by decide +kernel
private theorem c2923_nof2  : NoF2ChkSq 2923  := by decide +kernel
private theorem c2923_nof3  : NoF3ChkSq 2923  := by decide +kernel
private theorem c2923_nof4z : NoF4zChkSq 2923 := by decide +kernel
theorem C'_2923 : C' 2923 :=
  ⟨c2923_sqf, c2923_range, c2923_ell, leafNSq_of_sq c2923_nsq, leafHAr_of_sq c2923_har,
   c2923_r, c2923_e', c2923_f1, leafS2_of_sq c2923_s2, leafS3_of_sq c2923_s3,
   c2923_iso, leafR8_of_sq c2923_nof2 c2923_nof3 c2923_nof4z⟩
theorem not_tile'_2923 (D : CongruentDissection 2923) : False :=
  not_tile_of_conditions' 2923 C'_2923 D

private theorem c2926_sqf   : LeafSqf 2926   := by decide +kernel
private theorem c2926_range : LeafRange 2926  := by decide +kernel
private theorem c2926_ell   : LeafEll 2926    := by decide +kernel
private theorem c2926_nsq   : NSqChkSq 2926   := by decide +kernel
private theorem c2926_har   : HArithChkSq 2926 := by decide +kernel
private theorem c2926_r     : LeafR 2926      := by decide +kernel
private theorem c2926_e'    : LeafE' 2926     := by decide +kernel
private theorem c2926_f1    : LeafF1 2926     := Or.inl (by decide)
private theorem c2926_s2    : S2ChkSq 2926    := by decide +kernel
private theorem c2926_s3    : S3ChkSq 2926    := by decide +kernel
private theorem c2926_iso   : LeafIso 2926    := by decide +kernel
private theorem c2926_nof2  : NoF2ChkSq 2926  := by decide +kernel
private theorem c2926_nof3  : NoF3ChkSq 2926  := by decide +kernel
private theorem c2926_nof4z : NoF4zChkSq 2926 := by decide +kernel
theorem C'_2926 : C' 2926 :=
  ⟨c2926_sqf, c2926_range, c2926_ell, leafNSq_of_sq c2926_nsq, leafHAr_of_sq c2926_har,
   c2926_r, c2926_e', c2926_f1, leafS2_of_sq c2926_s2, leafS3_of_sq c2926_s3,
   c2926_iso, leafR8_of_sq c2926_nof2 c2926_nof3 c2926_nof4z⟩
theorem not_tile'_2926 (D : CongruentDissection 2926) : False :=
  not_tile_of_conditions' 2926 C'_2926 D

private theorem c2927_sqf   : LeafSqf 2927   := by decide +kernel
private theorem c2927_range : LeafRange 2927  := by decide +kernel
private theorem c2927_ell   : LeafEll 2927    := by decide +kernel
private theorem c2927_nsq   : NSqChkSq 2927   := by decide +kernel
private theorem c2927_har   : HArithChkSq 2927 := by decide +kernel
private theorem c2927_r     : LeafR 2927      := by decide +kernel
private theorem c2927_e'    : LeafE' 2927     := by decide +kernel
private theorem c2927_f1    : LeafF1 2927     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2927_s2    : S2ChkSq 2927    := by decide +kernel
private theorem c2927_s3    : S3ChkSq 2927    := by decide +kernel
private theorem c2927_iso   : LeafIso 2927    := by decide +kernel
private theorem c2927_nof2  : NoF2ChkSq 2927  := by decide +kernel
private theorem c2927_nof3  : NoF3ChkSq 2927  := by decide +kernel
private theorem c2927_nof4z : NoF4zChkSq 2927 := by decide +kernel
theorem C'_2927 : C' 2927 :=
  ⟨c2927_sqf, c2927_range, c2927_ell, leafNSq_of_sq c2927_nsq, leafHAr_of_sq c2927_har,
   c2927_r, c2927_e', c2927_f1, leafS2_of_sq c2927_s2, leafS3_of_sq c2927_s3,
   c2927_iso, leafR8_of_sq c2927_nof2 c2927_nof3 c2927_nof4z⟩
theorem not_tile'_2927 (D : CongruentDissection 2927) : False :=
  not_tile_of_conditions' 2927 C'_2927 D

private theorem c2931_sqf   : LeafSqf 2931   := by decide +kernel
private theorem c2931_range : LeafRange 2931  := by decide +kernel
private theorem c2931_ell   : LeafEll 2931    := by decide +kernel
private theorem c2931_nsq   : NSqChkSq 2931   := by decide +kernel
private theorem c2931_har   : HArithChkSq 2931 := by decide +kernel
private theorem c2931_r     : LeafR 2931      := by decide +kernel
private theorem c2931_e'    : LeafE' 2931     := by decide +kernel
private theorem c2931_f1    : LeafF1 2931     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2931_s2    : S2ChkSq 2931    := by decide +kernel
private theorem c2931_s3    : S3ChkSq 2931    := by decide +kernel
private theorem c2931_iso   : LeafIso 2931    := by decide +kernel
private theorem c2931_nof2  : NoF2ChkSq 2931  := by decide +kernel
private theorem c2931_nof3  : NoF3ChkSq 2931  := by decide +kernel
private theorem c2931_nof4z : NoF4zChkSq 2931 := by decide +kernel
theorem C'_2931 : C' 2931 :=
  ⟨c2931_sqf, c2931_range, c2931_ell, leafNSq_of_sq c2931_nsq, leafHAr_of_sq c2931_har,
   c2931_r, c2931_e', c2931_f1, leafS2_of_sq c2931_s2, leafS3_of_sq c2931_s3,
   c2931_iso, leafR8_of_sq c2931_nof2 c2931_nof3 c2931_nof4z⟩
theorem not_tile'_2931 (D : CongruentDissection 2931) : False :=
  not_tile_of_conditions' 2931 C'_2931 D

end Erdos634.Draft.AllN2

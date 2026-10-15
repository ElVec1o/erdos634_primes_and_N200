/- AllN2Check89: N = 2478, 2479, 2481, 2483, 2486
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2478_sqf   : LeafSqf 2478   := by decide +kernel
private theorem c2478_range : LeafRange 2478  := by decide +kernel
private theorem c2478_ell   : LeafEll 2478    := by decide +kernel
private theorem c2478_nsq   : NSqChkSq 2478   := by decide +kernel
private theorem c2478_har   : HArithChkSq 2478 := by decide +kernel
private theorem c2478_r     : LeafR 2478      := by decide +kernel
private theorem c2478_e'    : LeafE' 2478     := by decide +kernel
private theorem c2478_f1    : LeafF1 2478     := Or.inl (by decide)
private theorem c2478_s2    : S2ChkSq 2478    := by decide +kernel
private theorem c2478_s3    : S3ChkSq 2478    := by decide +kernel
private theorem c2478_iso   : LeafIso 2478    := by decide +kernel
private theorem c2478_nof2  : NoF2ChkSq 2478  := by decide +kernel
private theorem c2478_nof3  : NoF3ChkSq 2478  := by decide +kernel
private theorem c2478_nof4z : NoF4zChkSq 2478 := by decide +kernel
theorem C'_2478 : C' 2478 :=
  ⟨c2478_sqf, c2478_range, c2478_ell, leafNSq_of_sq c2478_nsq, leafHAr_of_sq c2478_har,
   c2478_r, c2478_e', c2478_f1, leafS2_of_sq c2478_s2, leafS3_of_sq c2478_s3,
   c2478_iso, leafR8_of_sq c2478_nof2 c2478_nof3 c2478_nof4z⟩
theorem not_tile'_2478 (D : CongruentDissection 2478) : False :=
  not_tile_of_conditions' 2478 C'_2478 D

private theorem c2479_sqf   : LeafSqf 2479   := by decide +kernel
private theorem c2479_range : LeafRange 2479  := by decide +kernel
private theorem c2479_ell   : LeafEll 2479    := by decide +kernel
private theorem c2479_nsq   : NSqChkSq 2479   := by decide +kernel
private theorem c2479_har   : HArithChkSq 2479 := by decide +kernel
private theorem c2479_r     : LeafR 2479      := by decide +kernel
private theorem c2479_e'    : LeafE' 2479     := by decide +kernel
private theorem c2479_f1    : LeafF1 2479     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2479_s2    : S2ChkSq 2479    := by decide +kernel
private theorem c2479_s3    : S3ChkSq 2479    := by decide +kernel
private theorem c2479_iso   : LeafIso 2479    := by decide +kernel
private theorem c2479_nof2  : NoF2ChkSq 2479  := by decide +kernel
private theorem c2479_nof3  : NoF3ChkSq 2479  := by decide +kernel
private theorem c2479_nof4z : NoF4zChkSq 2479 := by decide +kernel
theorem C'_2479 : C' 2479 :=
  ⟨c2479_sqf, c2479_range, c2479_ell, leafNSq_of_sq c2479_nsq, leafHAr_of_sq c2479_har,
   c2479_r, c2479_e', c2479_f1, leafS2_of_sq c2479_s2, leafS3_of_sq c2479_s3,
   c2479_iso, leafR8_of_sq c2479_nof2 c2479_nof3 c2479_nof4z⟩
theorem not_tile'_2479 (D : CongruentDissection 2479) : False :=
  not_tile_of_conditions' 2479 C'_2479 D

private theorem c2481_sqf   : LeafSqf 2481   := by decide +kernel
private theorem c2481_range : LeafRange 2481  := by decide +kernel
private theorem c2481_ell   : LeafEll 2481    := by decide +kernel
private theorem c2481_nsq   : NSqChkSq 2481   := by decide +kernel
private theorem c2481_har   : HArithChkSq 2481 := by decide +kernel
private theorem c2481_r     : LeafR 2481      := by decide +kernel
private theorem c2481_e'    : LeafE' 2481     := by decide +kernel
private theorem c2481_f1    : LeafF1 2481     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2481_s2    : S2ChkSq 2481    := by decide +kernel
private theorem c2481_s3    : S3ChkSq 2481    := by decide +kernel
private theorem c2481_iso   : LeafIso 2481    := by decide +kernel
private theorem c2481_nof2  : NoF2ChkSq 2481  := by decide +kernel
private theorem c2481_nof3  : NoF3ChkSq 2481  := by decide +kernel
private theorem c2481_nof4z : NoF4zChkSq 2481 := by decide +kernel
theorem C'_2481 : C' 2481 :=
  ⟨c2481_sqf, c2481_range, c2481_ell, leafNSq_of_sq c2481_nsq, leafHAr_of_sq c2481_har,
   c2481_r, c2481_e', c2481_f1, leafS2_of_sq c2481_s2, leafS3_of_sq c2481_s3,
   c2481_iso, leafR8_of_sq c2481_nof2 c2481_nof3 c2481_nof4z⟩
theorem not_tile'_2481 (D : CongruentDissection 2481) : False :=
  not_tile_of_conditions' 2481 C'_2481 D

private theorem c2483_sqf   : LeafSqf 2483   := by decide +kernel
private theorem c2483_range : LeafRange 2483  := by decide +kernel
private theorem c2483_ell   : LeafEll 2483    := by decide +kernel
private theorem c2483_nsq   : NSqChkSq 2483   := by decide +kernel
private theorem c2483_har   : HArithChkSq 2483 := by decide +kernel
private theorem c2483_r     : LeafR 2483      := by decide +kernel
private theorem c2483_e'    : LeafE' 2483     := by decide +kernel
private theorem c2483_f1    : LeafF1 2483     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2483_s2    : S2ChkSq 2483    := by decide +kernel
private theorem c2483_s3    : S3ChkSq 2483    := by decide +kernel
private theorem c2483_iso   : LeafIso 2483    := by decide +kernel
private theorem c2483_nof2  : NoF2ChkSq 2483  := by decide +kernel
private theorem c2483_nof3  : NoF3ChkSq 2483  := by decide +kernel
private theorem c2483_nof4z : NoF4zChkSq 2483 := by decide +kernel
theorem C'_2483 : C' 2483 :=
  ⟨c2483_sqf, c2483_range, c2483_ell, leafNSq_of_sq c2483_nsq, leafHAr_of_sq c2483_har,
   c2483_r, c2483_e', c2483_f1, leafS2_of_sq c2483_s2, leafS3_of_sq c2483_s3,
   c2483_iso, leafR8_of_sq c2483_nof2 c2483_nof3 c2483_nof4z⟩
theorem not_tile'_2483 (D : CongruentDissection 2483) : False :=
  not_tile_of_conditions' 2483 C'_2483 D

private theorem c2486_sqf   : LeafSqf 2486   := by decide +kernel
private theorem c2486_range : LeafRange 2486  := by decide +kernel
private theorem c2486_ell   : LeafEll 2486    := by decide +kernel
private theorem c2486_nsq   : NSqChkSq 2486   := by decide +kernel
private theorem c2486_har   : HArithChkSq 2486 := by decide +kernel
private theorem c2486_r     : LeafR 2486      := by decide +kernel
private theorem c2486_e'    : LeafE' 2486     := by decide +kernel
private theorem c2486_f1    : LeafF1 2486     := Or.inl (by decide)
private theorem c2486_s2    : S2ChkSq 2486    := by decide +kernel
private theorem c2486_s3    : S3ChkSq 2486    := by decide +kernel
private theorem c2486_iso   : LeafIso 2486    := by decide +kernel
private theorem c2486_nof2  : NoF2ChkSq 2486  := by decide +kernel
private theorem c2486_nof3  : NoF3ChkSq 2486  := by decide +kernel
private theorem c2486_nof4z : NoF4zChkSq 2486 := by decide +kernel
theorem C'_2486 : C' 2486 :=
  ⟨c2486_sqf, c2486_range, c2486_ell, leafNSq_of_sq c2486_nsq, leafHAr_of_sq c2486_har,
   c2486_r, c2486_e', c2486_f1, leafS2_of_sq c2486_s2, leafS3_of_sq c2486_s3,
   c2486_iso, leafR8_of_sq c2486_nof2 c2486_nof3 c2486_nof4z⟩
theorem not_tile'_2486 (D : CongruentDissection 2486) : False :=
  not_tile_of_conditions' 2486 C'_2486 D

end Erdos634.Draft.AllN2

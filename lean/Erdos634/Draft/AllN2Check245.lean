/- AllN2Check245: N = 4478, 4479, 4483, 4486, 4487
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4478_sqf   : LeafSqf 4478   := by decide +kernel
private theorem c4478_range : LeafRange 4478  := by decide +kernel
private theorem c4478_ell   : LeafEll 4478    := by decide +kernel
private theorem c4478_nsq   : NSqChkSq 4478   := by decide +kernel
private theorem c4478_har   : HArithChkSq 4478 := by decide +kernel
private theorem c4478_r     : LeafR 4478      := by decide +kernel
private theorem c4478_e'    : LeafE' 4478     := by decide +kernel
private theorem c4478_f1    : LeafF1 4478     := Or.inl (by decide)
private theorem c4478_s2    : S2ChkSq 4478    := by decide +kernel
private theorem c4478_s3    : S3ChkSq 4478    := by decide +kernel
private theorem c4478_iso   : LeafIso 4478    := by decide +kernel
private theorem c4478_nof2  : NoF2ChkSq 4478  := by decide +kernel
private theorem c4478_nof3  : NoF3ChkSq 4478  := by decide +kernel
private theorem c4478_nof4z : NoF4zChkSq 4478 := by decide +kernel
theorem C'_4478 : C' 4478 :=
  ⟨c4478_sqf, c4478_range, c4478_ell, leafNSq_of_sq c4478_nsq, leafHAr_of_sq c4478_har,
   c4478_r, c4478_e', c4478_f1, leafS2_of_sq c4478_s2, leafS3_of_sq c4478_s3,
   c4478_iso, leafR8_of_sq c4478_nof2 c4478_nof3 c4478_nof4z⟩
theorem not_tile'_4478 (D : CongruentDissection 4478) : False :=
  not_tile_of_conditions' 4478 C'_4478 D

private theorem c4479_sqf   : LeafSqf 4479   := by decide +kernel
private theorem c4479_range : LeafRange 4479  := by decide +kernel
private theorem c4479_ell   : LeafEll 4479    := by decide +kernel
private theorem c4479_nsq   : NSqChkSq 4479   := by decide +kernel
private theorem c4479_har   : HArithChkSq 4479 := by decide +kernel
private theorem c4479_r     : LeafR 4479      := by decide +kernel
private theorem c4479_e'    : LeafE' 4479     := by decide +kernel
private theorem c4479_f1    : LeafF1 4479     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4479_s2    : S2ChkSq 4479    := by decide +kernel
private theorem c4479_s3    : S3ChkSq 4479    := by decide +kernel
private theorem c4479_iso   : LeafIso 4479    := by decide +kernel
private theorem c4479_nof2  : NoF2ChkSq 4479  := by decide +kernel
private theorem c4479_nof3  : NoF3ChkSq 4479  := by decide +kernel
private theorem c4479_nof4z : NoF4zChkSq 4479 := by decide +kernel
theorem C'_4479 : C' 4479 :=
  ⟨c4479_sqf, c4479_range, c4479_ell, leafNSq_of_sq c4479_nsq, leafHAr_of_sq c4479_har,
   c4479_r, c4479_e', c4479_f1, leafS2_of_sq c4479_s2, leafS3_of_sq c4479_s3,
   c4479_iso, leafR8_of_sq c4479_nof2 c4479_nof3 c4479_nof4z⟩
theorem not_tile'_4479 (D : CongruentDissection 4479) : False :=
  not_tile_of_conditions' 4479 C'_4479 D

private theorem c4483_sqf   : LeafSqf 4483   := by decide +kernel
private theorem c4483_range : LeafRange 4483  := by decide +kernel
private theorem c4483_ell   : LeafEll 4483    := by decide +kernel
private theorem c4483_nsq   : NSqChkSq 4483   := by decide +kernel
private theorem c4483_har   : HArithChkSq 4483 := by decide +kernel
private theorem c4483_r     : LeafR 4483      := by decide +kernel
private theorem c4483_e'    : LeafE' 4483     := by decide +kernel
private theorem c4483_f1    : LeafF1 4483     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4483_s2    : S2ChkSq 4483    := by decide +kernel
private theorem c4483_s3    : S3ChkSq 4483    := by decide +kernel
private theorem c4483_iso   : LeafIso 4483    := by decide +kernel
private theorem c4483_nof2  : NoF2ChkSq 4483  := by decide +kernel
private theorem c4483_nof3  : NoF3ChkSq 4483  := by decide +kernel
private theorem c4483_nof4z : NoF4zChkSq 4483 := by decide +kernel
theorem C'_4483 : C' 4483 :=
  ⟨c4483_sqf, c4483_range, c4483_ell, leafNSq_of_sq c4483_nsq, leafHAr_of_sq c4483_har,
   c4483_r, c4483_e', c4483_f1, leafS2_of_sq c4483_s2, leafS3_of_sq c4483_s3,
   c4483_iso, leafR8_of_sq c4483_nof2 c4483_nof3 c4483_nof4z⟩
theorem not_tile'_4483 (D : CongruentDissection 4483) : False :=
  not_tile_of_conditions' 4483 C'_4483 D

private theorem c4486_sqf   : LeafSqf 4486   := by decide +kernel
private theorem c4486_range : LeafRange 4486  := by decide +kernel
private theorem c4486_ell   : LeafEll 4486    := by decide +kernel
private theorem c4486_nsq   : NSqChkSq 4486   := by decide +kernel
private theorem c4486_har   : HArithChkSq 4486 := by decide +kernel
private theorem c4486_r     : LeafR 4486      := by decide +kernel
private theorem c4486_e'    : LeafE' 4486     := by decide +kernel
private theorem c4486_f1    : LeafF1 4486     := Or.inl (by decide)
private theorem c4486_s2    : S2ChkSq 4486    := by decide +kernel
private theorem c4486_s3    : S3ChkSq 4486    := by decide +kernel
private theorem c4486_iso   : LeafIso 4486    := by decide +kernel
private theorem c4486_nof2  : NoF2ChkSq 4486  := by decide +kernel
private theorem c4486_nof3  : NoF3ChkSq 4486  := by decide +kernel
private theorem c4486_nof4z : NoF4zChkSq 4486 := by decide +kernel
theorem C'_4486 : C' 4486 :=
  ⟨c4486_sqf, c4486_range, c4486_ell, leafNSq_of_sq c4486_nsq, leafHAr_of_sq c4486_har,
   c4486_r, c4486_e', c4486_f1, leafS2_of_sq c4486_s2, leafS3_of_sq c4486_s3,
   c4486_iso, leafR8_of_sq c4486_nof2 c4486_nof3 c4486_nof4z⟩
theorem not_tile'_4486 (D : CongruentDissection 4486) : False :=
  not_tile_of_conditions' 4486 C'_4486 D

private theorem c4487_sqf   : LeafSqf 4487   := by decide +kernel
private theorem c4487_range : LeafRange 4487  := by decide +kernel
private theorem c4487_ell   : LeafEll 4487    := by decide +kernel
private theorem c4487_nsq   : NSqChkSq 4487   := by decide +kernel
private theorem c4487_har   : HArithChkSq 4487 := by decide +kernel
private theorem c4487_r     : LeafR 4487      := by decide +kernel
private theorem c4487_e'    : LeafE' 4487     := by decide +kernel
private theorem c4487_f1    : LeafF1 4487     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4487_s2    : S2ChkSq 4487    := by decide +kernel
private theorem c4487_s3    : S3ChkSq 4487    := by decide +kernel
private theorem c4487_iso   : LeafIso 4487    := by decide +kernel
private theorem c4487_nof2  : NoF2ChkSq 4487  := by decide +kernel
private theorem c4487_nof3  : NoF3ChkSq 4487  := by decide +kernel
private theorem c4487_nof4z : NoF4zChkSq 4487 := by decide +kernel
theorem C'_4487 : C' 4487 :=
  ⟨c4487_sqf, c4487_range, c4487_ell, leafNSq_of_sq c4487_nsq, leafHAr_of_sq c4487_har,
   c4487_r, c4487_e', c4487_f1, leafS2_of_sq c4487_s2, leafS3_of_sq c4487_s3,
   c4487_iso, leafR8_of_sq c4487_nof2 c4487_nof3 c4487_nof4z⟩
theorem not_tile'_4487 (D : CongruentDissection 4487) : False :=
  not_tile_of_conditions' 4487 C'_4487 D

end Erdos634.Draft.AllN2

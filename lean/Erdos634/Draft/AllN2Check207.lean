/- AllN2Check207: N = 3997, 3998, 4003, 4006, 4007
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3997_sqf   : LeafSqf 3997   := by decide +kernel
private theorem c3997_range : LeafRange 3997  := by decide +kernel
private theorem c3997_ell   : LeafEll 3997    := by decide +kernel
private theorem c3997_nsq   : NSqChkSq 3997   := by decide +kernel
private theorem c3997_har   : HArithChkSq 3997 := by decide +kernel
private theorem c3997_r     : LeafR 3997      := by decide +kernel
private theorem c3997_e'    : LeafE' 3997     := by decide +kernel
private theorem c3997_f1    : LeafF1 3997     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3997_s2    : S2ChkSq 3997    := by decide +kernel
private theorem c3997_s3    : S3ChkSq 3997    := by decide +kernel
private theorem c3997_iso   : LeafIso 3997    := by decide +kernel
private theorem c3997_nof2  : NoF2ChkSq 3997  := by decide +kernel
private theorem c3997_nof3  : NoF3ChkSq 3997  := by decide +kernel
private theorem c3997_nof4z : NoF4zChkSq 3997 := by decide +kernel
theorem C'_3997 : C' 3997 :=
  ⟨c3997_sqf, c3997_range, c3997_ell, leafNSq_of_sq c3997_nsq, leafHAr_of_sq c3997_har,
   c3997_r, c3997_e', c3997_f1, leafS2_of_sq c3997_s2, leafS3_of_sq c3997_s3,
   c3997_iso, leafR8_of_sq c3997_nof2 c3997_nof3 c3997_nof4z⟩
theorem not_tile'_3997 (D : CongruentDissection 3997) : False :=
  not_tile_of_conditions' 3997 C'_3997 D

private theorem c3998_sqf   : LeafSqf 3998   := by decide +kernel
private theorem c3998_range : LeafRange 3998  := by decide +kernel
private theorem c3998_ell   : LeafEll 3998    := by decide +kernel
private theorem c3998_nsq   : NSqChkSq 3998   := by decide +kernel
private theorem c3998_har   : HArithChkSq 3998 := by decide +kernel
private theorem c3998_r     : LeafR 3998      := by decide +kernel
private theorem c3998_e'    : LeafE' 3998     := by decide +kernel
private theorem c3998_f1    : LeafF1 3998     := Or.inl (by decide)
private theorem c3998_s2    : S2ChkSq 3998    := by decide +kernel
private theorem c3998_s3    : S3ChkSq 3998    := by decide +kernel
private theorem c3998_iso   : LeafIso 3998    := by decide +kernel
private theorem c3998_nof2  : NoF2ChkSq 3998  := by decide +kernel
private theorem c3998_nof3  : NoF3ChkSq 3998  := by decide +kernel
private theorem c3998_nof4z : NoF4zChkSq 3998 := by decide +kernel
theorem C'_3998 : C' 3998 :=
  ⟨c3998_sqf, c3998_range, c3998_ell, leafNSq_of_sq c3998_nsq, leafHAr_of_sq c3998_har,
   c3998_r, c3998_e', c3998_f1, leafS2_of_sq c3998_s2, leafS3_of_sq c3998_s3,
   c3998_iso, leafR8_of_sq c3998_nof2 c3998_nof3 c3998_nof4z⟩
theorem not_tile'_3998 (D : CongruentDissection 3998) : False :=
  not_tile_of_conditions' 3998 C'_3998 D

private theorem c4003_sqf   : LeafSqf 4003   := by decide +kernel
private theorem c4003_range : LeafRange 4003  := by decide +kernel
private theorem c4003_ell   : LeafEll 4003    := by decide +kernel
private theorem c4003_nsq   : NSqChkSq 4003   := by decide +kernel
private theorem c4003_har   : HArithChkSq 4003 := by decide +kernel
private theorem c4003_r     : LeafR 4003      := by decide +kernel
private theorem c4003_e'    : LeafE' 4003     := by decide +kernel
private theorem c4003_f1    : LeafF1 4003     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4003_s2    : S2ChkSq 4003    := by decide +kernel
private theorem c4003_s3    : S3ChkSq 4003    := by decide +kernel
private theorem c4003_iso   : LeafIso 4003    := by decide +kernel
private theorem c4003_nof2  : NoF2ChkSq 4003  := by decide +kernel
private theorem c4003_nof3  : NoF3ChkSq 4003  := by decide +kernel
private theorem c4003_nof4z : NoF4zChkSq 4003 := by decide +kernel
theorem C'_4003 : C' 4003 :=
  ⟨c4003_sqf, c4003_range, c4003_ell, leafNSq_of_sq c4003_nsq, leafHAr_of_sq c4003_har,
   c4003_r, c4003_e', c4003_f1, leafS2_of_sq c4003_s2, leafS3_of_sq c4003_s3,
   c4003_iso, leafR8_of_sq c4003_nof2 c4003_nof3 c4003_nof4z⟩
theorem not_tile'_4003 (D : CongruentDissection 4003) : False :=
  not_tile_of_conditions' 4003 C'_4003 D

private theorem c4006_sqf   : LeafSqf 4006   := by decide +kernel
private theorem c4006_range : LeafRange 4006  := by decide +kernel
private theorem c4006_ell   : LeafEll 4006    := by decide +kernel
private theorem c4006_nsq   : NSqChkSq 4006   := by decide +kernel
private theorem c4006_har   : HArithChkSq 4006 := by decide +kernel
private theorem c4006_r     : LeafR 4006      := by decide +kernel
private theorem c4006_e'    : LeafE' 4006     := by decide +kernel
private theorem c4006_f1    : LeafF1 4006     := Or.inl (by decide)
private theorem c4006_s2    : S2ChkSq 4006    := by decide +kernel
private theorem c4006_s3    : S3ChkSq 4006    := by decide +kernel
private theorem c4006_iso   : LeafIso 4006    := by decide +kernel
private theorem c4006_nof2  : NoF2ChkSq 4006  := by decide +kernel
private theorem c4006_nof3  : NoF3ChkSq 4006  := by decide +kernel
private theorem c4006_nof4z : NoF4zChkSq 4006 := by decide +kernel
theorem C'_4006 : C' 4006 :=
  ⟨c4006_sqf, c4006_range, c4006_ell, leafNSq_of_sq c4006_nsq, leafHAr_of_sq c4006_har,
   c4006_r, c4006_e', c4006_f1, leafS2_of_sq c4006_s2, leafS3_of_sq c4006_s3,
   c4006_iso, leafR8_of_sq c4006_nof2 c4006_nof3 c4006_nof4z⟩
theorem not_tile'_4006 (D : CongruentDissection 4006) : False :=
  not_tile_of_conditions' 4006 C'_4006 D

private theorem c4007_sqf   : LeafSqf 4007   := by decide +kernel
private theorem c4007_range : LeafRange 4007  := by decide +kernel
private theorem c4007_ell   : LeafEll 4007    := by decide +kernel
private theorem c4007_nsq   : NSqChkSq 4007   := by decide +kernel
private theorem c4007_har   : HArithChkSq 4007 := by decide +kernel
private theorem c4007_r     : LeafR 4007      := by decide +kernel
private theorem c4007_e'    : LeafE' 4007     := by decide +kernel
private theorem c4007_f1    : LeafF1 4007     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4007_s2    : S2ChkSq 4007    := by decide +kernel
private theorem c4007_s3    : S3ChkSq 4007    := by decide +kernel
private theorem c4007_iso   : LeafIso 4007    := by decide +kernel
private theorem c4007_nof2  : NoF2ChkSq 4007  := by decide +kernel
private theorem c4007_nof3  : NoF3ChkSq 4007  := by decide +kernel
private theorem c4007_nof4z : NoF4zChkSq 4007 := by decide +kernel
theorem C'_4007 : C' 4007 :=
  ⟨c4007_sqf, c4007_range, c4007_ell, leafNSq_of_sq c4007_nsq, leafHAr_of_sq c4007_har,
   c4007_r, c4007_e', c4007_f1, leafS2_of_sq c4007_s2, leafS3_of_sq c4007_s3,
   c4007_iso, leafR8_of_sq c4007_nof2 c4007_nof3 c4007_nof4z⟩
theorem not_tile'_4007 (D : CongruentDissection 4007) : False :=
  not_tile_of_conditions' 4007 C'_4007 D

end Erdos634.Draft.AllN2

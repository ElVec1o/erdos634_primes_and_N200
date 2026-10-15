/- AllN2Check129: N = 2991, 2994, 2995, 2998, 2999
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2991_sqf   : LeafSqf 2991   := by decide +kernel
private theorem c2991_range : LeafRange 2991  := by decide +kernel
private theorem c2991_ell   : LeafEll 2991    := by decide +kernel
private theorem c2991_nsq   : NSqChkSq 2991   := by decide +kernel
private theorem c2991_har   : HArithChkSq 2991 := by decide +kernel
private theorem c2991_r     : LeafR 2991      := by decide +kernel
private theorem c2991_e'    : LeafE' 2991     := by decide +kernel
private theorem c2991_f1    : LeafF1 2991     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2991_s2    : S2ChkSq 2991    := by decide +kernel
private theorem c2991_s3    : S3ChkSq 2991    := by decide +kernel
private theorem c2991_iso   : LeafIso 2991    := by decide +kernel
private theorem c2991_nof2  : NoF2ChkSq 2991  := by decide +kernel
private theorem c2991_nof3  : NoF3ChkSq 2991  := by decide +kernel
private theorem c2991_nof4z : NoF4zChkSq 2991 := by decide +kernel
theorem C'_2991 : C' 2991 :=
  ⟨c2991_sqf, c2991_range, c2991_ell, leafNSq_of_sq c2991_nsq, leafHAr_of_sq c2991_har,
   c2991_r, c2991_e', c2991_f1, leafS2_of_sq c2991_s2, leafS3_of_sq c2991_s3,
   c2991_iso, leafR8_of_sq c2991_nof2 c2991_nof3 c2991_nof4z⟩
theorem not_tile'_2991 (D : CongruentDissection 2991) : False :=
  not_tile_of_conditions' 2991 C'_2991 D

private theorem c2994_sqf   : LeafSqf 2994   := by decide +kernel
private theorem c2994_range : LeafRange 2994  := by decide +kernel
private theorem c2994_ell   : LeafEll 2994    := by decide +kernel
private theorem c2994_nsq   : NSqChkSq 2994   := by decide +kernel
private theorem c2994_har   : HArithChkSq 2994 := by decide +kernel
private theorem c2994_r     : LeafR 2994      := by decide +kernel
private theorem c2994_e'    : LeafE' 2994     := by decide +kernel
private theorem c2994_f1    : LeafF1 2994     := Or.inl (by decide)
private theorem c2994_s2    : S2ChkSq 2994    := by decide +kernel
private theorem c2994_s3    : S3ChkSq 2994    := by decide +kernel
private theorem c2994_iso   : LeafIso 2994    := by decide +kernel
private theorem c2994_nof2  : NoF2ChkSq 2994  := by decide +kernel
private theorem c2994_nof3  : NoF3ChkSq 2994  := by decide +kernel
private theorem c2994_nof4z : NoF4zChkSq 2994 := by decide +kernel
theorem C'_2994 : C' 2994 :=
  ⟨c2994_sqf, c2994_range, c2994_ell, leafNSq_of_sq c2994_nsq, leafHAr_of_sq c2994_har,
   c2994_r, c2994_e', c2994_f1, leafS2_of_sq c2994_s2, leafS3_of_sq c2994_s3,
   c2994_iso, leafR8_of_sq c2994_nof2 c2994_nof3 c2994_nof4z⟩
theorem not_tile'_2994 (D : CongruentDissection 2994) : False :=
  not_tile_of_conditions' 2994 C'_2994 D

private theorem c2995_sqf   : LeafSqf 2995   := by decide +kernel
private theorem c2995_range : LeafRange 2995  := by decide +kernel
private theorem c2995_ell   : LeafEll 2995    := by decide +kernel
private theorem c2995_nsq   : NSqChkSq 2995   := by decide +kernel
private theorem c2995_har   : HArithChkSq 2995 := by decide +kernel
private theorem c2995_r     : LeafR 2995      := by decide +kernel
private theorem c2995_e'    : LeafE' 2995     := by decide +kernel
private theorem c2995_f1    : LeafF1 2995     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2995_s2    : S2ChkSq 2995    := by decide +kernel
private theorem c2995_s3    : S3ChkSq 2995    := by decide +kernel
private theorem c2995_iso   : LeafIso 2995    := by decide +kernel
private theorem c2995_nof2  : NoF2ChkSq 2995  := by decide +kernel
private theorem c2995_nof3  : NoF3ChkSq 2995  := by decide +kernel
private theorem c2995_nof4z : NoF4zChkSq 2995 := by decide +kernel
theorem C'_2995 : C' 2995 :=
  ⟨c2995_sqf, c2995_range, c2995_ell, leafNSq_of_sq c2995_nsq, leafHAr_of_sq c2995_har,
   c2995_r, c2995_e', c2995_f1, leafS2_of_sq c2995_s2, leafS3_of_sq c2995_s3,
   c2995_iso, leafR8_of_sq c2995_nof2 c2995_nof3 c2995_nof4z⟩
theorem not_tile'_2995 (D : CongruentDissection 2995) : False :=
  not_tile_of_conditions' 2995 C'_2995 D

private theorem c2998_sqf   : LeafSqf 2998   := by decide +kernel
private theorem c2998_range : LeafRange 2998  := by decide +kernel
private theorem c2998_ell   : LeafEll 2998    := by decide +kernel
private theorem c2998_nsq   : NSqChkSq 2998   := by decide +kernel
private theorem c2998_har   : HArithChkSq 2998 := by decide +kernel
private theorem c2998_r     : LeafR 2998      := by decide +kernel
private theorem c2998_e'    : LeafE' 2998     := by decide +kernel
private theorem c2998_f1    : LeafF1 2998     := Or.inl (by decide)
private theorem c2998_s2    : S2ChkSq 2998    := by decide +kernel
private theorem c2998_s3    : S3ChkSq 2998    := by decide +kernel
private theorem c2998_iso   : LeafIso 2998    := by decide +kernel
private theorem c2998_nof2  : NoF2ChkSq 2998  := by decide +kernel
private theorem c2998_nof3  : NoF3ChkSq 2998  := by decide +kernel
private theorem c2998_nof4z : NoF4zChkSq 2998 := by decide +kernel
theorem C'_2998 : C' 2998 :=
  ⟨c2998_sqf, c2998_range, c2998_ell, leafNSq_of_sq c2998_nsq, leafHAr_of_sq c2998_har,
   c2998_r, c2998_e', c2998_f1, leafS2_of_sq c2998_s2, leafS3_of_sq c2998_s3,
   c2998_iso, leafR8_of_sq c2998_nof2 c2998_nof3 c2998_nof4z⟩
theorem not_tile'_2998 (D : CongruentDissection 2998) : False :=
  not_tile_of_conditions' 2998 C'_2998 D

private theorem c2999_sqf   : LeafSqf 2999   := by decide +kernel
private theorem c2999_range : LeafRange 2999  := by decide +kernel
private theorem c2999_ell   : LeafEll 2999    := by decide +kernel
private theorem c2999_nsq   : NSqChkSq 2999   := by decide +kernel
private theorem c2999_har   : HArithChkSq 2999 := by decide +kernel
private theorem c2999_r     : LeafR 2999      := by decide +kernel
private theorem c2999_e'    : LeafE' 2999     := by decide +kernel
private theorem c2999_f1    : LeafF1 2999     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2999_s2    : S2ChkSq 2999    := by decide +kernel
private theorem c2999_s3    : S3ChkSq 2999    := by decide +kernel
private theorem c2999_iso   : LeafIso 2999    := by decide +kernel
private theorem c2999_nof2  : NoF2ChkSq 2999  := by decide +kernel
private theorem c2999_nof3  : NoF3ChkSq 2999  := by decide +kernel
private theorem c2999_nof4z : NoF4zChkSq 2999 := by decide +kernel
theorem C'_2999 : C' 2999 :=
  ⟨c2999_sqf, c2999_range, c2999_ell, leafNSq_of_sq c2999_nsq, leafHAr_of_sq c2999_har,
   c2999_r, c2999_e', c2999_f1, leafS2_of_sq c2999_s2, leafS3_of_sq c2999_s3,
   c2999_iso, leafR8_of_sq c2999_nof2 c2999_nof3 c2999_nof4z⟩
theorem not_tile'_2999 (D : CongruentDissection 2999) : False :=
  not_tile_of_conditions' 2999 C'_2999 D

end Erdos634.Draft.AllN2

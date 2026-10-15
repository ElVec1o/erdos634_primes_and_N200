/- AllN2Check126: N = 2946, 2947, 2949, 2951, 2954
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2946_sqf   : LeafSqf 2946   := by decide +kernel
private theorem c2946_range : LeafRange 2946  := by decide +kernel
private theorem c2946_ell   : LeafEll 2946    := by decide +kernel
private theorem c2946_nsq   : NSqChkSq 2946   := by decide +kernel
private theorem c2946_har   : HArithChkSq 2946 := by decide +kernel
private theorem c2946_r     : LeafR 2946      := by decide +kernel
private theorem c2946_e'    : LeafE' 2946     := by decide +kernel
private theorem c2946_f1    : LeafF1 2946     := Or.inl (by decide)
private theorem c2946_s2    : S2ChkSq 2946    := by decide +kernel
private theorem c2946_s3    : S3ChkSq 2946    := by decide +kernel
private theorem c2946_iso   : LeafIso 2946    := by decide +kernel
private theorem c2946_nof2  : NoF2ChkSq 2946  := by decide +kernel
private theorem c2946_nof3  : NoF3ChkSq 2946  := by decide +kernel
private theorem c2946_nof4z : NoF4zChkSq 2946 := by decide +kernel
theorem C'_2946 : C' 2946 :=
  ⟨c2946_sqf, c2946_range, c2946_ell, leafNSq_of_sq c2946_nsq, leafHAr_of_sq c2946_har,
   c2946_r, c2946_e', c2946_f1, leafS2_of_sq c2946_s2, leafS3_of_sq c2946_s3,
   c2946_iso, leafR8_of_sq c2946_nof2 c2946_nof3 c2946_nof4z⟩
theorem not_tile'_2946 (D : CongruentDissection 2946) : False :=
  not_tile_of_conditions' 2946 C'_2946 D

private theorem c2947_sqf   : LeafSqf 2947   := by decide +kernel
private theorem c2947_range : LeafRange 2947  := by decide +kernel
private theorem c2947_ell   : LeafEll 2947    := by decide +kernel
private theorem c2947_nsq   : NSqChkSq 2947   := by decide +kernel
private theorem c2947_har   : HArithChkSq 2947 := by decide +kernel
private theorem c2947_r     : LeafR 2947      := by decide +kernel
private theorem c2947_e'    : LeafE' 2947     := by decide +kernel
private theorem c2947_f1    : LeafF1 2947     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2947_s2    : S2ChkSq 2947    := by decide +kernel
private theorem c2947_s3    : S3ChkSq 2947    := by decide +kernel
private theorem c2947_iso   : LeafIso 2947    := by decide +kernel
private theorem c2947_nof2  : NoF2ChkSq 2947  := by decide +kernel
private theorem c2947_nof3  : NoF3ChkSq 2947  := by decide +kernel
private theorem c2947_nof4z : NoF4zChkSq 2947 := by decide +kernel
theorem C'_2947 : C' 2947 :=
  ⟨c2947_sqf, c2947_range, c2947_ell, leafNSq_of_sq c2947_nsq, leafHAr_of_sq c2947_har,
   c2947_r, c2947_e', c2947_f1, leafS2_of_sq c2947_s2, leafS3_of_sq c2947_s3,
   c2947_iso, leafR8_of_sq c2947_nof2 c2947_nof3 c2947_nof4z⟩
theorem not_tile'_2947 (D : CongruentDissection 2947) : False :=
  not_tile_of_conditions' 2947 C'_2947 D

private theorem c2949_sqf   : LeafSqf 2949   := by decide +kernel
private theorem c2949_range : LeafRange 2949  := by decide +kernel
private theorem c2949_ell   : LeafEll 2949    := by decide +kernel
private theorem c2949_nsq   : NSqChkSq 2949   := by decide +kernel
private theorem c2949_har   : HArithChkSq 2949 := by decide +kernel
private theorem c2949_r     : LeafR 2949      := by decide +kernel
private theorem c2949_e'    : LeafE' 2949     := by decide +kernel
private theorem c2949_f1    : LeafF1 2949     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2949_s2    : S2ChkSq 2949    := by decide +kernel
private theorem c2949_s3    : S3ChkSq 2949    := by decide +kernel
private theorem c2949_iso   : LeafIso 2949    := by decide +kernel
private theorem c2949_nof2  : NoF2ChkSq 2949  := by decide +kernel
private theorem c2949_nof3  : NoF3ChkSq 2949  := by decide +kernel
private theorem c2949_nof4z : NoF4zChkSq 2949 := by decide +kernel
theorem C'_2949 : C' 2949 :=
  ⟨c2949_sqf, c2949_range, c2949_ell, leafNSq_of_sq c2949_nsq, leafHAr_of_sq c2949_har,
   c2949_r, c2949_e', c2949_f1, leafS2_of_sq c2949_s2, leafS3_of_sq c2949_s3,
   c2949_iso, leafR8_of_sq c2949_nof2 c2949_nof3 c2949_nof4z⟩
theorem not_tile'_2949 (D : CongruentDissection 2949) : False :=
  not_tile_of_conditions' 2949 C'_2949 D

private theorem c2951_sqf   : LeafSqf 2951   := by decide +kernel
private theorem c2951_range : LeafRange 2951  := by decide +kernel
private theorem c2951_ell   : LeafEll 2951    := by decide +kernel
private theorem c2951_nsq   : NSqChkSq 2951   := by decide +kernel
private theorem c2951_har   : HArithChkSq 2951 := by decide +kernel
private theorem c2951_r     : LeafR 2951      := by decide +kernel
private theorem c2951_e'    : LeafE' 2951     := by decide +kernel
private theorem c2951_f1    : LeafF1 2951     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2951_s2    : S2ChkSq 2951    := by decide +kernel
private theorem c2951_s3    : S3ChkSq 2951    := by decide +kernel
private theorem c2951_iso   : LeafIso 2951    := by decide +kernel
private theorem c2951_nof2  : NoF2ChkSq 2951  := by decide +kernel
private theorem c2951_nof3  : NoF3ChkSq 2951  := by decide +kernel
private theorem c2951_nof4z : NoF4zChkSq 2951 := by decide +kernel
theorem C'_2951 : C' 2951 :=
  ⟨c2951_sqf, c2951_range, c2951_ell, leafNSq_of_sq c2951_nsq, leafHAr_of_sq c2951_har,
   c2951_r, c2951_e', c2951_f1, leafS2_of_sq c2951_s2, leafS3_of_sq c2951_s3,
   c2951_iso, leafR8_of_sq c2951_nof2 c2951_nof3 c2951_nof4z⟩
theorem not_tile'_2951 (D : CongruentDissection 2951) : False :=
  not_tile_of_conditions' 2951 C'_2951 D

private theorem c2954_sqf   : LeafSqf 2954   := by decide +kernel
private theorem c2954_range : LeafRange 2954  := by decide +kernel
private theorem c2954_ell   : LeafEll 2954    := by decide +kernel
private theorem c2954_nsq   : NSqChkSq 2954   := by decide +kernel
private theorem c2954_har   : HArithChkSq 2954 := by decide +kernel
private theorem c2954_r     : LeafR 2954      := by decide +kernel
private theorem c2954_e'    : LeafE' 2954     := by decide +kernel
private theorem c2954_f1    : LeafF1 2954     := Or.inl (by decide)
private theorem c2954_s2    : S2ChkSq 2954    := by decide +kernel
private theorem c2954_s3    : S3ChkSq 2954    := by decide +kernel
private theorem c2954_iso   : LeafIso 2954    := by decide +kernel
private theorem c2954_nof2  : NoF2ChkSq 2954  := by decide +kernel
private theorem c2954_nof3  : NoF3ChkSq 2954  := by decide +kernel
private theorem c2954_nof4z : NoF4zChkSq 2954 := by decide +kernel
theorem C'_2954 : C' 2954 :=
  ⟨c2954_sqf, c2954_range, c2954_ell, leafNSq_of_sq c2954_nsq, leafHAr_of_sq c2954_har,
   c2954_r, c2954_e', c2954_f1, leafS2_of_sq c2954_s2, leafS3_of_sq c2954_s3,
   c2954_iso, leafR8_of_sq c2954_nof2 c2954_nof3 c2954_nof4z⟩
theorem not_tile'_2954 (D : CongruentDissection 2954) : False :=
  not_tile_of_conditions' 2954 C'_2954 D

end Erdos634.Draft.AllN2

/- AllN2Check203: N = 3943, 3947, 3949, 3953, 3954
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3943_sqf   : LeafSqf 3943   := by decide +kernel
private theorem c3943_range : LeafRange 3943  := by decide +kernel
private theorem c3943_ell   : LeafEll 3943    := by decide +kernel
private theorem c3943_nsq   : NSqChkSq 3943   := by decide +kernel
private theorem c3943_har   : HArithChkSq 3943 := by decide +kernel
private theorem c3943_r     : LeafR 3943      := by decide +kernel
private theorem c3943_e'    : LeafE' 3943     := by decide +kernel
private theorem c3943_f1    : LeafF1 3943     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3943_s2    : S2ChkSq 3943    := by decide +kernel
private theorem c3943_s3    : S3ChkSq 3943    := by decide +kernel
private theorem c3943_iso   : LeafIso 3943    := by decide +kernel
private theorem c3943_nof2  : NoF2ChkSq 3943  := by decide +kernel
private theorem c3943_nof3  : NoF3ChkSq 3943  := by decide +kernel
private theorem c3943_nof4z : NoF4zChkSq 3943 := by decide +kernel
theorem C'_3943 : C' 3943 :=
  ⟨c3943_sqf, c3943_range, c3943_ell, leafNSq_of_sq c3943_nsq, leafHAr_of_sq c3943_har,
   c3943_r, c3943_e', c3943_f1, leafS2_of_sq c3943_s2, leafS3_of_sq c3943_s3,
   c3943_iso, leafR8_of_sq c3943_nof2 c3943_nof3 c3943_nof4z⟩
theorem not_tile'_3943 (D : CongruentDissection 3943) : False :=
  not_tile_of_conditions' 3943 C'_3943 D

private theorem c3947_sqf   : LeafSqf 3947   := by decide +kernel
private theorem c3947_range : LeafRange 3947  := by decide +kernel
private theorem c3947_ell   : LeafEll 3947    := by decide +kernel
private theorem c3947_nsq   : NSqChkSq 3947   := by decide +kernel
private theorem c3947_har   : HArithChkSq 3947 := by decide +kernel
private theorem c3947_r     : LeafR 3947      := by decide +kernel
private theorem c3947_e'    : LeafE' 3947     := by decide +kernel
private theorem c3947_f1    : LeafF1 3947     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3947_s2    : S2ChkSq 3947    := by decide +kernel
private theorem c3947_s3    : S3ChkSq 3947    := by decide +kernel
private theorem c3947_iso   : LeafIso 3947    := by decide +kernel
private theorem c3947_nof2  : NoF2ChkSq 3947  := by decide +kernel
private theorem c3947_nof3  : NoF3ChkSq 3947  := by decide +kernel
private theorem c3947_nof4z : NoF4zChkSq 3947 := by decide +kernel
theorem C'_3947 : C' 3947 :=
  ⟨c3947_sqf, c3947_range, c3947_ell, leafNSq_of_sq c3947_nsq, leafHAr_of_sq c3947_har,
   c3947_r, c3947_e', c3947_f1, leafS2_of_sq c3947_s2, leafS3_of_sq c3947_s3,
   c3947_iso, leafR8_of_sq c3947_nof2 c3947_nof3 c3947_nof4z⟩
theorem not_tile'_3947 (D : CongruentDissection 3947) : False :=
  not_tile_of_conditions' 3947 C'_3947 D

private theorem c3949_sqf   : LeafSqf 3949   := by decide +kernel
private theorem c3949_range : LeafRange 3949  := by decide +kernel
private theorem c3949_ell   : LeafEll 3949    := by decide +kernel
private theorem c3949_nsq   : NSqChkSq 3949   := by decide +kernel
private theorem c3949_har   : HArithChkSq 3949 := by decide +kernel
private theorem c3949_r     : LeafR 3949      := by decide +kernel
private theorem c3949_e'    : LeafE' 3949     := by decide +kernel
private theorem c3949_f1    : LeafF1 3949     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3949_s2    : S2ChkSq 3949    := by decide +kernel
private theorem c3949_s3    : S3ChkSq 3949    := by decide +kernel
private theorem c3949_iso   : LeafIso 3949    := by decide +kernel
private theorem c3949_nof2  : NoF2ChkSq 3949  := by decide +kernel
private theorem c3949_nof3  : NoF3ChkSq 3949  := by decide +kernel
private theorem c3949_nof4z : NoF4zChkSq 3949 := by decide +kernel
theorem C'_3949 : C' 3949 :=
  ⟨c3949_sqf, c3949_range, c3949_ell, leafNSq_of_sq c3949_nsq, leafHAr_of_sq c3949_har,
   c3949_r, c3949_e', c3949_f1, leafS2_of_sq c3949_s2, leafS3_of_sq c3949_s3,
   c3949_iso, leafR8_of_sq c3949_nof2 c3949_nof3 c3949_nof4z⟩
theorem not_tile'_3949 (D : CongruentDissection 3949) : False :=
  not_tile_of_conditions' 3949 C'_3949 D

private theorem c3953_sqf   : LeafSqf 3953   := by decide +kernel
private theorem c3953_range : LeafRange 3953  := by decide +kernel
private theorem c3953_ell   : LeafEll 3953    := by decide +kernel
private theorem c3953_nsq   : NSqChkSq 3953   := by decide +kernel
private theorem c3953_har   : HArithChkSq 3953 := by decide +kernel
private theorem c3953_r     : LeafR 3953      := by decide +kernel
private theorem c3953_e'    : LeafE' 3953     := by decide +kernel
private theorem c3953_f1    : LeafF1 3953     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3953_s2    : S2ChkSq 3953    := by decide +kernel
private theorem c3953_s3    : S3ChkSq 3953    := by decide +kernel
private theorem c3953_iso   : LeafIso 3953    := by decide +kernel
private theorem c3953_nof2  : NoF2ChkSq 3953  := by decide +kernel
private theorem c3953_nof3  : NoF3ChkSq 3953  := by decide +kernel
private theorem c3953_nof4z : NoF4zChkSq 3953 := by decide +kernel
theorem C'_3953 : C' 3953 :=
  ⟨c3953_sqf, c3953_range, c3953_ell, leafNSq_of_sq c3953_nsq, leafHAr_of_sq c3953_har,
   c3953_r, c3953_e', c3953_f1, leafS2_of_sq c3953_s2, leafS3_of_sq c3953_s3,
   c3953_iso, leafR8_of_sq c3953_nof2 c3953_nof3 c3953_nof4z⟩
theorem not_tile'_3953 (D : CongruentDissection 3953) : False :=
  not_tile_of_conditions' 3953 C'_3953 D

private theorem c3954_sqf   : LeafSqf 3954   := by decide +kernel
private theorem c3954_range : LeafRange 3954  := by decide +kernel
private theorem c3954_ell   : LeafEll 3954    := by decide +kernel
private theorem c3954_nsq   : NSqChkSq 3954   := by decide +kernel
private theorem c3954_har   : HArithChkSq 3954 := by decide +kernel
private theorem c3954_r     : LeafR 3954      := by decide +kernel
private theorem c3954_e'    : LeafE' 3954     := by decide +kernel
private theorem c3954_f1    : LeafF1 3954     := Or.inl (by decide)
private theorem c3954_s2    : S2ChkSq 3954    := by decide +kernel
private theorem c3954_s3    : S3ChkSq 3954    := by decide +kernel
private theorem c3954_iso   : LeafIso 3954    := by decide +kernel
private theorem c3954_nof2  : NoF2ChkSq 3954  := by decide +kernel
private theorem c3954_nof3  : NoF3ChkSq 3954  := by decide +kernel
private theorem c3954_nof4z : NoF4zChkSq 3954 := by decide +kernel
theorem C'_3954 : C' 3954 :=
  ⟨c3954_sqf, c3954_range, c3954_ell, leafNSq_of_sq c3954_nsq, leafHAr_of_sq c3954_har,
   c3954_r, c3954_e', c3954_f1, leafS2_of_sq c3954_s2, leafS3_of_sq c3954_s3,
   c3954_iso, leafR8_of_sq c3954_nof2 c3954_nof3 c3954_nof4z⟩
theorem not_tile'_3954 (D : CongruentDissection 3954) : False :=
  not_tile_of_conditions' 3954 C'_3954 D

end Erdos634.Draft.AllN2

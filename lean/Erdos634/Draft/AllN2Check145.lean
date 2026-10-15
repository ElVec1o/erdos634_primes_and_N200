/- AllN2Check145: N = 3183, 3187, 3189, 3190, 3191
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3183_sqf   : LeafSqf 3183   := by decide +kernel
private theorem c3183_range : LeafRange 3183  := by decide +kernel
private theorem c3183_ell   : LeafEll 3183    := by decide +kernel
private theorem c3183_nsq   : NSqChkSq 3183   := by decide +kernel
private theorem c3183_har   : HArithChkSq 3183 := by decide +kernel
private theorem c3183_r     : LeafR 3183      := by decide +kernel
private theorem c3183_e'    : LeafE' 3183     := by decide +kernel
private theorem c3183_f1    : LeafF1 3183     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3183_s2    : S2ChkSq 3183    := by decide +kernel
private theorem c3183_s3    : S3ChkSq 3183    := by decide +kernel
private theorem c3183_iso   : LeafIso 3183    := by decide +kernel
private theorem c3183_nof2  : NoF2ChkSq 3183  := by decide +kernel
private theorem c3183_nof3  : NoF3ChkSq 3183  := by decide +kernel
private theorem c3183_nof4z : NoF4zChkSq 3183 := by decide +kernel
theorem C'_3183 : C' 3183 :=
  ⟨c3183_sqf, c3183_range, c3183_ell, leafNSq_of_sq c3183_nsq, leafHAr_of_sq c3183_har,
   c3183_r, c3183_e', c3183_f1, leafS2_of_sq c3183_s2, leafS3_of_sq c3183_s3,
   c3183_iso, leafR8_of_sq c3183_nof2 c3183_nof3 c3183_nof4z⟩
theorem not_tile'_3183 (D : CongruentDissection 3183) : False :=
  not_tile_of_conditions' 3183 C'_3183 D

private theorem c3187_sqf   : LeafSqf 3187   := by decide +kernel
private theorem c3187_range : LeafRange 3187  := by decide +kernel
private theorem c3187_ell   : LeafEll 3187    := by decide +kernel
private theorem c3187_nsq   : NSqChkSq 3187   := by decide +kernel
private theorem c3187_har   : HArithChkSq 3187 := by decide +kernel
private theorem c3187_r     : LeafR 3187      := by decide +kernel
private theorem c3187_e'    : LeafE' 3187     := by decide +kernel
private theorem c3187_f1    : LeafF1 3187     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3187_s2    : S2ChkSq 3187    := by decide +kernel
private theorem c3187_s3    : S3ChkSq 3187    := by decide +kernel
private theorem c3187_iso   : LeafIso 3187    := by decide +kernel
private theorem c3187_nof2  : NoF2ChkSq 3187  := by decide +kernel
private theorem c3187_nof3  : NoF3ChkSq 3187  := by decide +kernel
private theorem c3187_nof4z : NoF4zChkSq 3187 := by decide +kernel
theorem C'_3187 : C' 3187 :=
  ⟨c3187_sqf, c3187_range, c3187_ell, leafNSq_of_sq c3187_nsq, leafHAr_of_sq c3187_har,
   c3187_r, c3187_e', c3187_f1, leafS2_of_sq c3187_s2, leafS3_of_sq c3187_s3,
   c3187_iso, leafR8_of_sq c3187_nof2 c3187_nof3 c3187_nof4z⟩
theorem not_tile'_3187 (D : CongruentDissection 3187) : False :=
  not_tile_of_conditions' 3187 C'_3187 D

private theorem c3189_sqf   : LeafSqf 3189   := by decide +kernel
private theorem c3189_range : LeafRange 3189  := by decide +kernel
private theorem c3189_ell   : LeafEll 3189    := by decide +kernel
private theorem c3189_nsq   : NSqChkSq 3189   := by decide +kernel
private theorem c3189_har   : HArithChkSq 3189 := by decide +kernel
private theorem c3189_r     : LeafR 3189      := by decide +kernel
private theorem c3189_e'    : LeafE' 3189     := by decide +kernel
private theorem c3189_f1    : LeafF1 3189     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3189_s2    : S2ChkSq 3189    := by decide +kernel
private theorem c3189_s3    : S3ChkSq 3189    := by decide +kernel
private theorem c3189_iso   : LeafIso 3189    := by decide +kernel
private theorem c3189_nof2  : NoF2ChkSq 3189  := by decide +kernel
private theorem c3189_nof3  : NoF3ChkSq 3189  := by decide +kernel
private theorem c3189_nof4z : NoF4zChkSq 3189 := by decide +kernel
theorem C'_3189 : C' 3189 :=
  ⟨c3189_sqf, c3189_range, c3189_ell, leafNSq_of_sq c3189_nsq, leafHAr_of_sq c3189_har,
   c3189_r, c3189_e', c3189_f1, leafS2_of_sq c3189_s2, leafS3_of_sq c3189_s3,
   c3189_iso, leafR8_of_sq c3189_nof2 c3189_nof3 c3189_nof4z⟩
theorem not_tile'_3189 (D : CongruentDissection 3189) : False :=
  not_tile_of_conditions' 3189 C'_3189 D

private theorem c3190_sqf   : LeafSqf 3190   := by decide +kernel
private theorem c3190_range : LeafRange 3190  := by decide +kernel
private theorem c3190_ell   : LeafEll 3190    := by decide +kernel
private theorem c3190_nsq   : NSqChkSq 3190   := by decide +kernel
private theorem c3190_har   : HArithChkSq 3190 := by decide +kernel
private theorem c3190_r     : LeafR 3190      := by decide +kernel
private theorem c3190_e'    : LeafE' 3190     := by decide +kernel
private theorem c3190_f1    : LeafF1 3190     := Or.inl (by decide)
private theorem c3190_s2    : S2ChkSq 3190    := by decide +kernel
private theorem c3190_s3    : S3ChkSq 3190    := by decide +kernel
private theorem c3190_iso   : LeafIso 3190    := by decide +kernel
private theorem c3190_nof2  : NoF2ChkSq 3190  := by decide +kernel
private theorem c3190_nof3  : NoF3ChkSq 3190  := by decide +kernel
private theorem c3190_nof4z : NoF4zChkSq 3190 := by decide +kernel
theorem C'_3190 : C' 3190 :=
  ⟨c3190_sqf, c3190_range, c3190_ell, leafNSq_of_sq c3190_nsq, leafHAr_of_sq c3190_har,
   c3190_r, c3190_e', c3190_f1, leafS2_of_sq c3190_s2, leafS3_of_sq c3190_s3,
   c3190_iso, leafR8_of_sq c3190_nof2 c3190_nof3 c3190_nof4z⟩
theorem not_tile'_3190 (D : CongruentDissection 3190) : False :=
  not_tile_of_conditions' 3190 C'_3190 D

private theorem c3191_sqf   : LeafSqf 3191   := by decide +kernel
private theorem c3191_range : LeafRange 3191  := by decide +kernel
private theorem c3191_ell   : LeafEll 3191    := by decide +kernel
private theorem c3191_nsq   : NSqChkSq 3191   := by decide +kernel
private theorem c3191_har   : HArithChkSq 3191 := by decide +kernel
private theorem c3191_r     : LeafR 3191      := by decide +kernel
private theorem c3191_e'    : LeafE' 3191     := by decide +kernel
private theorem c3191_f1    : LeafF1 3191     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3191_s2    : S2ChkSq 3191    := by decide +kernel
private theorem c3191_s3    : S3ChkSq 3191    := by decide +kernel
private theorem c3191_iso   : LeafIso 3191    := by decide +kernel
private theorem c3191_nof2  : NoF2ChkSq 3191  := by decide +kernel
private theorem c3191_nof3  : NoF3ChkSq 3191  := by decide +kernel
private theorem c3191_nof4z : NoF4zChkSq 3191 := by decide +kernel
theorem C'_3191 : C' 3191 :=
  ⟨c3191_sqf, c3191_range, c3191_ell, leafNSq_of_sq c3191_nsq, leafHAr_of_sq c3191_har,
   c3191_r, c3191_e', c3191_f1, leafS2_of_sq c3191_s2, leafS3_of_sq c3191_s3,
   c3191_iso, leafR8_of_sq c3191_nof2 c3191_nof3 c3191_nof4z⟩
theorem not_tile'_3191 (D : CongruentDissection 3191) : False :=
  not_tile_of_conditions' 3191 C'_3191 D

end Erdos634.Draft.AllN2

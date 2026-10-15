/- AllN2Check69: N = 2219, 2222, 2226, 2227, 2229
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2219_sqf   : LeafSqf 2219   := by decide +kernel
private theorem c2219_range : LeafRange 2219  := by decide +kernel
private theorem c2219_ell   : LeafEll 2219    := by decide +kernel
private theorem c2219_nsq   : NSqChkSq 2219   := by decide +kernel
private theorem c2219_har   : HArithChkSq 2219 := by decide +kernel
private theorem c2219_r     : LeafR 2219      := by decide +kernel
private theorem c2219_e'    : LeafE' 2219     := by decide +kernel
private theorem c2219_f1    : LeafF1 2219     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2219_s2    : S2ChkSq 2219    := by decide +kernel
private theorem c2219_s3    : S3ChkSq 2219    := by decide +kernel
private theorem c2219_iso   : LeafIso 2219    := by decide +kernel
private theorem c2219_nof2  : NoF2ChkSq 2219  := by decide +kernel
private theorem c2219_nof3  : NoF3ChkSq 2219  := by decide +kernel
private theorem c2219_nof4z : NoF4zChkSq 2219 := by decide +kernel
theorem C'_2219 : C' 2219 :=
  ⟨c2219_sqf, c2219_range, c2219_ell, leafNSq_of_sq c2219_nsq, leafHAr_of_sq c2219_har,
   c2219_r, c2219_e', c2219_f1, leafS2_of_sq c2219_s2, leafS3_of_sq c2219_s3,
   c2219_iso, leafR8_of_sq c2219_nof2 c2219_nof3 c2219_nof4z⟩
theorem not_tile'_2219 (D : CongruentDissection 2219) : False :=
  not_tile_of_conditions' 2219 C'_2219 D

private theorem c2222_sqf   : LeafSqf 2222   := by decide +kernel
private theorem c2222_range : LeafRange 2222  := by decide +kernel
private theorem c2222_ell   : LeafEll 2222    := by decide +kernel
private theorem c2222_nsq   : NSqChkSq 2222   := by decide +kernel
private theorem c2222_har   : HArithChkSq 2222 := by decide +kernel
private theorem c2222_r     : LeafR 2222      := by decide +kernel
private theorem c2222_e'    : LeafE' 2222     := by decide +kernel
private theorem c2222_f1    : LeafF1 2222     := Or.inl (by decide)
private theorem c2222_s2    : S2ChkSq 2222    := by decide +kernel
private theorem c2222_s3    : S3ChkSq 2222    := by decide +kernel
private theorem c2222_iso   : LeafIso 2222    := by decide +kernel
private theorem c2222_nof2  : NoF2ChkSq 2222  := by decide +kernel
private theorem c2222_nof3  : NoF3ChkSq 2222  := by decide +kernel
private theorem c2222_nof4z : NoF4zChkSq 2222 := by decide +kernel
theorem C'_2222 : C' 2222 :=
  ⟨c2222_sqf, c2222_range, c2222_ell, leafNSq_of_sq c2222_nsq, leafHAr_of_sq c2222_har,
   c2222_r, c2222_e', c2222_f1, leafS2_of_sq c2222_s2, leafS3_of_sq c2222_s3,
   c2222_iso, leafR8_of_sq c2222_nof2 c2222_nof3 c2222_nof4z⟩
theorem not_tile'_2222 (D : CongruentDissection 2222) : False :=
  not_tile_of_conditions' 2222 C'_2222 D

private theorem c2226_sqf   : LeafSqf 2226   := by decide +kernel
private theorem c2226_range : LeafRange 2226  := by decide +kernel
private theorem c2226_ell   : LeafEll 2226    := by decide +kernel
private theorem c2226_nsq   : NSqChkSq 2226   := by decide +kernel
private theorem c2226_har   : HArithChkSq 2226 := by decide +kernel
private theorem c2226_r     : LeafR 2226      := by decide +kernel
private theorem c2226_e'    : LeafE' 2226     := by decide +kernel
private theorem c2226_f1    : LeafF1 2226     := Or.inl (by decide)
private theorem c2226_s2    : S2ChkSq 2226    := by decide +kernel
private theorem c2226_s3    : S3ChkSq 2226    := by decide +kernel
private theorem c2226_iso   : LeafIso 2226    := by decide +kernel
private theorem c2226_nof2  : NoF2ChkSq 2226  := by decide +kernel
private theorem c2226_nof3  : NoF3ChkSq 2226  := by decide +kernel
private theorem c2226_nof4z : NoF4zChkSq 2226 := by decide +kernel
theorem C'_2226 : C' 2226 :=
  ⟨c2226_sqf, c2226_range, c2226_ell, leafNSq_of_sq c2226_nsq, leafHAr_of_sq c2226_har,
   c2226_r, c2226_e', c2226_f1, leafS2_of_sq c2226_s2, leafS3_of_sq c2226_s3,
   c2226_iso, leafR8_of_sq c2226_nof2 c2226_nof3 c2226_nof4z⟩
theorem not_tile'_2226 (D : CongruentDissection 2226) : False :=
  not_tile_of_conditions' 2226 C'_2226 D

private theorem c2227_sqf   : LeafSqf 2227   := by decide +kernel
private theorem c2227_range : LeafRange 2227  := by decide +kernel
private theorem c2227_ell   : LeafEll 2227    := by decide +kernel
private theorem c2227_nsq   : NSqChkSq 2227   := by decide +kernel
private theorem c2227_har   : HArithChkSq 2227 := by decide +kernel
private theorem c2227_r     : LeafR 2227      := by decide +kernel
private theorem c2227_e'    : LeafE' 2227     := by decide +kernel
private theorem c2227_f1    : LeafF1 2227     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2227_s2    : S2ChkSq 2227    := by decide +kernel
private theorem c2227_s3    : S3ChkSq 2227    := by decide +kernel
private theorem c2227_iso   : LeafIso 2227    := by decide +kernel
private theorem c2227_nof2  : NoF2ChkSq 2227  := by decide +kernel
private theorem c2227_nof3  : NoF3ChkSq 2227  := by decide +kernel
private theorem c2227_nof4z : NoF4zChkSq 2227 := by decide +kernel
theorem C'_2227 : C' 2227 :=
  ⟨c2227_sqf, c2227_range, c2227_ell, leafNSq_of_sq c2227_nsq, leafHAr_of_sq c2227_har,
   c2227_r, c2227_e', c2227_f1, leafS2_of_sq c2227_s2, leafS3_of_sq c2227_s3,
   c2227_iso, leafR8_of_sq c2227_nof2 c2227_nof3 c2227_nof4z⟩
theorem not_tile'_2227 (D : CongruentDissection 2227) : False :=
  not_tile_of_conditions' 2227 C'_2227 D

private theorem c2229_sqf   : LeafSqf 2229   := by decide +kernel
private theorem c2229_range : LeafRange 2229  := by decide +kernel
private theorem c2229_ell   : LeafEll 2229    := by decide +kernel
private theorem c2229_nsq   : NSqChkSq 2229   := by decide +kernel
private theorem c2229_har   : HArithChkSq 2229 := by decide +kernel
private theorem c2229_r     : LeafR 2229      := by decide +kernel
private theorem c2229_e'    : LeafE' 2229     := by decide +kernel
private theorem c2229_f1    : LeafF1 2229     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2229_s2    : S2ChkSq 2229    := by decide +kernel
private theorem c2229_s3    : S3ChkSq 2229    := by decide +kernel
private theorem c2229_iso   : LeafIso 2229    := by decide +kernel
private theorem c2229_nof2  : NoF2ChkSq 2229  := by decide +kernel
private theorem c2229_nof3  : NoF3ChkSq 2229  := by decide +kernel
private theorem c2229_nof4z : NoF4zChkSq 2229 := by decide +kernel
theorem C'_2229 : C' 2229 :=
  ⟨c2229_sqf, c2229_range, c2229_ell, leafNSq_of_sq c2229_nsq, leafHAr_of_sq c2229_har,
   c2229_r, c2229_e', c2229_f1, leafS2_of_sq c2229_s2, leafS3_of_sq c2229_s3,
   c2229_iso, leafR8_of_sq c2229_nof2 c2229_nof3 c2229_nof4z⟩
theorem not_tile'_2229 (D : CongruentDissection 2229) : False :=
  not_tile_of_conditions' 2229 C'_2229 D

end Erdos634.Draft.AllN2

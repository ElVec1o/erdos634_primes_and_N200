/- AllN2Check118: N = 2843, 2846, 2849, 2851, 2854
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2843_sqf   : LeafSqf 2843   := by decide +kernel
private theorem c2843_range : LeafRange 2843  := by decide +kernel
private theorem c2843_ell   : LeafEll 2843    := by decide +kernel
private theorem c2843_nsq   : NSqChkSq 2843   := by decide +kernel
private theorem c2843_har   : HArithChkSq 2843 := by decide +kernel
private theorem c2843_r     : LeafR 2843      := by decide +kernel
private theorem c2843_e'    : LeafE' 2843     := by decide +kernel
private theorem c2843_f1    : LeafF1 2843     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2843_s2    : S2ChkSq 2843    := by decide +kernel
private theorem c2843_s3    : S3ChkSq 2843    := by decide +kernel
private theorem c2843_iso   : LeafIso 2843    := by decide +kernel
private theorem c2843_nof2  : NoF2ChkSq 2843  := by decide +kernel
private theorem c2843_nof3  : NoF3ChkSq 2843  := by decide +kernel
private theorem c2843_nof4z : NoF4zChkSq 2843 := by decide +kernel
theorem C'_2843 : C' 2843 :=
  ⟨c2843_sqf, c2843_range, c2843_ell, leafNSq_of_sq c2843_nsq, leafHAr_of_sq c2843_har,
   c2843_r, c2843_e', c2843_f1, leafS2_of_sq c2843_s2, leafS3_of_sq c2843_s3,
   c2843_iso, leafR8_of_sq c2843_nof2 c2843_nof3 c2843_nof4z⟩
theorem not_tile'_2843 (D : CongruentDissection 2843) : False :=
  not_tile_of_conditions' 2843 C'_2843 D

private theorem c2846_sqf   : LeafSqf 2846   := by decide +kernel
private theorem c2846_range : LeafRange 2846  := by decide +kernel
private theorem c2846_ell   : LeafEll 2846    := by decide +kernel
private theorem c2846_nsq   : NSqChkSq 2846   := by decide +kernel
private theorem c2846_har   : HArithChkSq 2846 := by decide +kernel
private theorem c2846_r     : LeafR 2846      := by decide +kernel
private theorem c2846_e'    : LeafE' 2846     := by decide +kernel
private theorem c2846_f1    : LeafF1 2846     := Or.inl (by decide)
private theorem c2846_s2    : S2ChkSq 2846    := by decide +kernel
private theorem c2846_s3    : S3ChkSq 2846    := by decide +kernel
private theorem c2846_iso   : LeafIso 2846    := by decide +kernel
private theorem c2846_nof2  : NoF2ChkSq 2846  := by decide +kernel
private theorem c2846_nof3  : NoF3ChkSq 2846  := by decide +kernel
private theorem c2846_nof4z : NoF4zChkSq 2846 := by decide +kernel
theorem C'_2846 : C' 2846 :=
  ⟨c2846_sqf, c2846_range, c2846_ell, leafNSq_of_sq c2846_nsq, leafHAr_of_sq c2846_har,
   c2846_r, c2846_e', c2846_f1, leafS2_of_sq c2846_s2, leafS3_of_sq c2846_s3,
   c2846_iso, leafR8_of_sq c2846_nof2 c2846_nof3 c2846_nof4z⟩
theorem not_tile'_2846 (D : CongruentDissection 2846) : False :=
  not_tile_of_conditions' 2846 C'_2846 D

private theorem c2849_sqf   : LeafSqf 2849   := by decide +kernel
private theorem c2849_range : LeafRange 2849  := by decide +kernel
private theorem c2849_ell   : LeafEll 2849    := by decide +kernel
private theorem c2849_nsq   : NSqChkSq 2849   := by decide +kernel
private theorem c2849_har   : HArithChkSq 2849 := by decide +kernel
private theorem c2849_r     : LeafR 2849      := by decide +kernel
private theorem c2849_e'    : LeafE' 2849     := by decide +kernel
private theorem c2849_f1    : LeafF1 2849     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2849_s2    : S2ChkSq 2849    := by decide +kernel
private theorem c2849_s3    : S3ChkSq 2849    := by decide +kernel
private theorem c2849_iso   : LeafIso 2849    := by decide +kernel
private theorem c2849_nof2  : NoF2ChkSq 2849  := by decide +kernel
private theorem c2849_nof3  : NoF3ChkSq 2849  := by decide +kernel
private theorem c2849_nof4z : NoF4zChkSq 2849 := by decide +kernel
theorem C'_2849 : C' 2849 :=
  ⟨c2849_sqf, c2849_range, c2849_ell, leafNSq_of_sq c2849_nsq, leafHAr_of_sq c2849_har,
   c2849_r, c2849_e', c2849_f1, leafS2_of_sq c2849_s2, leafS3_of_sq c2849_s3,
   c2849_iso, leafR8_of_sq c2849_nof2 c2849_nof3 c2849_nof4z⟩
theorem not_tile'_2849 (D : CongruentDissection 2849) : False :=
  not_tile_of_conditions' 2849 C'_2849 D

private theorem c2851_sqf   : LeafSqf 2851   := by decide +kernel
private theorem c2851_range : LeafRange 2851  := by decide +kernel
private theorem c2851_ell   : LeafEll 2851    := by decide +kernel
private theorem c2851_nsq   : NSqChkSq 2851   := by decide +kernel
private theorem c2851_har   : HArithChkSq 2851 := by decide +kernel
private theorem c2851_r     : LeafR 2851      := by decide +kernel
private theorem c2851_e'    : LeafE' 2851     := by decide +kernel
private theorem c2851_f1    : LeafF1 2851     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2851_s2    : S2ChkSq 2851    := by decide +kernel
private theorem c2851_s3    : S3ChkSq 2851    := by decide +kernel
private theorem c2851_iso   : LeafIso 2851    := by decide +kernel
private theorem c2851_nof2  : NoF2ChkSq 2851  := by decide +kernel
private theorem c2851_nof3  : NoF3ChkSq 2851  := by decide +kernel
private theorem c2851_nof4z : NoF4zChkSq 2851 := by decide +kernel
theorem C'_2851 : C' 2851 :=
  ⟨c2851_sqf, c2851_range, c2851_ell, leafNSq_of_sq c2851_nsq, leafHAr_of_sq c2851_har,
   c2851_r, c2851_e', c2851_f1, leafS2_of_sq c2851_s2, leafS3_of_sq c2851_s3,
   c2851_iso, leafR8_of_sq c2851_nof2 c2851_nof3 c2851_nof4z⟩
theorem not_tile'_2851 (D : CongruentDissection 2851) : False :=
  not_tile_of_conditions' 2851 C'_2851 D

private theorem c2854_sqf   : LeafSqf 2854   := by decide +kernel
private theorem c2854_range : LeafRange 2854  := by decide +kernel
private theorem c2854_ell   : LeafEll 2854    := by decide +kernel
private theorem c2854_nsq   : NSqChkSq 2854   := by decide +kernel
private theorem c2854_har   : HArithChkSq 2854 := by decide +kernel
private theorem c2854_r     : LeafR 2854      := by decide +kernel
private theorem c2854_e'    : LeafE' 2854     := by decide +kernel
private theorem c2854_f1    : LeafF1 2854     := Or.inl (by decide)
private theorem c2854_s2    : S2ChkSq 2854    := by decide +kernel
private theorem c2854_s3    : S3ChkSq 2854    := by decide +kernel
private theorem c2854_iso   : LeafIso 2854    := by decide +kernel
private theorem c2854_nof2  : NoF2ChkSq 2854  := by decide +kernel
private theorem c2854_nof3  : NoF3ChkSq 2854  := by decide +kernel
private theorem c2854_nof4z : NoF4zChkSq 2854 := by decide +kernel
theorem C'_2854 : C' 2854 :=
  ⟨c2854_sqf, c2854_range, c2854_ell, leafNSq_of_sq c2854_nsq, leafHAr_of_sq c2854_har,
   c2854_r, c2854_e', c2854_f1, leafS2_of_sq c2854_s2, leafS3_of_sq c2854_s3,
   c2854_iso, leafR8_of_sq c2854_nof2 c2854_nof3 c2854_nof4z⟩
theorem not_tile'_2854 (D : CongruentDissection 2854) : False :=
  not_tile_of_conditions' 2854 C'_2854 D

end Erdos634.Draft.AllN2

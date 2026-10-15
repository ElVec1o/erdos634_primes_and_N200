/- AllN2Check196: N = 3854, 3857, 3858, 3859, 3862
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3854_sqf   : LeafSqf 3854   := by decide +kernel
private theorem c3854_range : LeafRange 3854  := by decide +kernel
private theorem c3854_ell   : LeafEll 3854    := by decide +kernel
private theorem c3854_nsq   : NSqChkSq 3854   := by decide +kernel
private theorem c3854_har   : HArithChkSq 3854 := by decide +kernel
private theorem c3854_r     : LeafR 3854      := by decide +kernel
private theorem c3854_e'    : LeafE' 3854     := by decide +kernel
private theorem c3854_f1    : LeafF1 3854     := Or.inl (by decide)
private theorem c3854_s2    : S2ChkSq 3854    := by decide +kernel
private theorem c3854_s3    : S3ChkSq 3854    := by decide +kernel
private theorem c3854_iso   : LeafIso 3854    := by decide +kernel
private theorem c3854_nof2  : NoF2ChkSq 3854  := by decide +kernel
private theorem c3854_nof3  : NoF3ChkSq 3854  := by decide +kernel
private theorem c3854_nof4z : NoF4zChkSq 3854 := by decide +kernel
theorem C'_3854 : C' 3854 :=
  ⟨c3854_sqf, c3854_range, c3854_ell, leafNSq_of_sq c3854_nsq, leafHAr_of_sq c3854_har,
   c3854_r, c3854_e', c3854_f1, leafS2_of_sq c3854_s2, leafS3_of_sq c3854_s3,
   c3854_iso, leafR8_of_sq c3854_nof2 c3854_nof3 c3854_nof4z⟩
theorem not_tile'_3854 (D : CongruentDissection 3854) : False :=
  not_tile_of_conditions' 3854 C'_3854 D

private theorem c3857_sqf   : LeafSqf 3857   := by decide +kernel
private theorem c3857_range : LeafRange 3857  := by decide +kernel
private theorem c3857_ell   : LeafEll 3857    := by decide +kernel
private theorem c3857_nsq   : NSqChkSq 3857   := by decide +kernel
private theorem c3857_har   : HArithChkSq 3857 := by decide +kernel
private theorem c3857_r     : LeafR 3857      := by decide +kernel
private theorem c3857_e'    : LeafE' 3857     := by decide +kernel
private theorem c3857_f1    : LeafF1 3857     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3857_s2    : S2ChkSq 3857    := by decide +kernel
private theorem c3857_s3    : S3ChkSq 3857    := by decide +kernel
private theorem c3857_iso   : LeafIso 3857    := by decide +kernel
private theorem c3857_nof2  : NoF2ChkSq 3857  := by decide +kernel
private theorem c3857_nof3  : NoF3ChkSq 3857  := by decide +kernel
private theorem c3857_nof4z : NoF4zChkSq 3857 := by decide +kernel
theorem C'_3857 : C' 3857 :=
  ⟨c3857_sqf, c3857_range, c3857_ell, leafNSq_of_sq c3857_nsq, leafHAr_of_sq c3857_har,
   c3857_r, c3857_e', c3857_f1, leafS2_of_sq c3857_s2, leafS3_of_sq c3857_s3,
   c3857_iso, leafR8_of_sq c3857_nof2 c3857_nof3 c3857_nof4z⟩
theorem not_tile'_3857 (D : CongruentDissection 3857) : False :=
  not_tile_of_conditions' 3857 C'_3857 D

private theorem c3858_sqf   : LeafSqf 3858   := by decide +kernel
private theorem c3858_range : LeafRange 3858  := by decide +kernel
private theorem c3858_ell   : LeafEll 3858    := by decide +kernel
private theorem c3858_nsq   : NSqChkSq 3858   := by decide +kernel
private theorem c3858_har   : HArithChkSq 3858 := by decide +kernel
private theorem c3858_r     : LeafR 3858      := by decide +kernel
private theorem c3858_e'    : LeafE' 3858     := by decide +kernel
private theorem c3858_f1    : LeafF1 3858     := Or.inl (by decide)
private theorem c3858_s2    : S2ChkSq 3858    := by decide +kernel
private theorem c3858_s3    : S3ChkSq 3858    := by decide +kernel
private theorem c3858_iso   : LeafIso 3858    := by decide +kernel
private theorem c3858_nof2  : NoF2ChkSq 3858  := by decide +kernel
private theorem c3858_nof3  : NoF3ChkSq 3858  := by decide +kernel
private theorem c3858_nof4z : NoF4zChkSq 3858 := by decide +kernel
theorem C'_3858 : C' 3858 :=
  ⟨c3858_sqf, c3858_range, c3858_ell, leafNSq_of_sq c3858_nsq, leafHAr_of_sq c3858_har,
   c3858_r, c3858_e', c3858_f1, leafS2_of_sq c3858_s2, leafS3_of_sq c3858_s3,
   c3858_iso, leafR8_of_sq c3858_nof2 c3858_nof3 c3858_nof4z⟩
theorem not_tile'_3858 (D : CongruentDissection 3858) : False :=
  not_tile_of_conditions' 3858 C'_3858 D

private theorem c3859_sqf   : LeafSqf 3859   := by decide +kernel
private theorem c3859_range : LeafRange 3859  := by decide +kernel
private theorem c3859_ell   : LeafEll 3859    := by decide +kernel
private theorem c3859_nsq   : NSqChkSq 3859   := by decide +kernel
private theorem c3859_har   : HArithChkSq 3859 := by decide +kernel
private theorem c3859_r     : LeafR 3859      := by decide +kernel
private theorem c3859_e'    : LeafE' 3859     := by decide +kernel
private theorem c3859_f1    : LeafF1 3859     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3859_s2    : S2ChkSq 3859    := by decide +kernel
private theorem c3859_s3    : S3ChkSq 3859    := by decide +kernel
private theorem c3859_iso   : LeafIso 3859    := by decide +kernel
private theorem c3859_nof2  : NoF2ChkSq 3859  := by decide +kernel
private theorem c3859_nof3  : NoF3ChkSq 3859  := by decide +kernel
private theorem c3859_nof4z : NoF4zChkSq 3859 := by decide +kernel
theorem C'_3859 : C' 3859 :=
  ⟨c3859_sqf, c3859_range, c3859_ell, leafNSq_of_sq c3859_nsq, leafHAr_of_sq c3859_har,
   c3859_r, c3859_e', c3859_f1, leafS2_of_sq c3859_s2, leafS3_of_sq c3859_s3,
   c3859_iso, leafR8_of_sq c3859_nof2 c3859_nof3 c3859_nof4z⟩
theorem not_tile'_3859 (D : CongruentDissection 3859) : False :=
  not_tile_of_conditions' 3859 C'_3859 D

private theorem c3862_sqf   : LeafSqf 3862   := by decide +kernel
private theorem c3862_range : LeafRange 3862  := by decide +kernel
private theorem c3862_ell   : LeafEll 3862    := by decide +kernel
private theorem c3862_nsq   : NSqChkSq 3862   := by decide +kernel
private theorem c3862_har   : HArithChkSq 3862 := by decide +kernel
private theorem c3862_r     : LeafR 3862      := by decide +kernel
private theorem c3862_e'    : LeafE' 3862     := by decide +kernel
private theorem c3862_f1    : LeafF1 3862     := Or.inl (by decide)
private theorem c3862_s2    : S2ChkSq 3862    := by decide +kernel
private theorem c3862_s3    : S3ChkSq 3862    := by decide +kernel
private theorem c3862_iso   : LeafIso 3862    := by decide +kernel
private theorem c3862_nof2  : NoF2ChkSq 3862  := by decide +kernel
private theorem c3862_nof3  : NoF3ChkSq 3862  := by decide +kernel
private theorem c3862_nof4z : NoF4zChkSq 3862 := by decide +kernel
theorem C'_3862 : C' 3862 :=
  ⟨c3862_sqf, c3862_range, c3862_ell, leafNSq_of_sq c3862_nsq, leafHAr_of_sq c3862_har,
   c3862_r, c3862_e', c3862_f1, leafS2_of_sq c3862_s2, leafS3_of_sq c3862_s3,
   c3862_iso, leafR8_of_sq c3862_nof2 c3862_nof3 c3862_nof4z⟩
theorem not_tile'_3862 (D : CongruentDissection 3862) : False :=
  not_tile_of_conditions' 3862 C'_3862 D

end Erdos634.Draft.AllN2

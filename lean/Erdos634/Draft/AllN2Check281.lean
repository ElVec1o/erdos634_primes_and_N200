/- AllN2Check281: N = 4919, 4921, 4922, 4926, 4927
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4919_sqf   : LeafSqf 4919   := by decide +kernel
private theorem c4919_range : LeafRange 4919  := by decide +kernel
private theorem c4919_ell   : LeafEll 4919    := by decide +kernel
private theorem c4919_nsq   : NSqChkSq 4919   := by decide +kernel
private theorem c4919_har   : HArithChkSq 4919 := by decide +kernel
private theorem c4919_r     : LeafR 4919      := by decide +kernel
private theorem c4919_e'    : LeafE' 4919     := by decide +kernel
private theorem c4919_f1    : LeafF1 4919     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4919_s2    : S2ChkSq 4919    := by decide +kernel
private theorem c4919_s3    : S3ChkSq 4919    := by decide +kernel
private theorem c4919_iso   : LeafIso 4919    := by decide +kernel
private theorem c4919_nof2  : NoF2ChkSq 4919  := by decide +kernel
private theorem c4919_nof3  : NoF3ChkSq 4919  := by decide +kernel
private theorem c4919_nof4z : NoF4zChkSq 4919 := by decide +kernel
theorem C'_4919 : C' 4919 :=
  ⟨c4919_sqf, c4919_range, c4919_ell, leafNSq_of_sq c4919_nsq, leafHAr_of_sq c4919_har,
   c4919_r, c4919_e', c4919_f1, leafS2_of_sq c4919_s2, leafS3_of_sq c4919_s3,
   c4919_iso, leafR8_of_sq c4919_nof2 c4919_nof3 c4919_nof4z⟩
theorem not_tile'_4919 (D : CongruentDissection 4919) : False :=
  not_tile_of_conditions' 4919 C'_4919 D

private theorem c4921_sqf   : LeafSqf 4921   := by decide +kernel
private theorem c4921_range : LeafRange 4921  := by decide +kernel
private theorem c4921_ell   : LeafEll 4921    := by decide +kernel
private theorem c4921_nsq   : NSqChkSq 4921   := by decide +kernel
private theorem c4921_har   : HArithChkSq 4921 := by decide +kernel
private theorem c4921_r     : LeafR 4921      := by decide +kernel
private theorem c4921_e'    : LeafE' 4921     := by decide +kernel
private theorem c4921_f1    : LeafF1 4921     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4921_s2    : S2ChkSq 4921    := by decide +kernel
private theorem c4921_s3    : S3ChkSq 4921    := by decide +kernel
private theorem c4921_iso   : LeafIso 4921    := by decide +kernel
private theorem c4921_nof2  : NoF2ChkSq 4921  := by decide +kernel
private theorem c4921_nof3  : NoF3ChkSq 4921  := by decide +kernel
private theorem c4921_nof4z : NoF4zChkSq 4921 := by decide +kernel
theorem C'_4921 : C' 4921 :=
  ⟨c4921_sqf, c4921_range, c4921_ell, leafNSq_of_sq c4921_nsq, leafHAr_of_sq c4921_har,
   c4921_r, c4921_e', c4921_f1, leafS2_of_sq c4921_s2, leafS3_of_sq c4921_s3,
   c4921_iso, leafR8_of_sq c4921_nof2 c4921_nof3 c4921_nof4z⟩
theorem not_tile'_4921 (D : CongruentDissection 4921) : False :=
  not_tile_of_conditions' 4921 C'_4921 D

private theorem c4922_sqf   : LeafSqf 4922   := by decide +kernel
private theorem c4922_range : LeafRange 4922  := by decide +kernel
private theorem c4922_ell   : LeafEll 4922    := by decide +kernel
private theorem c4922_nsq   : NSqChkSq 4922   := by decide +kernel
private theorem c4922_har   : HArithChkSq 4922 := by decide +kernel
private theorem c4922_r     : LeafR 4922      := by decide +kernel
private theorem c4922_e'    : LeafE' 4922     := by decide +kernel
private theorem c4922_f1    : LeafF1 4922     := Or.inl (by decide)
private theorem c4922_s2    : S2ChkSq 4922    := by decide +kernel
private theorem c4922_s3    : S3ChkSq 4922    := by decide +kernel
private theorem c4922_iso   : LeafIso 4922    := by decide +kernel
private theorem c4922_nof2  : NoF2ChkSq 4922  := by decide +kernel
private theorem c4922_nof3  : NoF3ChkSq 4922  := by decide +kernel
private theorem c4922_nof4z : NoF4zChkSq 4922 := by decide +kernel
theorem C'_4922 : C' 4922 :=
  ⟨c4922_sqf, c4922_range, c4922_ell, leafNSq_of_sq c4922_nsq, leafHAr_of_sq c4922_har,
   c4922_r, c4922_e', c4922_f1, leafS2_of_sq c4922_s2, leafS3_of_sq c4922_s3,
   c4922_iso, leafR8_of_sq c4922_nof2 c4922_nof3 c4922_nof4z⟩
theorem not_tile'_4922 (D : CongruentDissection 4922) : False :=
  not_tile_of_conditions' 4922 C'_4922 D

private theorem c4926_sqf   : LeafSqf 4926   := by decide +kernel
private theorem c4926_range : LeafRange 4926  := by decide +kernel
private theorem c4926_ell   : LeafEll 4926    := by decide +kernel
private theorem c4926_nsq   : NSqChkSq 4926   := by decide +kernel
private theorem c4926_har   : HArithChkSq 4926 := by decide +kernel
private theorem c4926_r     : LeafR 4926      := by decide +kernel
private theorem c4926_e'    : LeafE' 4926     := by decide +kernel
private theorem c4926_f1    : LeafF1 4926     := Or.inl (by decide)
private theorem c4926_s2    : S2ChkSq 4926    := by decide +kernel
private theorem c4926_s3    : S3ChkSq 4926    := by decide +kernel
private theorem c4926_iso   : LeafIso 4926    := by decide +kernel
private theorem c4926_nof2  : NoF2ChkSq 4926  := by decide +kernel
private theorem c4926_nof3  : NoF3ChkSq 4926  := by decide +kernel
private theorem c4926_nof4z : NoF4zChkSq 4926 := by decide +kernel
theorem C'_4926 : C' 4926 :=
  ⟨c4926_sqf, c4926_range, c4926_ell, leafNSq_of_sq c4926_nsq, leafHAr_of_sq c4926_har,
   c4926_r, c4926_e', c4926_f1, leafS2_of_sq c4926_s2, leafS3_of_sq c4926_s3,
   c4926_iso, leafR8_of_sq c4926_nof2 c4926_nof3 c4926_nof4z⟩
theorem not_tile'_4926 (D : CongruentDissection 4926) : False :=
  not_tile_of_conditions' 4926 C'_4926 D

private theorem c4927_sqf   : LeafSqf 4927   := by decide +kernel
private theorem c4927_range : LeafRange 4927  := by decide +kernel
private theorem c4927_ell   : LeafEll 4927    := by decide +kernel
private theorem c4927_nsq   : NSqChkSq 4927   := by decide +kernel
private theorem c4927_har   : HArithChkSq 4927 := by decide +kernel
private theorem c4927_r     : LeafR 4927      := by decide +kernel
private theorem c4927_e'    : LeafE' 4927     := by decide +kernel
private theorem c4927_f1    : LeafF1 4927     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4927_s2    : S2ChkSq 4927    := by decide +kernel
private theorem c4927_s3    : S3ChkSq 4927    := by decide +kernel
private theorem c4927_iso   : LeafIso 4927    := by decide +kernel
private theorem c4927_nof2  : NoF2ChkSq 4927  := by decide +kernel
private theorem c4927_nof3  : NoF3ChkSq 4927  := by decide +kernel
private theorem c4927_nof4z : NoF4zChkSq 4927 := by decide +kernel
theorem C'_4927 : C' 4927 :=
  ⟨c4927_sqf, c4927_range, c4927_ell, leafNSq_of_sq c4927_nsq, leafHAr_of_sq c4927_har,
   c4927_r, c4927_e', c4927_f1, leafS2_of_sq c4927_s2, leafS3_of_sq c4927_s3,
   c4927_iso, leafR8_of_sq c4927_nof2 c4927_nof3 c4927_nof4z⟩
theorem not_tile'_4927 (D : CongruentDissection 4927) : False :=
  not_tile_of_conditions' 4927 C'_4927 D

end Erdos634.Draft.AllN2

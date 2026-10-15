/- AllN2Check283: N = 4943, 4945, 4951, 4955, 4958
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4943_sqf   : LeafSqf 4943   := by decide +kernel
private theorem c4943_range : LeafRange 4943  := by decide +kernel
private theorem c4943_ell   : LeafEll 4943    := by decide +kernel
private theorem c4943_nsq   : NSqChkSq 4943   := by decide +kernel
private theorem c4943_har   : HArithChkSq 4943 := by decide +kernel
private theorem c4943_r     : LeafR 4943      := by decide +kernel
private theorem c4943_e'    : LeafE' 4943     := by decide +kernel
private theorem c4943_f1    : LeafF1 4943     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4943_s2    : S2ChkSq 4943    := by decide +kernel
private theorem c4943_s3    : S3ChkSq 4943    := by decide +kernel
private theorem c4943_iso   : LeafIso 4943    := by decide +kernel
private theorem c4943_nof2  : NoF2ChkSq 4943  := by decide +kernel
private theorem c4943_nof3  : NoF3ChkSq 4943  := by decide +kernel
private theorem c4943_nof4z : NoF4zChkSq 4943 := by decide +kernel
theorem C'_4943 : C' 4943 :=
  ⟨c4943_sqf, c4943_range, c4943_ell, leafNSq_of_sq c4943_nsq, leafHAr_of_sq c4943_har,
   c4943_r, c4943_e', c4943_f1, leafS2_of_sq c4943_s2, leafS3_of_sq c4943_s3,
   c4943_iso, leafR8_of_sq c4943_nof2 c4943_nof3 c4943_nof4z⟩
theorem not_tile'_4943 (D : CongruentDissection 4943) : False :=
  not_tile_of_conditions' 4943 C'_4943 D

private theorem c4945_sqf   : LeafSqf 4945   := by decide +kernel
private theorem c4945_range : LeafRange 4945  := by decide +kernel
private theorem c4945_ell   : LeafEll 4945    := by decide +kernel
private theorem c4945_nsq   : NSqChkSq 4945   := by decide +kernel
private theorem c4945_har   : HArithChkSq 4945 := by decide +kernel
private theorem c4945_r     : LeafR 4945      := by decide +kernel
private theorem c4945_e'    : LeafE' 4945     := by decide +kernel
private theorem c4945_f1    : LeafF1 4945     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4945_s2    : S2ChkSq 4945    := by decide +kernel
private theorem c4945_s3    : S3ChkSq 4945    := by decide +kernel
private theorem c4945_iso   : LeafIso 4945    := by decide +kernel
private theorem c4945_nof2  : NoF2ChkSq 4945  := by decide +kernel
private theorem c4945_nof3  : NoF3ChkSq 4945  := by decide +kernel
private theorem c4945_nof4z : NoF4zChkSq 4945 := by decide +kernel
theorem C'_4945 : C' 4945 :=
  ⟨c4945_sqf, c4945_range, c4945_ell, leafNSq_of_sq c4945_nsq, leafHAr_of_sq c4945_har,
   c4945_r, c4945_e', c4945_f1, leafS2_of_sq c4945_s2, leafS3_of_sq c4945_s3,
   c4945_iso, leafR8_of_sq c4945_nof2 c4945_nof3 c4945_nof4z⟩
theorem not_tile'_4945 (D : CongruentDissection 4945) : False :=
  not_tile_of_conditions' 4945 C'_4945 D

private theorem c4951_sqf   : LeafSqf 4951   := by decide +kernel
private theorem c4951_range : LeafRange 4951  := by decide +kernel
private theorem c4951_ell   : LeafEll 4951    := by decide +kernel
private theorem c4951_nsq   : NSqChkSq 4951   := by decide +kernel
private theorem c4951_har   : HArithChkSq 4951 := by decide +kernel
private theorem c4951_r     : LeafR 4951      := by decide +kernel
private theorem c4951_e'    : LeafE' 4951     := by decide +kernel
private theorem c4951_f1    : LeafF1 4951     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4951_s2    : S2ChkSq 4951    := by decide +kernel
private theorem c4951_s3    : S3ChkSq 4951    := by decide +kernel
private theorem c4951_iso   : LeafIso 4951    := by decide +kernel
private theorem c4951_nof2  : NoF2ChkSq 4951  := by decide +kernel
private theorem c4951_nof3  : NoF3ChkSq 4951  := by decide +kernel
private theorem c4951_nof4z : NoF4zChkSq 4951 := by decide +kernel
theorem C'_4951 : C' 4951 :=
  ⟨c4951_sqf, c4951_range, c4951_ell, leafNSq_of_sq c4951_nsq, leafHAr_of_sq c4951_har,
   c4951_r, c4951_e', c4951_f1, leafS2_of_sq c4951_s2, leafS3_of_sq c4951_s3,
   c4951_iso, leafR8_of_sq c4951_nof2 c4951_nof3 c4951_nof4z⟩
theorem not_tile'_4951 (D : CongruentDissection 4951) : False :=
  not_tile_of_conditions' 4951 C'_4951 D

private theorem c4955_sqf   : LeafSqf 4955   := by decide +kernel
private theorem c4955_range : LeafRange 4955  := by decide +kernel
private theorem c4955_ell   : LeafEll 4955    := by decide +kernel
private theorem c4955_nsq   : NSqChkSq 4955   := by decide +kernel
private theorem c4955_har   : HArithChkSq 4955 := by decide +kernel
private theorem c4955_r     : LeafR 4955      := by decide +kernel
private theorem c4955_e'    : LeafE' 4955     := by decide +kernel
private theorem c4955_f1    : LeafF1 4955     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4955_s2    : S2ChkSq 4955    := by decide +kernel
private theorem c4955_s3    : S3ChkSq 4955    := by decide +kernel
private theorem c4955_iso   : LeafIso 4955    := by decide +kernel
private theorem c4955_nof2  : NoF2ChkSq 4955  := by decide +kernel
private theorem c4955_nof3  : NoF3ChkSq 4955  := by decide +kernel
private theorem c4955_nof4z : NoF4zChkSq 4955 := by decide +kernel
theorem C'_4955 : C' 4955 :=
  ⟨c4955_sqf, c4955_range, c4955_ell, leafNSq_of_sq c4955_nsq, leafHAr_of_sq c4955_har,
   c4955_r, c4955_e', c4955_f1, leafS2_of_sq c4955_s2, leafS3_of_sq c4955_s3,
   c4955_iso, leafR8_of_sq c4955_nof2 c4955_nof3 c4955_nof4z⟩
theorem not_tile'_4955 (D : CongruentDissection 4955) : False :=
  not_tile_of_conditions' 4955 C'_4955 D

private theorem c4958_sqf   : LeafSqf 4958   := by decide +kernel
private theorem c4958_range : LeafRange 4958  := by decide +kernel
private theorem c4958_ell   : LeafEll 4958    := by decide +kernel
private theorem c4958_nsq   : NSqChkSq 4958   := by decide +kernel
private theorem c4958_har   : HArithChkSq 4958 := by decide +kernel
private theorem c4958_r     : LeafR 4958      := by decide +kernel
private theorem c4958_e'    : LeafE' 4958     := by decide +kernel
private theorem c4958_f1    : LeafF1 4958     := Or.inl (by decide)
private theorem c4958_s2    : S2ChkSq 4958    := by decide +kernel
private theorem c4958_s3    : S3ChkSq 4958    := by decide +kernel
private theorem c4958_iso   : LeafIso 4958    := by decide +kernel
private theorem c4958_nof2  : NoF2ChkSq 4958  := by decide +kernel
private theorem c4958_nof3  : NoF3ChkSq 4958  := by decide +kernel
private theorem c4958_nof4z : NoF4zChkSq 4958 := by decide +kernel
theorem C'_4958 : C' 4958 :=
  ⟨c4958_sqf, c4958_range, c4958_ell, leafNSq_of_sq c4958_nsq, leafHAr_of_sq c4958_har,
   c4958_r, c4958_e', c4958_f1, leafS2_of_sq c4958_s2, leafS3_of_sq c4958_s3,
   c4958_iso, leafR8_of_sq c4958_nof2 c4958_nof3 c4958_nof4z⟩
theorem not_tile'_4958 (D : CongruentDissection 4958) : False :=
  not_tile_of_conditions' 4958 C'_4958 D

end Erdos634.Draft.AllN2

/- AllN2Check274: N = 4841, 4843, 4846, 4847, 4853
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4841_sqf   : LeafSqf 4841   := by decide +kernel
private theorem c4841_range : LeafRange 4841  := by decide +kernel
private theorem c4841_ell   : LeafEll 4841    := by decide +kernel
private theorem c4841_nsq   : NSqChkSq 4841   := by decide +kernel
private theorem c4841_har   : HArithChkSq 4841 := by decide +kernel
private theorem c4841_r     : LeafR 4841      := by decide +kernel
private theorem c4841_e'    : LeafE' 4841     := by decide +kernel
private theorem c4841_f1    : LeafF1 4841     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4841_s2    : S2ChkSq 4841    := by decide +kernel
private theorem c4841_s3    : S3ChkSq 4841    := by decide +kernel
private theorem c4841_iso   : LeafIso 4841    := by decide +kernel
private theorem c4841_nof2  : NoF2ChkSq 4841  := by decide +kernel
private theorem c4841_nof3  : NoF3ChkSq 4841  := by decide +kernel
private theorem c4841_nof4z : NoF4zChkSq 4841 := by decide +kernel
theorem C'_4841 : C' 4841 :=
  ⟨c4841_sqf, c4841_range, c4841_ell, leafNSq_of_sq c4841_nsq, leafHAr_of_sq c4841_har,
   c4841_r, c4841_e', c4841_f1, leafS2_of_sq c4841_s2, leafS3_of_sq c4841_s3,
   c4841_iso, leafR8_of_sq c4841_nof2 c4841_nof3 c4841_nof4z⟩
theorem not_tile'_4841 (D : CongruentDissection 4841) : False :=
  not_tile_of_conditions' 4841 C'_4841 D

private theorem c4843_sqf   : LeafSqf 4843   := by decide +kernel
private theorem c4843_range : LeafRange 4843  := by decide +kernel
private theorem c4843_ell   : LeafEll 4843    := by decide +kernel
private theorem c4843_nsq   : NSqChkSq 4843   := by decide +kernel
private theorem c4843_har   : HArithChkSq 4843 := by decide +kernel
private theorem c4843_r     : LeafR 4843      := by decide +kernel
private theorem c4843_e'    : LeafE' 4843     := by decide +kernel
private theorem c4843_f1    : LeafF1 4843     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4843_s2    : S2ChkSq 4843    := by decide +kernel
private theorem c4843_s3    : S3ChkSq 4843    := by decide +kernel
private theorem c4843_iso   : LeafIso 4843    := by decide +kernel
private theorem c4843_nof2  : NoF2ChkSq 4843  := by decide +kernel
private theorem c4843_nof3  : NoF3ChkSq 4843  := by decide +kernel
private theorem c4843_nof4z : NoF4zChkSq 4843 := by decide +kernel
theorem C'_4843 : C' 4843 :=
  ⟨c4843_sqf, c4843_range, c4843_ell, leafNSq_of_sq c4843_nsq, leafHAr_of_sq c4843_har,
   c4843_r, c4843_e', c4843_f1, leafS2_of_sq c4843_s2, leafS3_of_sq c4843_s3,
   c4843_iso, leafR8_of_sq c4843_nof2 c4843_nof3 c4843_nof4z⟩
theorem not_tile'_4843 (D : CongruentDissection 4843) : False :=
  not_tile_of_conditions' 4843 C'_4843 D

private theorem c4846_sqf   : LeafSqf 4846   := by decide +kernel
private theorem c4846_range : LeafRange 4846  := by decide +kernel
private theorem c4846_ell   : LeafEll 4846    := by decide +kernel
private theorem c4846_nsq   : NSqChkSq 4846   := by decide +kernel
private theorem c4846_har   : HArithChkSq 4846 := by decide +kernel
private theorem c4846_r     : LeafR 4846      := by decide +kernel
private theorem c4846_e'    : LeafE' 4846     := by decide +kernel
private theorem c4846_f1    : LeafF1 4846     := Or.inl (by decide)
private theorem c4846_s2    : S2ChkSq 4846    := by decide +kernel
private theorem c4846_s3    : S3ChkSq 4846    := by decide +kernel
private theorem c4846_iso   : LeafIso 4846    := by decide +kernel
private theorem c4846_nof2  : NoF2ChkSq 4846  := by decide +kernel
private theorem c4846_nof3  : NoF3ChkSq 4846  := by decide +kernel
private theorem c4846_nof4z : NoF4zChkSq 4846 := by decide +kernel
theorem C'_4846 : C' 4846 :=
  ⟨c4846_sqf, c4846_range, c4846_ell, leafNSq_of_sq c4846_nsq, leafHAr_of_sq c4846_har,
   c4846_r, c4846_e', c4846_f1, leafS2_of_sq c4846_s2, leafS3_of_sq c4846_s3,
   c4846_iso, leafR8_of_sq c4846_nof2 c4846_nof3 c4846_nof4z⟩
theorem not_tile'_4846 (D : CongruentDissection 4846) : False :=
  not_tile_of_conditions' 4846 C'_4846 D

private theorem c4847_sqf   : LeafSqf 4847   := by decide +kernel
private theorem c4847_range : LeafRange 4847  := by decide +kernel
private theorem c4847_ell   : LeafEll 4847    := by decide +kernel
private theorem c4847_nsq   : NSqChkSq 4847   := by decide +kernel
private theorem c4847_har   : HArithChkSq 4847 := by decide +kernel
private theorem c4847_r     : LeafR 4847      := by decide +kernel
private theorem c4847_e'    : LeafE' 4847     := by decide +kernel
private theorem c4847_f1    : LeafF1 4847     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4847_s2    : S2ChkSq 4847    := by decide +kernel
private theorem c4847_s3    : S3ChkSq 4847    := by decide +kernel
private theorem c4847_iso   : LeafIso 4847    := by decide +kernel
private theorem c4847_nof2  : NoF2ChkSq 4847  := by decide +kernel
private theorem c4847_nof3  : NoF3ChkSq 4847  := by decide +kernel
private theorem c4847_nof4z : NoF4zChkSq 4847 := by decide +kernel
theorem C'_4847 : C' 4847 :=
  ⟨c4847_sqf, c4847_range, c4847_ell, leafNSq_of_sq c4847_nsq, leafHAr_of_sq c4847_har,
   c4847_r, c4847_e', c4847_f1, leafS2_of_sq c4847_s2, leafS3_of_sq c4847_s3,
   c4847_iso, leafR8_of_sq c4847_nof2 c4847_nof3 c4847_nof4z⟩
theorem not_tile'_4847 (D : CongruentDissection 4847) : False :=
  not_tile_of_conditions' 4847 C'_4847 D

private theorem c4853_sqf   : LeafSqf 4853   := by decide +kernel
private theorem c4853_range : LeafRange 4853  := by decide +kernel
private theorem c4853_ell   : LeafEll 4853    := by decide +kernel
private theorem c4853_nsq   : NSqChkSq 4853   := by decide +kernel
private theorem c4853_har   : HArithChkSq 4853 := by decide +kernel
private theorem c4853_r     : LeafR 4853      := by decide +kernel
private theorem c4853_e'    : LeafE' 4853     := by decide +kernel
private theorem c4853_f1    : LeafF1 4853     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4853_s2    : S2ChkSq 4853    := by decide +kernel
private theorem c4853_s3    : S3ChkSq 4853    := by decide +kernel
private theorem c4853_iso   : LeafIso 4853    := by decide +kernel
private theorem c4853_nof2  : NoF2ChkSq 4853  := by decide +kernel
private theorem c4853_nof3  : NoF3ChkSq 4853  := by decide +kernel
private theorem c4853_nof4z : NoF4zChkSq 4853 := by decide +kernel
theorem C'_4853 : C' 4853 :=
  ⟨c4853_sqf, c4853_range, c4853_ell, leafNSq_of_sq c4853_nsq, leafHAr_of_sq c4853_har,
   c4853_r, c4853_e', c4853_f1, leafS2_of_sq c4853_s2, leafS3_of_sq c4853_s3,
   c4853_iso, leafR8_of_sq c4853_nof2 c4853_nof3 c4853_nof4z⟩
theorem not_tile'_4853 (D : CongruentDissection 4853) : False :=
  not_tile_of_conditions' 4853 C'_4853 D

end Erdos634.Draft.AllN2

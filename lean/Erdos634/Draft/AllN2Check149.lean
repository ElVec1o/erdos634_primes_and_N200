/- AllN2Check149: N = 3241, 3243, 3245, 3246, 3247
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3241_sqf   : LeafSqf 3241   := by decide +kernel
private theorem c3241_range : LeafRange 3241  := by decide +kernel
private theorem c3241_ell   : LeafEll 3241    := by decide +kernel
private theorem c3241_nsq   : NSqChkSq 3241   := by decide +kernel
private theorem c3241_har   : HArithChkSq 3241 := by decide +kernel
private theorem c3241_r     : LeafR 3241      := by decide +kernel
private theorem c3241_e'    : LeafE' 3241     := by decide +kernel
private theorem c3241_f1    : LeafF1 3241     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3241_s2    : S2ChkSq 3241    := by decide +kernel
private theorem c3241_s3    : S3ChkSq 3241    := by decide +kernel
private theorem c3241_iso   : LeafIso 3241    := by decide +kernel
private theorem c3241_nof2  : NoF2ChkSq 3241  := by decide +kernel
private theorem c3241_nof3  : NoF3ChkSq 3241  := by decide +kernel
private theorem c3241_nof4z : NoF4zChkSq 3241 := by decide +kernel
theorem C'_3241 : C' 3241 :=
  ⟨c3241_sqf, c3241_range, c3241_ell, leafNSq_of_sq c3241_nsq, leafHAr_of_sq c3241_har,
   c3241_r, c3241_e', c3241_f1, leafS2_of_sq c3241_s2, leafS3_of_sq c3241_s3,
   c3241_iso, leafR8_of_sq c3241_nof2 c3241_nof3 c3241_nof4z⟩
theorem not_tile'_3241 (D : CongruentDissection 3241) : False :=
  not_tile_of_conditions' 3241 C'_3241 D

private theorem c3243_sqf   : LeafSqf 3243   := by decide +kernel
private theorem c3243_range : LeafRange 3243  := by decide +kernel
private theorem c3243_ell   : LeafEll 3243    := by decide +kernel
private theorem c3243_nsq   : NSqChkSq 3243   := by decide +kernel
private theorem c3243_har   : HArithChkSq 3243 := by decide +kernel
private theorem c3243_r     : LeafR 3243      := by decide +kernel
private theorem c3243_e'    : LeafE' 3243     := by decide +kernel
private theorem c3243_f1    : LeafF1 3243     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3243_s2    : S2ChkSq 3243    := by decide +kernel
private theorem c3243_s3    : S3ChkSq 3243    := by decide +kernel
private theorem c3243_iso   : LeafIso 3243    := by decide +kernel
private theorem c3243_nof2  : NoF2ChkSq 3243  := by decide +kernel
private theorem c3243_nof3  : NoF3ChkSq 3243  := by decide +kernel
private theorem c3243_nof4z : NoF4zChkSq 3243 := by decide +kernel
theorem C'_3243 : C' 3243 :=
  ⟨c3243_sqf, c3243_range, c3243_ell, leafNSq_of_sq c3243_nsq, leafHAr_of_sq c3243_har,
   c3243_r, c3243_e', c3243_f1, leafS2_of_sq c3243_s2, leafS3_of_sq c3243_s3,
   c3243_iso, leafR8_of_sq c3243_nof2 c3243_nof3 c3243_nof4z⟩
theorem not_tile'_3243 (D : CongruentDissection 3243) : False :=
  not_tile_of_conditions' 3243 C'_3243 D

private theorem c3245_sqf   : LeafSqf 3245   := by decide +kernel
private theorem c3245_range : LeafRange 3245  := by decide +kernel
private theorem c3245_ell   : LeafEll 3245    := by decide +kernel
private theorem c3245_nsq   : NSqChkSq 3245   := by decide +kernel
private theorem c3245_har   : HArithChkSq 3245 := by decide +kernel
private theorem c3245_r     : LeafR 3245      := by decide +kernel
private theorem c3245_e'    : LeafE' 3245     := by decide +kernel
private theorem c3245_f1    : LeafF1 3245     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3245_s2    : S2ChkSq 3245    := by decide +kernel
private theorem c3245_s3    : S3ChkSq 3245    := by decide +kernel
private theorem c3245_iso   : LeafIso 3245    := by decide +kernel
private theorem c3245_nof2  : NoF2ChkSq 3245  := by decide +kernel
private theorem c3245_nof3  : NoF3ChkSq 3245  := by decide +kernel
private theorem c3245_nof4z : NoF4zChkSq 3245 := by decide +kernel
theorem C'_3245 : C' 3245 :=
  ⟨c3245_sqf, c3245_range, c3245_ell, leafNSq_of_sq c3245_nsq, leafHAr_of_sq c3245_har,
   c3245_r, c3245_e', c3245_f1, leafS2_of_sq c3245_s2, leafS3_of_sq c3245_s3,
   c3245_iso, leafR8_of_sq c3245_nof2 c3245_nof3 c3245_nof4z⟩
theorem not_tile'_3245 (D : CongruentDissection 3245) : False :=
  not_tile_of_conditions' 3245 C'_3245 D

private theorem c3246_sqf   : LeafSqf 3246   := by decide +kernel
private theorem c3246_range : LeafRange 3246  := by decide +kernel
private theorem c3246_ell   : LeafEll 3246    := by decide +kernel
private theorem c3246_nsq   : NSqChkSq 3246   := by decide +kernel
private theorem c3246_har   : HArithChkSq 3246 := by decide +kernel
private theorem c3246_r     : LeafR 3246      := by decide +kernel
private theorem c3246_e'    : LeafE' 3246     := by decide +kernel
private theorem c3246_f1    : LeafF1 3246     := Or.inl (by decide)
private theorem c3246_s2    : S2ChkSq 3246    := by decide +kernel
private theorem c3246_s3    : S3ChkSq 3246    := by decide +kernel
private theorem c3246_iso   : LeafIso 3246    := by decide +kernel
private theorem c3246_nof2  : NoF2ChkSq 3246  := by decide +kernel
private theorem c3246_nof3  : NoF3ChkSq 3246  := by decide +kernel
private theorem c3246_nof4z : NoF4zChkSq 3246 := by decide +kernel
theorem C'_3246 : C' 3246 :=
  ⟨c3246_sqf, c3246_range, c3246_ell, leafNSq_of_sq c3246_nsq, leafHAr_of_sq c3246_har,
   c3246_r, c3246_e', c3246_f1, leafS2_of_sq c3246_s2, leafS3_of_sq c3246_s3,
   c3246_iso, leafR8_of_sq c3246_nof2 c3246_nof3 c3246_nof4z⟩
theorem not_tile'_3246 (D : CongruentDissection 3246) : False :=
  not_tile_of_conditions' 3246 C'_3246 D

private theorem c3247_sqf   : LeafSqf 3247   := by decide +kernel
private theorem c3247_range : LeafRange 3247  := by decide +kernel
private theorem c3247_ell   : LeafEll 3247    := by decide +kernel
private theorem c3247_nsq   : NSqChkSq 3247   := by decide +kernel
private theorem c3247_har   : HArithChkSq 3247 := by decide +kernel
private theorem c3247_r     : LeafR 3247      := by decide +kernel
private theorem c3247_e'    : LeafE' 3247     := by decide +kernel
private theorem c3247_f1    : LeafF1 3247     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3247_s2    : S2ChkSq 3247    := by decide +kernel
private theorem c3247_s3    : S3ChkSq 3247    := by decide +kernel
private theorem c3247_iso   : LeafIso 3247    := by decide +kernel
private theorem c3247_nof2  : NoF2ChkSq 3247  := by decide +kernel
private theorem c3247_nof3  : NoF3ChkSq 3247  := by decide +kernel
private theorem c3247_nof4z : NoF4zChkSq 3247 := by decide +kernel
theorem C'_3247 : C' 3247 :=
  ⟨c3247_sqf, c3247_range, c3247_ell, leafNSq_of_sq c3247_nsq, leafHAr_of_sq c3247_har,
   c3247_r, c3247_e', c3247_f1, leafS2_of_sq c3247_s2, leafS3_of_sq c3247_s3,
   c3247_iso, leafR8_of_sq c3247_nof2 c3247_nof3 c3247_nof4z⟩
theorem not_tile'_3247 (D : CongruentDissection 3247) : False :=
  not_tile_of_conditions' 3247 C'_3247 D

end Erdos634.Draft.AllN2

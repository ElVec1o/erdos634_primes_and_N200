/- AllN2Check139: N = 3103, 3107, 3110, 3113, 3115
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3103_sqf   : LeafSqf 3103   := by decide +kernel
private theorem c3103_range : LeafRange 3103  := by decide +kernel
private theorem c3103_ell   : LeafEll 3103    := by decide +kernel
private theorem c3103_nsq   : NSqChkSq 3103   := by decide +kernel
private theorem c3103_har   : HArithChkSq 3103 := by decide +kernel
private theorem c3103_r     : LeafR 3103      := by decide +kernel
private theorem c3103_e'    : LeafE' 3103     := by decide +kernel
private theorem c3103_f1    : LeafF1 3103     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3103_s2    : S2ChkSq 3103    := by decide +kernel
private theorem c3103_s3    : S3ChkSq 3103    := by decide +kernel
private theorem c3103_iso   : LeafIso 3103    := by decide +kernel
private theorem c3103_nof2  : NoF2ChkSq 3103  := by decide +kernel
private theorem c3103_nof3  : NoF3ChkSq 3103  := by decide +kernel
private theorem c3103_nof4z : NoF4zChkSq 3103 := by decide +kernel
theorem C'_3103 : C' 3103 :=
  ⟨c3103_sqf, c3103_range, c3103_ell, leafNSq_of_sq c3103_nsq, leafHAr_of_sq c3103_har,
   c3103_r, c3103_e', c3103_f1, leafS2_of_sq c3103_s2, leafS3_of_sq c3103_s3,
   c3103_iso, leafR8_of_sq c3103_nof2 c3103_nof3 c3103_nof4z⟩
theorem not_tile'_3103 (D : CongruentDissection 3103) : False :=
  not_tile_of_conditions' 3103 C'_3103 D

private theorem c3107_sqf   : LeafSqf 3107   := by decide +kernel
private theorem c3107_range : LeafRange 3107  := by decide +kernel
private theorem c3107_ell   : LeafEll 3107    := by decide +kernel
private theorem c3107_nsq   : NSqChkSq 3107   := by decide +kernel
private theorem c3107_har   : HArithChkSq 3107 := by decide +kernel
private theorem c3107_r     : LeafR 3107      := by decide +kernel
private theorem c3107_e'    : LeafE' 3107     := by decide +kernel
private theorem c3107_f1    : LeafF1 3107     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3107_s2    : S2ChkSq 3107    := by decide +kernel
private theorem c3107_s3    : S3ChkSq 3107    := by decide +kernel
private theorem c3107_iso   : LeafIso 3107    := by decide +kernel
private theorem c3107_nof2  : NoF2ChkSq 3107  := by decide +kernel
private theorem c3107_nof3  : NoF3ChkSq 3107  := by decide +kernel
private theorem c3107_nof4z : NoF4zChkSq 3107 := by decide +kernel
theorem C'_3107 : C' 3107 :=
  ⟨c3107_sqf, c3107_range, c3107_ell, leafNSq_of_sq c3107_nsq, leafHAr_of_sq c3107_har,
   c3107_r, c3107_e', c3107_f1, leafS2_of_sq c3107_s2, leafS3_of_sq c3107_s3,
   c3107_iso, leafR8_of_sq c3107_nof2 c3107_nof3 c3107_nof4z⟩
theorem not_tile'_3107 (D : CongruentDissection 3107) : False :=
  not_tile_of_conditions' 3107 C'_3107 D

private theorem c3110_sqf   : LeafSqf 3110   := by decide +kernel
private theorem c3110_range : LeafRange 3110  := by decide +kernel
private theorem c3110_ell   : LeafEll 3110    := by decide +kernel
private theorem c3110_nsq   : NSqChkSq 3110   := by decide +kernel
private theorem c3110_har   : HArithChkSq 3110 := by decide +kernel
private theorem c3110_r     : LeafR 3110      := by decide +kernel
private theorem c3110_e'    : LeafE' 3110     := by decide +kernel
private theorem c3110_f1    : LeafF1 3110     := Or.inl (by decide)
private theorem c3110_s2    : S2ChkSq 3110    := by decide +kernel
private theorem c3110_s3    : S3ChkSq 3110    := by decide +kernel
private theorem c3110_iso   : LeafIso 3110    := by decide +kernel
private theorem c3110_nof2  : NoF2ChkSq 3110  := by decide +kernel
private theorem c3110_nof3  : NoF3ChkSq 3110  := by decide +kernel
private theorem c3110_nof4z : NoF4zChkSq 3110 := by decide +kernel
theorem C'_3110 : C' 3110 :=
  ⟨c3110_sqf, c3110_range, c3110_ell, leafNSq_of_sq c3110_nsq, leafHAr_of_sq c3110_har,
   c3110_r, c3110_e', c3110_f1, leafS2_of_sq c3110_s2, leafS3_of_sq c3110_s3,
   c3110_iso, leafR8_of_sq c3110_nof2 c3110_nof3 c3110_nof4z⟩
theorem not_tile'_3110 (D : CongruentDissection 3110) : False :=
  not_tile_of_conditions' 3110 C'_3110 D

private theorem c3113_sqf   : LeafSqf 3113   := by decide +kernel
private theorem c3113_range : LeafRange 3113  := by decide +kernel
private theorem c3113_ell   : LeafEll 3113    := by decide +kernel
private theorem c3113_nsq   : NSqChkSq 3113   := by decide +kernel
private theorem c3113_har   : HArithChkSq 3113 := by decide +kernel
private theorem c3113_r     : LeafR 3113      := by decide +kernel
private theorem c3113_e'    : LeafE' 3113     := by decide +kernel
private theorem c3113_f1    : LeafF1 3113     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3113_s2    : S2ChkSq 3113    := by decide +kernel
private theorem c3113_s3    : S3ChkSq 3113    := by decide +kernel
private theorem c3113_iso   : LeafIso 3113    := by decide +kernel
private theorem c3113_nof2  : NoF2ChkSq 3113  := by decide +kernel
private theorem c3113_nof3  : NoF3ChkSq 3113  := by decide +kernel
private theorem c3113_nof4z : NoF4zChkSq 3113 := by decide +kernel
theorem C'_3113 : C' 3113 :=
  ⟨c3113_sqf, c3113_range, c3113_ell, leafNSq_of_sq c3113_nsq, leafHAr_of_sq c3113_har,
   c3113_r, c3113_e', c3113_f1, leafS2_of_sq c3113_s2, leafS3_of_sq c3113_s3,
   c3113_iso, leafR8_of_sq c3113_nof2 c3113_nof3 c3113_nof4z⟩
theorem not_tile'_3113 (D : CongruentDissection 3113) : False :=
  not_tile_of_conditions' 3113 C'_3113 D

private theorem c3115_sqf   : LeafSqf 3115   := by decide +kernel
private theorem c3115_range : LeafRange 3115  := by decide +kernel
private theorem c3115_ell   : LeafEll 3115    := by decide +kernel
private theorem c3115_nsq   : NSqChkSq 3115   := by decide +kernel
private theorem c3115_har   : HArithChkSq 3115 := by decide +kernel
private theorem c3115_r     : LeafR 3115      := by decide +kernel
private theorem c3115_e'    : LeafE' 3115     := by decide +kernel
private theorem c3115_f1    : LeafF1 3115     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3115_s2    : S2ChkSq 3115    := by decide +kernel
private theorem c3115_s3    : S3ChkSq 3115    := by decide +kernel
private theorem c3115_iso   : LeafIso 3115    := by decide +kernel
private theorem c3115_nof2  : NoF2ChkSq 3115  := by decide +kernel
private theorem c3115_nof3  : NoF3ChkSq 3115  := by decide +kernel
private theorem c3115_nof4z : NoF4zChkSq 3115 := by decide +kernel
theorem C'_3115 : C' 3115 :=
  ⟨c3115_sqf, c3115_range, c3115_ell, leafNSq_of_sq c3115_nsq, leafHAr_of_sq c3115_har,
   c3115_r, c3115_e', c3115_f1, leafS2_of_sq c3115_s2, leafS3_of_sq c3115_s3,
   c3115_iso, leafR8_of_sq c3115_nof2 c3115_nof3 c3115_nof4z⟩
theorem not_tile'_3115 (D : CongruentDissection 3115) : False :=
  not_tile_of_conditions' 3115 C'_3115 D

end Erdos634.Draft.AllN2

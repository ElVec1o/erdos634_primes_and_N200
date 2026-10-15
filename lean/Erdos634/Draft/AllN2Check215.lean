/- AllN2Check215: N = 4103, 4109, 4110, 4111, 4115
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4103_sqf   : LeafSqf 4103   := by decide +kernel
private theorem c4103_range : LeafRange 4103  := by decide +kernel
private theorem c4103_ell   : LeafEll 4103    := by decide +kernel
private theorem c4103_nsq   : NSqChkSq 4103   := by decide +kernel
private theorem c4103_har   : HArithChkSq 4103 := by decide +kernel
private theorem c4103_r     : LeafR 4103      := by decide +kernel
private theorem c4103_e'    : LeafE' 4103     := by decide +kernel
private theorem c4103_f1    : LeafF1 4103     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4103_s2    : S2ChkSq 4103    := by decide +kernel
private theorem c4103_s3    : S3ChkSq 4103    := by decide +kernel
private theorem c4103_iso   : LeafIso 4103    := by decide +kernel
private theorem c4103_nof2  : NoF2ChkSq 4103  := by decide +kernel
private theorem c4103_nof3  : NoF3ChkSq 4103  := by decide +kernel
private theorem c4103_nof4z : NoF4zChkSq 4103 := by decide +kernel
theorem C'_4103 : C' 4103 :=
  ⟨c4103_sqf, c4103_range, c4103_ell, leafNSq_of_sq c4103_nsq, leafHAr_of_sq c4103_har,
   c4103_r, c4103_e', c4103_f1, leafS2_of_sq c4103_s2, leafS3_of_sq c4103_s3,
   c4103_iso, leafR8_of_sq c4103_nof2 c4103_nof3 c4103_nof4z⟩
theorem not_tile'_4103 (D : CongruentDissection 4103) : False :=
  not_tile_of_conditions' 4103 C'_4103 D

private theorem c4109_sqf   : LeafSqf 4109   := by decide +kernel
private theorem c4109_range : LeafRange 4109  := by decide +kernel
private theorem c4109_ell   : LeafEll 4109    := by decide +kernel
private theorem c4109_nsq   : NSqChkSq 4109   := by decide +kernel
private theorem c4109_har   : HArithChkSq 4109 := by decide +kernel
private theorem c4109_r     : LeafR 4109      := by decide +kernel
private theorem c4109_e'    : LeafE' 4109     := by decide +kernel
private theorem c4109_f1    : LeafF1 4109     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4109_s2    : S2ChkSq 4109    := by decide +kernel
private theorem c4109_s3    : S3ChkSq 4109    := by decide +kernel
private theorem c4109_iso   : LeafIso 4109    := by decide +kernel
private theorem c4109_nof2  : NoF2ChkSq 4109  := by decide +kernel
private theorem c4109_nof3  : NoF3ChkSq 4109  := by decide +kernel
private theorem c4109_nof4z : NoF4zChkSq 4109 := by decide +kernel
theorem C'_4109 : C' 4109 :=
  ⟨c4109_sqf, c4109_range, c4109_ell, leafNSq_of_sq c4109_nsq, leafHAr_of_sq c4109_har,
   c4109_r, c4109_e', c4109_f1, leafS2_of_sq c4109_s2, leafS3_of_sq c4109_s3,
   c4109_iso, leafR8_of_sq c4109_nof2 c4109_nof3 c4109_nof4z⟩
theorem not_tile'_4109 (D : CongruentDissection 4109) : False :=
  not_tile_of_conditions' 4109 C'_4109 D

private theorem c4110_sqf   : LeafSqf 4110   := by decide +kernel
private theorem c4110_range : LeafRange 4110  := by decide +kernel
private theorem c4110_ell   : LeafEll 4110    := by decide +kernel
private theorem c4110_nsq   : NSqChkSq 4110   := by decide +kernel
private theorem c4110_har   : HArithChkSq 4110 := by decide +kernel
private theorem c4110_r     : LeafR 4110      := by decide +kernel
private theorem c4110_e'    : LeafE' 4110     := by decide +kernel
private theorem c4110_f1    : LeafF1 4110     := Or.inl (by decide)
private theorem c4110_s2    : S2ChkSq 4110    := by decide +kernel
private theorem c4110_s3    : S3ChkSq 4110    := by decide +kernel
private theorem c4110_iso   : LeafIso 4110    := by decide +kernel
private theorem c4110_nof2  : NoF2ChkSq 4110  := by decide +kernel
private theorem c4110_nof3  : NoF3ChkSq 4110  := by decide +kernel
private theorem c4110_nof4z : NoF4zChkSq 4110 := by decide +kernel
theorem C'_4110 : C' 4110 :=
  ⟨c4110_sqf, c4110_range, c4110_ell, leafNSq_of_sq c4110_nsq, leafHAr_of_sq c4110_har,
   c4110_r, c4110_e', c4110_f1, leafS2_of_sq c4110_s2, leafS3_of_sq c4110_s3,
   c4110_iso, leafR8_of_sq c4110_nof2 c4110_nof3 c4110_nof4z⟩
theorem not_tile'_4110 (D : CongruentDissection 4110) : False :=
  not_tile_of_conditions' 4110 C'_4110 D

private theorem c4111_sqf   : LeafSqf 4111   := by decide +kernel
private theorem c4111_range : LeafRange 4111  := by decide +kernel
private theorem c4111_ell   : LeafEll 4111    := by decide +kernel
private theorem c4111_nsq   : NSqChkSq 4111   := by decide +kernel
private theorem c4111_har   : HArithChkSq 4111 := by decide +kernel
private theorem c4111_r     : LeafR 4111      := by decide +kernel
private theorem c4111_e'    : LeafE' 4111     := by decide +kernel
private theorem c4111_f1    : LeafF1 4111     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4111_s2    : S2ChkSq 4111    := by decide +kernel
private theorem c4111_s3    : S3ChkSq 4111    := by decide +kernel
private theorem c4111_iso   : LeafIso 4111    := by decide +kernel
private theorem c4111_nof2  : NoF2ChkSq 4111  := by decide +kernel
private theorem c4111_nof3  : NoF3ChkSq 4111  := by decide +kernel
private theorem c4111_nof4z : NoF4zChkSq 4111 := by decide +kernel
theorem C'_4111 : C' 4111 :=
  ⟨c4111_sqf, c4111_range, c4111_ell, leafNSq_of_sq c4111_nsq, leafHAr_of_sq c4111_har,
   c4111_r, c4111_e', c4111_f1, leafS2_of_sq c4111_s2, leafS3_of_sq c4111_s3,
   c4111_iso, leafR8_of_sq c4111_nof2 c4111_nof3 c4111_nof4z⟩
theorem not_tile'_4111 (D : CongruentDissection 4111) : False :=
  not_tile_of_conditions' 4111 C'_4111 D

private theorem c4115_sqf   : LeafSqf 4115   := by decide +kernel
private theorem c4115_range : LeafRange 4115  := by decide +kernel
private theorem c4115_ell   : LeafEll 4115    := by decide +kernel
private theorem c4115_nsq   : NSqChkSq 4115   := by decide +kernel
private theorem c4115_har   : HArithChkSq 4115 := by decide +kernel
private theorem c4115_r     : LeafR 4115      := by decide +kernel
private theorem c4115_e'    : LeafE' 4115     := by decide +kernel
private theorem c4115_f1    : LeafF1 4115     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4115_s2    : S2ChkSq 4115    := by decide +kernel
private theorem c4115_s3    : S3ChkSq 4115    := by decide +kernel
private theorem c4115_iso   : LeafIso 4115    := by decide +kernel
private theorem c4115_nof2  : NoF2ChkSq 4115  := by decide +kernel
private theorem c4115_nof3  : NoF3ChkSq 4115  := by decide +kernel
private theorem c4115_nof4z : NoF4zChkSq 4115 := by decide +kernel
theorem C'_4115 : C' 4115 :=
  ⟨c4115_sqf, c4115_range, c4115_ell, leafNSq_of_sq c4115_nsq, leafHAr_of_sq c4115_har,
   c4115_r, c4115_e', c4115_f1, leafS2_of_sq c4115_s2, leafS3_of_sq c4115_s3,
   c4115_iso, leafR8_of_sq c4115_nof2 c4115_nof3 c4115_nof4z⟩
theorem not_tile'_4115 (D : CongruentDissection 4115) : False :=
  not_tile_of_conditions' 4115 C'_4115 D

end Erdos634.Draft.AllN2

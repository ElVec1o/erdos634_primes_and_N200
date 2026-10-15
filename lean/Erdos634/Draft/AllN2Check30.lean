/- AllN2Check30: N = 1253, 1255, 1257, 1263, 1265
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1253_sqf   : LeafSqf 1253   := by decide +kernel
private theorem c1253_range : LeafRange 1253  := by decide +kernel
private theorem c1253_ell   : LeafEll 1253    := by decide +kernel
private theorem c1253_nsq   : NSqChkSq 1253   := by decide +kernel
private theorem c1253_har   : HArithChkSq 1253 := by decide +kernel
private theorem c1253_r     : LeafR 1253      := by decide +kernel
private theorem c1253_e'    : LeafE' 1253     := by decide +kernel
private theorem c1253_f1    : LeafF1 1253     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1253_s2    : S2ChkSq 1253    := by decide +kernel
private theorem c1253_s3    : S3ChkSq 1253    := by decide +kernel
private theorem c1253_iso   : LeafIso 1253    := by decide +kernel
private theorem c1253_nof2  : NoF2ChkSq 1253  := by decide +kernel
private theorem c1253_nof3  : NoF3ChkSq 1253  := by decide +kernel
private theorem c1253_nof4z : NoF4zChkSq 1253 := by decide +kernel
theorem C'_1253 : C' 1253 :=
  ⟨c1253_sqf, c1253_range, c1253_ell, leafNSq_of_sq c1253_nsq, leafHAr_of_sq c1253_har,
   c1253_r, c1253_e', c1253_f1, leafS2_of_sq c1253_s2, leafS3_of_sq c1253_s3,
   c1253_iso, leafR8_of_sq c1253_nof2 c1253_nof3 c1253_nof4z⟩
theorem not_tile'_1253 (D : CongruentDissection 1253) : False :=
  not_tile_of_conditions' 1253 C'_1253 D

private theorem c1255_sqf   : LeafSqf 1255   := by decide +kernel
private theorem c1255_range : LeafRange 1255  := by decide +kernel
private theorem c1255_ell   : LeafEll 1255    := by decide +kernel
private theorem c1255_nsq   : NSqChkSq 1255   := by decide +kernel
private theorem c1255_har   : HArithChkSq 1255 := by decide +kernel
private theorem c1255_r     : LeafR 1255      := by decide +kernel
private theorem c1255_e'    : LeafE' 1255     := by decide +kernel
private theorem c1255_f1    : LeafF1 1255     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1255_s2    : S2ChkSq 1255    := by decide +kernel
private theorem c1255_s3    : S3ChkSq 1255    := by decide +kernel
private theorem c1255_iso   : LeafIso 1255    := by decide +kernel
private theorem c1255_nof2  : NoF2ChkSq 1255  := by decide +kernel
private theorem c1255_nof3  : NoF3ChkSq 1255  := by decide +kernel
private theorem c1255_nof4z : NoF4zChkSq 1255 := by decide +kernel
theorem C'_1255 : C' 1255 :=
  ⟨c1255_sqf, c1255_range, c1255_ell, leafNSq_of_sq c1255_nsq, leafHAr_of_sq c1255_har,
   c1255_r, c1255_e', c1255_f1, leafS2_of_sq c1255_s2, leafS3_of_sq c1255_s3,
   c1255_iso, leafR8_of_sq c1255_nof2 c1255_nof3 c1255_nof4z⟩
theorem not_tile'_1255 (D : CongruentDissection 1255) : False :=
  not_tile_of_conditions' 1255 C'_1255 D

private theorem c1257_sqf   : LeafSqf 1257   := by decide +kernel
private theorem c1257_range : LeafRange 1257  := by decide +kernel
private theorem c1257_ell   : LeafEll 1257    := by decide +kernel
private theorem c1257_nsq   : NSqChkSq 1257   := by decide +kernel
private theorem c1257_har   : HArithChkSq 1257 := by decide +kernel
private theorem c1257_r     : LeafR 1257      := by decide +kernel
private theorem c1257_e'    : LeafE' 1257     := by decide +kernel
private theorem c1257_f1    : LeafF1 1257     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1257_s2    : S2ChkSq 1257    := by decide +kernel
private theorem c1257_s3    : S3ChkSq 1257    := by decide +kernel
private theorem c1257_iso   : LeafIso 1257    := by decide +kernel
private theorem c1257_nof2  : NoF2ChkSq 1257  := by decide +kernel
private theorem c1257_nof3  : NoF3ChkSq 1257  := by decide +kernel
private theorem c1257_nof4z : NoF4zChkSq 1257 := by decide +kernel
theorem C'_1257 : C' 1257 :=
  ⟨c1257_sqf, c1257_range, c1257_ell, leafNSq_of_sq c1257_nsq, leafHAr_of_sq c1257_har,
   c1257_r, c1257_e', c1257_f1, leafS2_of_sq c1257_s2, leafS3_of_sq c1257_s3,
   c1257_iso, leafR8_of_sq c1257_nof2 c1257_nof3 c1257_nof4z⟩
theorem not_tile'_1257 (D : CongruentDissection 1257) : False :=
  not_tile_of_conditions' 1257 C'_1257 D

private theorem c1263_sqf   : LeafSqf 1263   := by decide +kernel
private theorem c1263_range : LeafRange 1263  := by decide +kernel
private theorem c1263_ell   : LeafEll 1263    := by decide +kernel
private theorem c1263_nsq   : NSqChkSq 1263   := by decide +kernel
private theorem c1263_har   : HArithChkSq 1263 := by decide +kernel
private theorem c1263_r     : LeafR 1263      := by decide +kernel
private theorem c1263_e'    : LeafE' 1263     := by decide +kernel
private theorem c1263_f1    : LeafF1 1263     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1263_s2    : S2ChkSq 1263    := by decide +kernel
private theorem c1263_s3    : S3ChkSq 1263    := by decide +kernel
private theorem c1263_iso   : LeafIso 1263    := by decide +kernel
private theorem c1263_nof2  : NoF2ChkSq 1263  := by decide +kernel
private theorem c1263_nof3  : NoF3ChkSq 1263  := by decide +kernel
private theorem c1263_nof4z : NoF4zChkSq 1263 := by decide +kernel
theorem C'_1263 : C' 1263 :=
  ⟨c1263_sqf, c1263_range, c1263_ell, leafNSq_of_sq c1263_nsq, leafHAr_of_sq c1263_har,
   c1263_r, c1263_e', c1263_f1, leafS2_of_sq c1263_s2, leafS3_of_sq c1263_s3,
   c1263_iso, leafR8_of_sq c1263_nof2 c1263_nof3 c1263_nof4z⟩
theorem not_tile'_1263 (D : CongruentDissection 1263) : False :=
  not_tile_of_conditions' 1263 C'_1263 D

private theorem c1265_sqf   : LeafSqf 1265   := by decide +kernel
private theorem c1265_range : LeafRange 1265  := by decide +kernel
private theorem c1265_ell   : LeafEll 1265    := by decide +kernel
private theorem c1265_nsq   : NSqChkSq 1265   := by decide +kernel
private theorem c1265_har   : HArithChkSq 1265 := by decide +kernel
private theorem c1265_r     : LeafR 1265      := by decide +kernel
private theorem c1265_e'    : LeafE' 1265     := by decide +kernel
private theorem c1265_f1    : LeafF1 1265     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1265_s2    : S2ChkSq 1265    := by decide +kernel
private theorem c1265_s3    : S3ChkSq 1265    := by decide +kernel
private theorem c1265_iso   : LeafIso 1265    := by decide +kernel
private theorem c1265_nof2  : NoF2ChkSq 1265  := by decide +kernel
private theorem c1265_nof3  : NoF3ChkSq 1265  := by decide +kernel
private theorem c1265_nof4z : NoF4zChkSq 1265 := by decide +kernel
theorem C'_1265 : C' 1265 :=
  ⟨c1265_sqf, c1265_range, c1265_ell, leafNSq_of_sq c1265_nsq, leafHAr_of_sq c1265_har,
   c1265_r, c1265_e', c1265_f1, leafS2_of_sq c1265_s2, leafS3_of_sq c1265_s3,
   c1265_iso, leafR8_of_sq c1265_nof2 c1265_nof3 c1265_nof4z⟩
theorem not_tile'_1265 (D : CongruentDissection 1265) : False :=
  not_tile_of_conditions' 1265 C'_1265 D

end Erdos634.Draft.AllN2

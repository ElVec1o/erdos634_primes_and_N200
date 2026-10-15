/- AllN2Check31: N = 1267, 1293, 1295, 1299, 1309
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1267_sqf   : LeafSqf 1267   := by decide +kernel
private theorem c1267_range : LeafRange 1267  := by decide +kernel
private theorem c1267_ell   : LeafEll 1267    := by decide +kernel
private theorem c1267_nsq   : NSqChkSq 1267   := by decide +kernel
private theorem c1267_har   : HArithChkSq 1267 := by decide +kernel
private theorem c1267_r     : LeafR 1267      := by decide +kernel
private theorem c1267_e'    : LeafE' 1267     := by decide +kernel
private theorem c1267_f1    : LeafF1 1267     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1267_s2    : S2ChkSq 1267    := by decide +kernel
private theorem c1267_s3    : S3ChkSq 1267    := by decide +kernel
private theorem c1267_iso   : LeafIso 1267    := by decide +kernel
private theorem c1267_nof2  : NoF2ChkSq 1267  := by decide +kernel
private theorem c1267_nof3  : NoF3ChkSq 1267  := by decide +kernel
private theorem c1267_nof4z : NoF4zChkSq 1267 := by decide +kernel
theorem C'_1267 : C' 1267 :=
  ⟨c1267_sqf, c1267_range, c1267_ell, leafNSq_of_sq c1267_nsq, leafHAr_of_sq c1267_har,
   c1267_r, c1267_e', c1267_f1, leafS2_of_sq c1267_s2, leafS3_of_sq c1267_s3,
   c1267_iso, leafR8_of_sq c1267_nof2 c1267_nof3 c1267_nof4z⟩
theorem not_tile'_1267 (D : CongruentDissection 1267) : False :=
  not_tile_of_conditions' 1267 C'_1267 D

private theorem c1293_sqf   : LeafSqf 1293   := by decide +kernel
private theorem c1293_range : LeafRange 1293  := by decide +kernel
private theorem c1293_ell   : LeafEll 1293    := by decide +kernel
private theorem c1293_nsq   : NSqChkSq 1293   := by decide +kernel
private theorem c1293_har   : HArithChkSq 1293 := by decide +kernel
private theorem c1293_r     : LeafR 1293      := by decide +kernel
private theorem c1293_e'    : LeafE' 1293     := by decide +kernel
private theorem c1293_f1    : LeafF1 1293     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1293_s2    : S2ChkSq 1293    := by decide +kernel
private theorem c1293_s3    : S3ChkSq 1293    := by decide +kernel
private theorem c1293_iso   : LeafIso 1293    := by decide +kernel
private theorem c1293_nof2  : NoF2ChkSq 1293  := by decide +kernel
private theorem c1293_nof3  : NoF3ChkSq 1293  := by decide +kernel
private theorem c1293_nof4z : NoF4zChkSq 1293 := by decide +kernel
theorem C'_1293 : C' 1293 :=
  ⟨c1293_sqf, c1293_range, c1293_ell, leafNSq_of_sq c1293_nsq, leafHAr_of_sq c1293_har,
   c1293_r, c1293_e', c1293_f1, leafS2_of_sq c1293_s2, leafS3_of_sq c1293_s3,
   c1293_iso, leafR8_of_sq c1293_nof2 c1293_nof3 c1293_nof4z⟩
theorem not_tile'_1293 (D : CongruentDissection 1293) : False :=
  not_tile_of_conditions' 1293 C'_1293 D

private theorem c1295_sqf   : LeafSqf 1295   := by decide +kernel
private theorem c1295_range : LeafRange 1295  := by decide +kernel
private theorem c1295_ell   : LeafEll 1295    := by decide +kernel
private theorem c1295_nsq   : NSqChkSq 1295   := by decide +kernel
private theorem c1295_har   : HArithChkSq 1295 := by decide +kernel
private theorem c1295_r     : LeafR 1295      := by decide +kernel
private theorem c1295_e'    : LeafE' 1295     := by decide +kernel
private theorem c1295_f1    : LeafF1 1295     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1295_s2    : S2ChkSq 1295    := by decide +kernel
private theorem c1295_s3    : S3ChkSq 1295    := by decide +kernel
private theorem c1295_iso   : LeafIso 1295    := by decide +kernel
private theorem c1295_nof2  : NoF2ChkSq 1295  := by decide +kernel
private theorem c1295_nof3  : NoF3ChkSq 1295  := by decide +kernel
private theorem c1295_nof4z : NoF4zChkSq 1295 := by decide +kernel
theorem C'_1295 : C' 1295 :=
  ⟨c1295_sqf, c1295_range, c1295_ell, leafNSq_of_sq c1295_nsq, leafHAr_of_sq c1295_har,
   c1295_r, c1295_e', c1295_f1, leafS2_of_sq c1295_s2, leafS3_of_sq c1295_s3,
   c1295_iso, leafR8_of_sq c1295_nof2 c1295_nof3 c1295_nof4z⟩
theorem not_tile'_1295 (D : CongruentDissection 1295) : False :=
  not_tile_of_conditions' 1295 C'_1295 D

private theorem c1299_sqf   : LeafSqf 1299   := by decide +kernel
private theorem c1299_range : LeafRange 1299  := by decide +kernel
private theorem c1299_ell   : LeafEll 1299    := by decide +kernel
private theorem c1299_nsq   : NSqChkSq 1299   := by decide +kernel
private theorem c1299_har   : HArithChkSq 1299 := by decide +kernel
private theorem c1299_r     : LeafR 1299      := by decide +kernel
private theorem c1299_e'    : LeafE' 1299     := by decide +kernel
private theorem c1299_f1    : LeafF1 1299     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1299_s2    : S2ChkSq 1299    := by decide +kernel
private theorem c1299_s3    : S3ChkSq 1299    := by decide +kernel
private theorem c1299_iso   : LeafIso 1299    := by decide +kernel
private theorem c1299_nof2  : NoF2ChkSq 1299  := by decide +kernel
private theorem c1299_nof3  : NoF3ChkSq 1299  := by decide +kernel
private theorem c1299_nof4z : NoF4zChkSq 1299 := by decide +kernel
theorem C'_1299 : C' 1299 :=
  ⟨c1299_sqf, c1299_range, c1299_ell, leafNSq_of_sq c1299_nsq, leafHAr_of_sq c1299_har,
   c1299_r, c1299_e', c1299_f1, leafS2_of_sq c1299_s2, leafS3_of_sq c1299_s3,
   c1299_iso, leafR8_of_sq c1299_nof2 c1299_nof3 c1299_nof4z⟩
theorem not_tile'_1299 (D : CongruentDissection 1299) : False :=
  not_tile_of_conditions' 1299 C'_1299 D

private theorem c1309_sqf   : LeafSqf 1309   := by decide +kernel
private theorem c1309_range : LeafRange 1309  := by decide +kernel
private theorem c1309_ell   : LeafEll 1309    := by decide +kernel
private theorem c1309_nsq   : NSqChkSq 1309   := by decide +kernel
private theorem c1309_har   : HArithChkSq 1309 := by decide +kernel
private theorem c1309_r     : LeafR 1309      := by decide +kernel
private theorem c1309_e'    : LeafE' 1309     := by decide +kernel
private theorem c1309_f1    : LeafF1 1309     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1309_s2    : S2ChkSq 1309    := by decide +kernel
private theorem c1309_s3    : S3ChkSq 1309    := by decide +kernel
private theorem c1309_iso   : LeafIso 1309    := by decide +kernel
private theorem c1309_nof2  : NoF2ChkSq 1309  := by decide +kernel
private theorem c1309_nof3  : NoF3ChkSq 1309  := by decide +kernel
private theorem c1309_nof4z : NoF4zChkSq 1309 := by decide +kernel
theorem C'_1309 : C' 1309 :=
  ⟨c1309_sqf, c1309_range, c1309_ell, leafNSq_of_sq c1309_nsq, leafHAr_of_sq c1309_har,
   c1309_r, c1309_e', c1309_f1, leafS2_of_sq c1309_s2, leafS3_of_sq c1309_s3,
   c1309_iso, leafR8_of_sq c1309_nof2 c1309_nof3 c1309_nof4z⟩
theorem not_tile'_1309 (D : CongruentDissection 1309) : False :=
  not_tile_of_conditions' 1309 C'_1309 D

end Erdos634.Draft.AllN2

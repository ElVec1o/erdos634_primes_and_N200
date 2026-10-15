/- AllN2Check229: N = 4290, 4291, 4294, 4295, 4298
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4290_sqf   : LeafSqf 4290   := by decide +kernel
private theorem c4290_range : LeafRange 4290  := by decide +kernel
private theorem c4290_ell   : LeafEll 4290    := by decide +kernel
private theorem c4290_nsq   : NSqChkSq 4290   := by decide +kernel
private theorem c4290_har   : HArithChkSq 4290 := by decide +kernel
private theorem c4290_r     : LeafR 4290      := by decide +kernel
private theorem c4290_e'    : LeafE' 4290     := by decide +kernel
private theorem c4290_f1    : LeafF1 4290     := Or.inl (by decide)
private theorem c4290_s2    : S2ChkSq 4290    := by decide +kernel
private theorem c4290_s3    : S3ChkSq 4290    := by decide +kernel
private theorem c4290_iso   : LeafIso 4290    := by decide +kernel
private theorem c4290_nof2  : NoF2ChkSq 4290  := by decide +kernel
private theorem c4290_nof3  : NoF3ChkSq 4290  := by decide +kernel
private theorem c4290_nof4z : NoF4zChkSq 4290 := by decide +kernel
theorem C'_4290 : C' 4290 :=
  ⟨c4290_sqf, c4290_range, c4290_ell, leafNSq_of_sq c4290_nsq, leafHAr_of_sq c4290_har,
   c4290_r, c4290_e', c4290_f1, leafS2_of_sq c4290_s2, leafS3_of_sq c4290_s3,
   c4290_iso, leafR8_of_sq c4290_nof2 c4290_nof3 c4290_nof4z⟩
theorem not_tile'_4290 (D : CongruentDissection 4290) : False :=
  not_tile_of_conditions' 4290 C'_4290 D

private theorem c4291_sqf   : LeafSqf 4291   := by decide +kernel
private theorem c4291_range : LeafRange 4291  := by decide +kernel
private theorem c4291_ell   : LeafEll 4291    := by decide +kernel
private theorem c4291_nsq   : NSqChkSq 4291   := by decide +kernel
private theorem c4291_har   : HArithChkSq 4291 := by decide +kernel
private theorem c4291_r     : LeafR 4291      := by decide +kernel
private theorem c4291_e'    : LeafE' 4291     := by decide +kernel
private theorem c4291_f1    : LeafF1 4291     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4291_s2    : S2ChkSq 4291    := by decide +kernel
private theorem c4291_s3    : S3ChkSq 4291    := by decide +kernel
private theorem c4291_iso   : LeafIso 4291    := by decide +kernel
private theorem c4291_nof2  : NoF2ChkSq 4291  := by decide +kernel
private theorem c4291_nof3  : NoF3ChkSq 4291  := by decide +kernel
private theorem c4291_nof4z : NoF4zChkSq 4291 := by decide +kernel
theorem C'_4291 : C' 4291 :=
  ⟨c4291_sqf, c4291_range, c4291_ell, leafNSq_of_sq c4291_nsq, leafHAr_of_sq c4291_har,
   c4291_r, c4291_e', c4291_f1, leafS2_of_sq c4291_s2, leafS3_of_sq c4291_s3,
   c4291_iso, leafR8_of_sq c4291_nof2 c4291_nof3 c4291_nof4z⟩
theorem not_tile'_4291 (D : CongruentDissection 4291) : False :=
  not_tile_of_conditions' 4291 C'_4291 D

private theorem c4294_sqf   : LeafSqf 4294   := by decide +kernel
private theorem c4294_range : LeafRange 4294  := by decide +kernel
private theorem c4294_ell   : LeafEll 4294    := by decide +kernel
private theorem c4294_nsq   : NSqChkSq 4294   := by decide +kernel
private theorem c4294_har   : HArithChkSq 4294 := by decide +kernel
private theorem c4294_r     : LeafR 4294      := by decide +kernel
private theorem c4294_e'    : LeafE' 4294     := by decide +kernel
private theorem c4294_f1    : LeafF1 4294     := Or.inl (by decide)
private theorem c4294_s2    : S2ChkSq 4294    := by decide +kernel
private theorem c4294_s3    : S3ChkSq 4294    := by decide +kernel
private theorem c4294_iso   : LeafIso 4294    := by decide +kernel
private theorem c4294_nof2  : NoF2ChkSq 4294  := by decide +kernel
private theorem c4294_nof3  : NoF3ChkSq 4294  := by decide +kernel
private theorem c4294_nof4z : NoF4zChkSq 4294 := by decide +kernel
theorem C'_4294 : C' 4294 :=
  ⟨c4294_sqf, c4294_range, c4294_ell, leafNSq_of_sq c4294_nsq, leafHAr_of_sq c4294_har,
   c4294_r, c4294_e', c4294_f1, leafS2_of_sq c4294_s2, leafS3_of_sq c4294_s3,
   c4294_iso, leafR8_of_sq c4294_nof2 c4294_nof3 c4294_nof4z⟩
theorem not_tile'_4294 (D : CongruentDissection 4294) : False :=
  not_tile_of_conditions' 4294 C'_4294 D

private theorem c4295_sqf   : LeafSqf 4295   := by decide +kernel
private theorem c4295_range : LeafRange 4295  := by decide +kernel
private theorem c4295_ell   : LeafEll 4295    := by decide +kernel
private theorem c4295_nsq   : NSqChkSq 4295   := by decide +kernel
private theorem c4295_har   : HArithChkSq 4295 := by decide +kernel
private theorem c4295_r     : LeafR 4295      := by decide +kernel
private theorem c4295_e'    : LeafE' 4295     := by decide +kernel
private theorem c4295_f1    : LeafF1 4295     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4295_s2    : S2ChkSq 4295    := by decide +kernel
private theorem c4295_s3    : S3ChkSq 4295    := by decide +kernel
private theorem c4295_iso   : LeafIso 4295    := by decide +kernel
private theorem c4295_nof2  : NoF2ChkSq 4295  := by decide +kernel
private theorem c4295_nof3  : NoF3ChkSq 4295  := by decide +kernel
private theorem c4295_nof4z : NoF4zChkSq 4295 := by decide +kernel
theorem C'_4295 : C' 4295 :=
  ⟨c4295_sqf, c4295_range, c4295_ell, leafNSq_of_sq c4295_nsq, leafHAr_of_sq c4295_har,
   c4295_r, c4295_e', c4295_f1, leafS2_of_sq c4295_s2, leafS3_of_sq c4295_s3,
   c4295_iso, leafR8_of_sq c4295_nof2 c4295_nof3 c4295_nof4z⟩
theorem not_tile'_4295 (D : CongruentDissection 4295) : False :=
  not_tile_of_conditions' 4295 C'_4295 D

private theorem c4298_sqf   : LeafSqf 4298   := by decide +kernel
private theorem c4298_range : LeafRange 4298  := by decide +kernel
private theorem c4298_ell   : LeafEll 4298    := by decide +kernel
private theorem c4298_nsq   : NSqChkSq 4298   := by decide +kernel
private theorem c4298_har   : HArithChkSq 4298 := by decide +kernel
private theorem c4298_r     : LeafR 4298      := by decide +kernel
private theorem c4298_e'    : LeafE' 4298     := by decide +kernel
private theorem c4298_f1    : LeafF1 4298     := Or.inl (by decide)
private theorem c4298_s2    : S2ChkSq 4298    := by decide +kernel
private theorem c4298_s3    : S3ChkSq 4298    := by decide +kernel
private theorem c4298_iso   : LeafIso 4298    := by decide +kernel
private theorem c4298_nof2  : NoF2ChkSq 4298  := by decide +kernel
private theorem c4298_nof3  : NoF3ChkSq 4298  := by decide +kernel
private theorem c4298_nof4z : NoF4zChkSq 4298 := by decide +kernel
theorem C'_4298 : C' 4298 :=
  ⟨c4298_sqf, c4298_range, c4298_ell, leafNSq_of_sq c4298_nsq, leafHAr_of_sq c4298_har,
   c4298_r, c4298_e', c4298_f1, leafS2_of_sq c4298_s2, leafS3_of_sq c4298_s3,
   c4298_iso, leafR8_of_sq c4298_nof2 c4298_nof3 c4298_nof4z⟩
theorem not_tile'_4298 (D : CongruentDissection 4298) : False :=
  not_tile_of_conditions' 4298 C'_4298 D

end Erdos634.Draft.AllN2

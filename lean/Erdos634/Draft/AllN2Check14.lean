/- AllN2Check14: N = 267, 291, 295, 303, 309, 321, 327, 335, 339, 355
   Squarefree exclusions via C' with sqrt-bounded checks (Wave-2 OOM fix). -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c267_sqf   : LeafSqf 267   := by decide +kernel
private theorem c267_range : LeafRange 267  := by decide +kernel
private theorem c267_ell   : LeafEll 267    := by decide +kernel
private theorem c267_nsq   : NSqChkSq 267   := by decide +kernel
private theorem c267_har   : HArithChkSq 267 := by decide +kernel
private theorem c267_r     : LeafR 267      := by decide +kernel
private theorem c267_e'    : LeafE' 267     := by decide +kernel
private theorem c267_f1    : LeafF1 267     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c267_s2    : S2ChkSq 267    := by decide +kernel
private theorem c267_s3    : S3ChkSq 267    := by decide +kernel
private theorem c267_iso   : LeafIso 267    := by decide +kernel
private theorem c267_nof2  : NoF2ChkSq 267  := by decide +kernel
private theorem c267_nof3  : NoF3ChkSq 267  := by decide +kernel
private theorem c267_nof4z : NoF4zChkSq 267 := by decide +kernel
theorem C'_267 : C' 267 :=
  ⟨c267_sqf, c267_range, c267_ell, leafNSq_of_sq c267_nsq, leafHAr_of_sq c267_har,
   c267_r, c267_e', c267_f1, leafS2_of_sq c267_s2, leafS3_of_sq c267_s3,
   c267_iso, leafR8_of_sq c267_nof2 c267_nof3 c267_nof4z⟩
theorem not_tile'_267 (D : CongruentDissection 267) : False :=
  not_tile_of_conditions' 267 C'_267 D

private theorem c291_sqf   : LeafSqf 291   := by decide +kernel
private theorem c291_range : LeafRange 291  := by decide +kernel
private theorem c291_ell   : LeafEll 291    := by decide +kernel
private theorem c291_nsq   : NSqChkSq 291   := by decide +kernel
private theorem c291_har   : HArithChkSq 291 := by decide +kernel
private theorem c291_r     : LeafR 291      := by decide +kernel
private theorem c291_e'    : LeafE' 291     := by decide +kernel
private theorem c291_f1    : LeafF1 291     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c291_s2    : S2ChkSq 291    := by decide +kernel
private theorem c291_s3    : S3ChkSq 291    := by decide +kernel
private theorem c291_iso   : LeafIso 291    := by decide +kernel
private theorem c291_nof2  : NoF2ChkSq 291  := by decide +kernel
private theorem c291_nof3  : NoF3ChkSq 291  := by decide +kernel
private theorem c291_nof4z : NoF4zChkSq 291 := by decide +kernel
theorem C'_291 : C' 291 :=
  ⟨c291_sqf, c291_range, c291_ell, leafNSq_of_sq c291_nsq, leafHAr_of_sq c291_har,
   c291_r, c291_e', c291_f1, leafS2_of_sq c291_s2, leafS3_of_sq c291_s3,
   c291_iso, leafR8_of_sq c291_nof2 c291_nof3 c291_nof4z⟩
theorem not_tile'_291 (D : CongruentDissection 291) : False :=
  not_tile_of_conditions' 291 C'_291 D

private theorem c295_sqf   : LeafSqf 295   := by decide +kernel
private theorem c295_range : LeafRange 295  := by decide +kernel
private theorem c295_ell   : LeafEll 295    := by decide +kernel
private theorem c295_nsq   : NSqChkSq 295   := by decide +kernel
private theorem c295_har   : HArithChkSq 295 := by decide +kernel
private theorem c295_r     : LeafR 295      := by decide +kernel
private theorem c295_e'    : LeafE' 295     := by decide +kernel
private theorem c295_f1    : LeafF1 295     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c295_s2    : S2ChkSq 295    := by decide +kernel
private theorem c295_s3    : S3ChkSq 295    := by decide +kernel
private theorem c295_iso   : LeafIso 295    := by decide +kernel
private theorem c295_nof2  : NoF2ChkSq 295  := by decide +kernel
private theorem c295_nof3  : NoF3ChkSq 295  := by decide +kernel
private theorem c295_nof4z : NoF4zChkSq 295 := by decide +kernel
theorem C'_295 : C' 295 :=
  ⟨c295_sqf, c295_range, c295_ell, leafNSq_of_sq c295_nsq, leafHAr_of_sq c295_har,
   c295_r, c295_e', c295_f1, leafS2_of_sq c295_s2, leafS3_of_sq c295_s3,
   c295_iso, leafR8_of_sq c295_nof2 c295_nof3 c295_nof4z⟩
theorem not_tile'_295 (D : CongruentDissection 295) : False :=
  not_tile_of_conditions' 295 C'_295 D

private theorem c303_sqf   : LeafSqf 303   := by decide +kernel
private theorem c303_range : LeafRange 303  := by decide +kernel
private theorem c303_ell   : LeafEll 303    := by decide +kernel
private theorem c303_nsq   : NSqChkSq 303   := by decide +kernel
private theorem c303_har   : HArithChkSq 303 := by decide +kernel
private theorem c303_r     : LeafR 303      := by decide +kernel
private theorem c303_e'    : LeafE' 303     := by decide +kernel
private theorem c303_f1    : LeafF1 303     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c303_s2    : S2ChkSq 303    := by decide +kernel
private theorem c303_s3    : S3ChkSq 303    := by decide +kernel
private theorem c303_iso   : LeafIso 303    := by decide +kernel
private theorem c303_nof2  : NoF2ChkSq 303  := by decide +kernel
private theorem c303_nof3  : NoF3ChkSq 303  := by decide +kernel
private theorem c303_nof4z : NoF4zChkSq 303 := by decide +kernel
theorem C'_303 : C' 303 :=
  ⟨c303_sqf, c303_range, c303_ell, leafNSq_of_sq c303_nsq, leafHAr_of_sq c303_har,
   c303_r, c303_e', c303_f1, leafS2_of_sq c303_s2, leafS3_of_sq c303_s3,
   c303_iso, leafR8_of_sq c303_nof2 c303_nof3 c303_nof4z⟩
theorem not_tile'_303 (D : CongruentDissection 303) : False :=
  not_tile_of_conditions' 303 C'_303 D

private theorem c309_sqf   : LeafSqf 309   := by decide +kernel
private theorem c309_range : LeafRange 309  := by decide +kernel
private theorem c309_ell   : LeafEll 309    := by decide +kernel
private theorem c309_nsq   : NSqChkSq 309   := by decide +kernel
private theorem c309_har   : HArithChkSq 309 := by decide +kernel
private theorem c309_r     : LeafR 309      := by decide +kernel
private theorem c309_e'    : LeafE' 309     := by decide +kernel
private theorem c309_f1    : LeafF1 309     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c309_s2    : S2ChkSq 309    := by decide +kernel
private theorem c309_s3    : S3ChkSq 309    := by decide +kernel
private theorem c309_iso   : LeafIso 309    := by decide +kernel
private theorem c309_nof2  : NoF2ChkSq 309  := by decide +kernel
private theorem c309_nof3  : NoF3ChkSq 309  := by decide +kernel
private theorem c309_nof4z : NoF4zChkSq 309 := by decide +kernel
theorem C'_309 : C' 309 :=
  ⟨c309_sqf, c309_range, c309_ell, leafNSq_of_sq c309_nsq, leafHAr_of_sq c309_har,
   c309_r, c309_e', c309_f1, leafS2_of_sq c309_s2, leafS3_of_sq c309_s3,
   c309_iso, leafR8_of_sq c309_nof2 c309_nof3 c309_nof4z⟩
theorem not_tile'_309 (D : CongruentDissection 309) : False :=
  not_tile_of_conditions' 309 C'_309 D

private theorem c321_sqf   : LeafSqf 321   := by decide +kernel
private theorem c321_range : LeafRange 321  := by decide +kernel
private theorem c321_ell   : LeafEll 321    := by decide +kernel
private theorem c321_nsq   : NSqChkSq 321   := by decide +kernel
private theorem c321_har   : HArithChkSq 321 := by decide +kernel
private theorem c321_r     : LeafR 321      := by decide +kernel
private theorem c321_e'    : LeafE' 321     := by decide +kernel
private theorem c321_f1    : LeafF1 321     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c321_s2    : S2ChkSq 321    := by decide +kernel
private theorem c321_s3    : S3ChkSq 321    := by decide +kernel
private theorem c321_iso   : LeafIso 321    := by decide +kernel
private theorem c321_nof2  : NoF2ChkSq 321  := by decide +kernel
private theorem c321_nof3  : NoF3ChkSq 321  := by decide +kernel
private theorem c321_nof4z : NoF4zChkSq 321 := by decide +kernel
theorem C'_321 : C' 321 :=
  ⟨c321_sqf, c321_range, c321_ell, leafNSq_of_sq c321_nsq, leafHAr_of_sq c321_har,
   c321_r, c321_e', c321_f1, leafS2_of_sq c321_s2, leafS3_of_sq c321_s3,
   c321_iso, leafR8_of_sq c321_nof2 c321_nof3 c321_nof4z⟩
theorem not_tile'_321 (D : CongruentDissection 321) : False :=
  not_tile_of_conditions' 321 C'_321 D

private theorem c327_sqf   : LeafSqf 327   := by decide +kernel
private theorem c327_range : LeafRange 327  := by decide +kernel
private theorem c327_ell   : LeafEll 327    := by decide +kernel
private theorem c327_nsq   : NSqChkSq 327   := by decide +kernel
private theorem c327_har   : HArithChkSq 327 := by decide +kernel
private theorem c327_r     : LeafR 327      := by decide +kernel
private theorem c327_e'    : LeafE' 327     := by decide +kernel
private theorem c327_f1    : LeafF1 327     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c327_s2    : S2ChkSq 327    := by decide +kernel
private theorem c327_s3    : S3ChkSq 327    := by decide +kernel
private theorem c327_iso   : LeafIso 327    := by decide +kernel
private theorem c327_nof2  : NoF2ChkSq 327  := by decide +kernel
private theorem c327_nof3  : NoF3ChkSq 327  := by decide +kernel
private theorem c327_nof4z : NoF4zChkSq 327 := by decide +kernel
theorem C'_327 : C' 327 :=
  ⟨c327_sqf, c327_range, c327_ell, leafNSq_of_sq c327_nsq, leafHAr_of_sq c327_har,
   c327_r, c327_e', c327_f1, leafS2_of_sq c327_s2, leafS3_of_sq c327_s3,
   c327_iso, leafR8_of_sq c327_nof2 c327_nof3 c327_nof4z⟩
theorem not_tile'_327 (D : CongruentDissection 327) : False :=
  not_tile_of_conditions' 327 C'_327 D

private theorem c335_sqf   : LeafSqf 335   := by decide +kernel
private theorem c335_range : LeafRange 335  := by decide +kernel
private theorem c335_ell   : LeafEll 335    := by decide +kernel
private theorem c335_nsq   : NSqChkSq 335   := by decide +kernel
private theorem c335_har   : HArithChkSq 335 := by decide +kernel
private theorem c335_r     : LeafR 335      := by decide +kernel
private theorem c335_e'    : LeafE' 335     := by decide +kernel
private theorem c335_f1    : LeafF1 335     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c335_s2    : S2ChkSq 335    := by decide +kernel
private theorem c335_s3    : S3ChkSq 335    := by decide +kernel
private theorem c335_iso   : LeafIso 335    := by decide +kernel
private theorem c335_nof2  : NoF2ChkSq 335  := by decide +kernel
private theorem c335_nof3  : NoF3ChkSq 335  := by decide +kernel
private theorem c335_nof4z : NoF4zChkSq 335 := by decide +kernel
theorem C'_335 : C' 335 :=
  ⟨c335_sqf, c335_range, c335_ell, leafNSq_of_sq c335_nsq, leafHAr_of_sq c335_har,
   c335_r, c335_e', c335_f1, leafS2_of_sq c335_s2, leafS3_of_sq c335_s3,
   c335_iso, leafR8_of_sq c335_nof2 c335_nof3 c335_nof4z⟩
theorem not_tile'_335 (D : CongruentDissection 335) : False :=
  not_tile_of_conditions' 335 C'_335 D

private theorem c339_sqf   : LeafSqf 339   := by decide +kernel
private theorem c339_range : LeafRange 339  := by decide +kernel
private theorem c339_ell   : LeafEll 339    := by decide +kernel
private theorem c339_nsq   : NSqChkSq 339   := by decide +kernel
private theorem c339_har   : HArithChkSq 339 := by decide +kernel
private theorem c339_r     : LeafR 339      := by decide +kernel
private theorem c339_e'    : LeafE' 339     := by decide +kernel
private theorem c339_f1    : LeafF1 339     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c339_s2    : S2ChkSq 339    := by decide +kernel
private theorem c339_s3    : S3ChkSq 339    := by decide +kernel
private theorem c339_iso   : LeafIso 339    := by decide +kernel
private theorem c339_nof2  : NoF2ChkSq 339  := by decide +kernel
private theorem c339_nof3  : NoF3ChkSq 339  := by decide +kernel
private theorem c339_nof4z : NoF4zChkSq 339 := by decide +kernel
theorem C'_339 : C' 339 :=
  ⟨c339_sqf, c339_range, c339_ell, leafNSq_of_sq c339_nsq, leafHAr_of_sq c339_har,
   c339_r, c339_e', c339_f1, leafS2_of_sq c339_s2, leafS3_of_sq c339_s3,
   c339_iso, leafR8_of_sq c339_nof2 c339_nof3 c339_nof4z⟩
theorem not_tile'_339 (D : CongruentDissection 339) : False :=
  not_tile_of_conditions' 339 C'_339 D

private theorem c355_sqf   : LeafSqf 355   := by decide +kernel
private theorem c355_range : LeafRange 355  := by decide +kernel
private theorem c355_ell   : LeafEll 355    := by decide +kernel
private theorem c355_nsq   : NSqChkSq 355   := by decide +kernel
private theorem c355_har   : HArithChkSq 355 := by decide +kernel
private theorem c355_r     : LeafR 355      := by decide +kernel
private theorem c355_e'    : LeafE' 355     := by decide +kernel
private theorem c355_f1    : LeafF1 355     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c355_s2    : S2ChkSq 355    := by decide +kernel
private theorem c355_s3    : S3ChkSq 355    := by decide +kernel
private theorem c355_iso   : LeafIso 355    := by decide +kernel
private theorem c355_nof2  : NoF2ChkSq 355  := by decide +kernel
private theorem c355_nof3  : NoF3ChkSq 355  := by decide +kernel
private theorem c355_nof4z : NoF4zChkSq 355 := by decide +kernel
theorem C'_355 : C' 355 :=
  ⟨c355_sqf, c355_range, c355_ell, leafNSq_of_sq c355_nsq, leafHAr_of_sq c355_har,
   c355_r, c355_e', c355_f1, leafS2_of_sq c355_s2, leafS3_of_sq c355_s3,
   c355_iso, leafR8_of_sq c355_nof2 c355_nof3 c355_nof4z⟩
theorem not_tile'_355 (D : CongruentDissection 355) : False :=
  not_tile_of_conditions' 355 C'_355 D

end Erdos634.Draft.AllN2

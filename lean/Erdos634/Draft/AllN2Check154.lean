/- AllN2Check154: N = 3307, 3309, 3310, 3311, 3317
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3307_sqf   : LeafSqf 3307   := by decide +kernel
private theorem c3307_range : LeafRange 3307  := by decide +kernel
private theorem c3307_ell   : LeafEll 3307    := by decide +kernel
private theorem c3307_nsq   : NSqChkSq 3307   := by decide +kernel
private theorem c3307_har   : HArithChkSq 3307 := by decide +kernel
private theorem c3307_r     : LeafR 3307      := by decide +kernel
private theorem c3307_e'    : LeafE' 3307     := by decide +kernel
private theorem c3307_f1    : LeafF1 3307     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3307_s2    : S2ChkSq 3307    := by decide +kernel
private theorem c3307_s3    : S3ChkSq 3307    := by decide +kernel
private theorem c3307_iso   : LeafIso 3307    := by decide +kernel
private theorem c3307_nof2  : NoF2ChkSq 3307  := by decide +kernel
private theorem c3307_nof3  : NoF3ChkSq 3307  := by decide +kernel
private theorem c3307_nof4z : NoF4zChkSq 3307 := by decide +kernel
theorem C'_3307 : C' 3307 :=
  ⟨c3307_sqf, c3307_range, c3307_ell, leafNSq_of_sq c3307_nsq, leafHAr_of_sq c3307_har,
   c3307_r, c3307_e', c3307_f1, leafS2_of_sq c3307_s2, leafS3_of_sq c3307_s3,
   c3307_iso, leafR8_of_sq c3307_nof2 c3307_nof3 c3307_nof4z⟩
theorem not_tile'_3307 (D : CongruentDissection 3307) : False :=
  not_tile_of_conditions' 3307 C'_3307 D

private theorem c3309_sqf   : LeafSqf 3309   := by decide +kernel
private theorem c3309_range : LeafRange 3309  := by decide +kernel
private theorem c3309_ell   : LeafEll 3309    := by decide +kernel
private theorem c3309_nsq   : NSqChkSq 3309   := by decide +kernel
private theorem c3309_har   : HArithChkSq 3309 := by decide +kernel
private theorem c3309_r     : LeafR 3309      := by decide +kernel
private theorem c3309_e'    : LeafE' 3309     := by decide +kernel
private theorem c3309_f1    : LeafF1 3309     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3309_s2    : S2ChkSq 3309    := by decide +kernel
private theorem c3309_s3    : S3ChkSq 3309    := by decide +kernel
private theorem c3309_iso   : LeafIso 3309    := by decide +kernel
private theorem c3309_nof2  : NoF2ChkSq 3309  := by decide +kernel
private theorem c3309_nof3  : NoF3ChkSq 3309  := by decide +kernel
private theorem c3309_nof4z : NoF4zChkSq 3309 := by decide +kernel
theorem C'_3309 : C' 3309 :=
  ⟨c3309_sqf, c3309_range, c3309_ell, leafNSq_of_sq c3309_nsq, leafHAr_of_sq c3309_har,
   c3309_r, c3309_e', c3309_f1, leafS2_of_sq c3309_s2, leafS3_of_sq c3309_s3,
   c3309_iso, leafR8_of_sq c3309_nof2 c3309_nof3 c3309_nof4z⟩
theorem not_tile'_3309 (D : CongruentDissection 3309) : False :=
  not_tile_of_conditions' 3309 C'_3309 D

private theorem c3310_sqf   : LeafSqf 3310   := by decide +kernel
private theorem c3310_range : LeafRange 3310  := by decide +kernel
private theorem c3310_ell   : LeafEll 3310    := by decide +kernel
private theorem c3310_nsq   : NSqChkSq 3310   := by decide +kernel
private theorem c3310_har   : HArithChkSq 3310 := by decide +kernel
private theorem c3310_r     : LeafR 3310      := by decide +kernel
private theorem c3310_e'    : LeafE' 3310     := by decide +kernel
private theorem c3310_f1    : LeafF1 3310     := Or.inl (by decide)
private theorem c3310_s2    : S2ChkSq 3310    := by decide +kernel
private theorem c3310_s3    : S3ChkSq 3310    := by decide +kernel
private theorem c3310_iso   : LeafIso 3310    := by decide +kernel
private theorem c3310_nof2  : NoF2ChkSq 3310  := by decide +kernel
private theorem c3310_nof3  : NoF3ChkSq 3310  := by decide +kernel
private theorem c3310_nof4z : NoF4zChkSq 3310 := by decide +kernel
theorem C'_3310 : C' 3310 :=
  ⟨c3310_sqf, c3310_range, c3310_ell, leafNSq_of_sq c3310_nsq, leafHAr_of_sq c3310_har,
   c3310_r, c3310_e', c3310_f1, leafS2_of_sq c3310_s2, leafS3_of_sq c3310_s3,
   c3310_iso, leafR8_of_sq c3310_nof2 c3310_nof3 c3310_nof4z⟩
theorem not_tile'_3310 (D : CongruentDissection 3310) : False :=
  not_tile_of_conditions' 3310 C'_3310 D

private theorem c3311_sqf   : LeafSqf 3311   := by decide +kernel
private theorem c3311_range : LeafRange 3311  := by decide +kernel
private theorem c3311_ell   : LeafEll 3311    := by decide +kernel
private theorem c3311_nsq   : NSqChkSq 3311   := by decide +kernel
private theorem c3311_har   : HArithChkSq 3311 := by decide +kernel
private theorem c3311_r     : LeafR 3311      := by decide +kernel
private theorem c3311_e'    : LeafE' 3311     := by decide +kernel
private theorem c3311_f1    : LeafF1 3311     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3311_s2    : S2ChkSq 3311    := by decide +kernel
private theorem c3311_s3    : S3ChkSq 3311    := by decide +kernel
private theorem c3311_iso   : LeafIso 3311    := by decide +kernel
private theorem c3311_nof2  : NoF2ChkSq 3311  := by decide +kernel
private theorem c3311_nof3  : NoF3ChkSq 3311  := by decide +kernel
private theorem c3311_nof4z : NoF4zChkSq 3311 := by decide +kernel
theorem C'_3311 : C' 3311 :=
  ⟨c3311_sqf, c3311_range, c3311_ell, leafNSq_of_sq c3311_nsq, leafHAr_of_sq c3311_har,
   c3311_r, c3311_e', c3311_f1, leafS2_of_sq c3311_s2, leafS3_of_sq c3311_s3,
   c3311_iso, leafR8_of_sq c3311_nof2 c3311_nof3 c3311_nof4z⟩
theorem not_tile'_3311 (D : CongruentDissection 3311) : False :=
  not_tile_of_conditions' 3311 C'_3311 D

private theorem c3317_sqf   : LeafSqf 3317   := by decide +kernel
private theorem c3317_range : LeafRange 3317  := by decide +kernel
private theorem c3317_ell   : LeafEll 3317    := by decide +kernel
private theorem c3317_nsq   : NSqChkSq 3317   := by decide +kernel
private theorem c3317_har   : HArithChkSq 3317 := by decide +kernel
private theorem c3317_r     : LeafR 3317      := by decide +kernel
private theorem c3317_e'    : LeafE' 3317     := by decide +kernel
private theorem c3317_f1    : LeafF1 3317     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3317_s2    : S2ChkSq 3317    := by decide +kernel
private theorem c3317_s3    : S3ChkSq 3317    := by decide +kernel
private theorem c3317_iso   : LeafIso 3317    := by decide +kernel
private theorem c3317_nof2  : NoF2ChkSq 3317  := by decide +kernel
private theorem c3317_nof3  : NoF3ChkSq 3317  := by decide +kernel
private theorem c3317_nof4z : NoF4zChkSq 3317 := by decide +kernel
theorem C'_3317 : C' 3317 :=
  ⟨c3317_sqf, c3317_range, c3317_ell, leafNSq_of_sq c3317_nsq, leafHAr_of_sq c3317_har,
   c3317_r, c3317_e', c3317_f1, leafS2_of_sq c3317_s2, leafS3_of_sq c3317_s3,
   c3317_iso, leafR8_of_sq c3317_nof2 c3317_nof3 c3317_nof4z⟩
theorem not_tile'_3317 (D : CongruentDissection 3317) : False :=
  not_tile_of_conditions' 3317 C'_3317 D

end Erdos634.Draft.AllN2

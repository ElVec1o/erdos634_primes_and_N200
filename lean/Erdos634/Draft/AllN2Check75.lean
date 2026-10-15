/- AllN2Check75: N = 2307, 2311, 2315, 2317, 2318
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2307_sqf   : LeafSqf 2307   := by decide +kernel
private theorem c2307_range : LeafRange 2307  := by decide +kernel
private theorem c2307_ell   : LeafEll 2307    := by decide +kernel
private theorem c2307_nsq   : NSqChkSq 2307   := by decide +kernel
private theorem c2307_har   : HArithChkSq 2307 := by decide +kernel
private theorem c2307_r     : LeafR 2307      := by decide +kernel
private theorem c2307_e'    : LeafE' 2307     := by decide +kernel
private theorem c2307_f1    : LeafF1 2307     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2307_s2    : S2ChkSq 2307    := by decide +kernel
private theorem c2307_s3    : S3ChkSq 2307    := by decide +kernel
private theorem c2307_iso   : LeafIso 2307    := by decide +kernel
private theorem c2307_nof2  : NoF2ChkSq 2307  := by decide +kernel
private theorem c2307_nof3  : NoF3ChkSq 2307  := by decide +kernel
private theorem c2307_nof4z : NoF4zChkSq 2307 := by decide +kernel
theorem C'_2307 : C' 2307 :=
  ⟨c2307_sqf, c2307_range, c2307_ell, leafNSq_of_sq c2307_nsq, leafHAr_of_sq c2307_har,
   c2307_r, c2307_e', c2307_f1, leafS2_of_sq c2307_s2, leafS3_of_sq c2307_s3,
   c2307_iso, leafR8_of_sq c2307_nof2 c2307_nof3 c2307_nof4z⟩
theorem not_tile'_2307 (D : CongruentDissection 2307) : False :=
  not_tile_of_conditions' 2307 C'_2307 D

private theorem c2311_sqf   : LeafSqf 2311   := by decide +kernel
private theorem c2311_range : LeafRange 2311  := by decide +kernel
private theorem c2311_ell   : LeafEll 2311    := by decide +kernel
private theorem c2311_nsq   : NSqChkSq 2311   := by decide +kernel
private theorem c2311_har   : HArithChkSq 2311 := by decide +kernel
private theorem c2311_r     : LeafR 2311      := by decide +kernel
private theorem c2311_e'    : LeafE' 2311     := by decide +kernel
private theorem c2311_f1    : LeafF1 2311     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2311_s2    : S2ChkSq 2311    := by decide +kernel
private theorem c2311_s3    : S3ChkSq 2311    := by decide +kernel
private theorem c2311_iso   : LeafIso 2311    := by decide +kernel
private theorem c2311_nof2  : NoF2ChkSq 2311  := by decide +kernel
private theorem c2311_nof3  : NoF3ChkSq 2311  := by decide +kernel
private theorem c2311_nof4z : NoF4zChkSq 2311 := by decide +kernel
theorem C'_2311 : C' 2311 :=
  ⟨c2311_sqf, c2311_range, c2311_ell, leafNSq_of_sq c2311_nsq, leafHAr_of_sq c2311_har,
   c2311_r, c2311_e', c2311_f1, leafS2_of_sq c2311_s2, leafS3_of_sq c2311_s3,
   c2311_iso, leafR8_of_sq c2311_nof2 c2311_nof3 c2311_nof4z⟩
theorem not_tile'_2311 (D : CongruentDissection 2311) : False :=
  not_tile_of_conditions' 2311 C'_2311 D

private theorem c2315_sqf   : LeafSqf 2315   := by decide +kernel
private theorem c2315_range : LeafRange 2315  := by decide +kernel
private theorem c2315_ell   : LeafEll 2315    := by decide +kernel
private theorem c2315_nsq   : NSqChkSq 2315   := by decide +kernel
private theorem c2315_har   : HArithChkSq 2315 := by decide +kernel
private theorem c2315_r     : LeafR 2315      := by decide +kernel
private theorem c2315_e'    : LeafE' 2315     := by decide +kernel
private theorem c2315_f1    : LeafF1 2315     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2315_s2    : S2ChkSq 2315    := by decide +kernel
private theorem c2315_s3    : S3ChkSq 2315    := by decide +kernel
private theorem c2315_iso   : LeafIso 2315    := by decide +kernel
private theorem c2315_nof2  : NoF2ChkSq 2315  := by decide +kernel
private theorem c2315_nof3  : NoF3ChkSq 2315  := by decide +kernel
private theorem c2315_nof4z : NoF4zChkSq 2315 := by decide +kernel
theorem C'_2315 : C' 2315 :=
  ⟨c2315_sqf, c2315_range, c2315_ell, leafNSq_of_sq c2315_nsq, leafHAr_of_sq c2315_har,
   c2315_r, c2315_e', c2315_f1, leafS2_of_sq c2315_s2, leafS3_of_sq c2315_s3,
   c2315_iso, leafR8_of_sq c2315_nof2 c2315_nof3 c2315_nof4z⟩
theorem not_tile'_2315 (D : CongruentDissection 2315) : False :=
  not_tile_of_conditions' 2315 C'_2315 D

private theorem c2317_sqf   : LeafSqf 2317   := by decide +kernel
private theorem c2317_range : LeafRange 2317  := by decide +kernel
private theorem c2317_ell   : LeafEll 2317    := by decide +kernel
private theorem c2317_nsq   : NSqChkSq 2317   := by decide +kernel
private theorem c2317_har   : HArithChkSq 2317 := by decide +kernel
private theorem c2317_r     : LeafR 2317      := by decide +kernel
private theorem c2317_e'    : LeafE' 2317     := by decide +kernel
private theorem c2317_f1    : LeafF1 2317     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2317_s2    : S2ChkSq 2317    := by decide +kernel
private theorem c2317_s3    : S3ChkSq 2317    := by decide +kernel
private theorem c2317_iso   : LeafIso 2317    := by decide +kernel
private theorem c2317_nof2  : NoF2ChkSq 2317  := by decide +kernel
private theorem c2317_nof3  : NoF3ChkSq 2317  := by decide +kernel
private theorem c2317_nof4z : NoF4zChkSq 2317 := by decide +kernel
theorem C'_2317 : C' 2317 :=
  ⟨c2317_sqf, c2317_range, c2317_ell, leafNSq_of_sq c2317_nsq, leafHAr_of_sq c2317_har,
   c2317_r, c2317_e', c2317_f1, leafS2_of_sq c2317_s2, leafS3_of_sq c2317_s3,
   c2317_iso, leafR8_of_sq c2317_nof2 c2317_nof3 c2317_nof4z⟩
theorem not_tile'_2317 (D : CongruentDissection 2317) : False :=
  not_tile_of_conditions' 2317 C'_2317 D

private theorem c2318_sqf   : LeafSqf 2318   := by decide +kernel
private theorem c2318_range : LeafRange 2318  := by decide +kernel
private theorem c2318_ell   : LeafEll 2318    := by decide +kernel
private theorem c2318_nsq   : NSqChkSq 2318   := by decide +kernel
private theorem c2318_har   : HArithChkSq 2318 := by decide +kernel
private theorem c2318_r     : LeafR 2318      := by decide +kernel
private theorem c2318_e'    : LeafE' 2318     := by decide +kernel
private theorem c2318_f1    : LeafF1 2318     := Or.inl (by decide)
private theorem c2318_s2    : S2ChkSq 2318    := by decide +kernel
private theorem c2318_s3    : S3ChkSq 2318    := by decide +kernel
private theorem c2318_iso   : LeafIso 2318    := by decide +kernel
private theorem c2318_nof2  : NoF2ChkSq 2318  := by decide +kernel
private theorem c2318_nof3  : NoF3ChkSq 2318  := by decide +kernel
private theorem c2318_nof4z : NoF4zChkSq 2318 := by decide +kernel
theorem C'_2318 : C' 2318 :=
  ⟨c2318_sqf, c2318_range, c2318_ell, leafNSq_of_sq c2318_nsq, leafHAr_of_sq c2318_har,
   c2318_r, c2318_e', c2318_f1, leafS2_of_sq c2318_s2, leafS3_of_sq c2318_s3,
   c2318_iso, leafR8_of_sq c2318_nof2 c2318_nof3 c2318_nof4z⟩
theorem not_tile'_2318 (D : CongruentDissection 2318) : False :=
  not_tile_of_conditions' 2318 C'_2318 D

end Erdos634.Draft.AllN2

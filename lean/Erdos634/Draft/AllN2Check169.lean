/- AllN2Check169: N = 3499, 3502, 3503, 3511, 3513
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3499_sqf   : LeafSqf 3499   := by decide +kernel
private theorem c3499_range : LeafRange 3499  := by decide +kernel
private theorem c3499_ell   : LeafEll 3499    := by decide +kernel
private theorem c3499_nsq   : NSqChkSq 3499   := by decide +kernel
private theorem c3499_har   : HArithChkSq 3499 := by decide +kernel
private theorem c3499_r     : LeafR 3499      := by decide +kernel
private theorem c3499_e'    : LeafE' 3499     := by decide +kernel
private theorem c3499_f1    : LeafF1 3499     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3499_s2    : S2ChkSq 3499    := by decide +kernel
private theorem c3499_s3    : S3ChkSq 3499    := by decide +kernel
private theorem c3499_iso   : LeafIso 3499    := by decide +kernel
private theorem c3499_nof2  : NoF2ChkSq 3499  := by decide +kernel
private theorem c3499_nof3  : NoF3ChkSq 3499  := by decide +kernel
private theorem c3499_nof4z : NoF4zChkSq 3499 := by decide +kernel
theorem C'_3499 : C' 3499 :=
  ⟨c3499_sqf, c3499_range, c3499_ell, leafNSq_of_sq c3499_nsq, leafHAr_of_sq c3499_har,
   c3499_r, c3499_e', c3499_f1, leafS2_of_sq c3499_s2, leafS3_of_sq c3499_s3,
   c3499_iso, leafR8_of_sq c3499_nof2 c3499_nof3 c3499_nof4z⟩
theorem not_tile'_3499 (D : CongruentDissection 3499) : False :=
  not_tile_of_conditions' 3499 C'_3499 D

private theorem c3502_sqf   : LeafSqf 3502   := by decide +kernel
private theorem c3502_range : LeafRange 3502  := by decide +kernel
private theorem c3502_ell   : LeafEll 3502    := by decide +kernel
private theorem c3502_nsq   : NSqChkSq 3502   := by decide +kernel
private theorem c3502_har   : HArithChkSq 3502 := by decide +kernel
private theorem c3502_r     : LeafR 3502      := by decide +kernel
private theorem c3502_e'    : LeafE' 3502     := by decide +kernel
private theorem c3502_f1    : LeafF1 3502     := Or.inl (by decide)
private theorem c3502_s2    : S2ChkSq 3502    := by decide +kernel
private theorem c3502_s3    : S3ChkSq 3502    := by decide +kernel
private theorem c3502_iso   : LeafIso 3502    := by decide +kernel
private theorem c3502_nof2  : NoF2ChkSq 3502  := by decide +kernel
private theorem c3502_nof3  : NoF3ChkSq 3502  := by decide +kernel
private theorem c3502_nof4z : NoF4zChkSq 3502 := by decide +kernel
theorem C'_3502 : C' 3502 :=
  ⟨c3502_sqf, c3502_range, c3502_ell, leafNSq_of_sq c3502_nsq, leafHAr_of_sq c3502_har,
   c3502_r, c3502_e', c3502_f1, leafS2_of_sq c3502_s2, leafS3_of_sq c3502_s3,
   c3502_iso, leafR8_of_sq c3502_nof2 c3502_nof3 c3502_nof4z⟩
theorem not_tile'_3502 (D : CongruentDissection 3502) : False :=
  not_tile_of_conditions' 3502 C'_3502 D

private theorem c3503_sqf   : LeafSqf 3503   := by decide +kernel
private theorem c3503_range : LeafRange 3503  := by decide +kernel
private theorem c3503_ell   : LeafEll 3503    := by decide +kernel
private theorem c3503_nsq   : NSqChkSq 3503   := by decide +kernel
private theorem c3503_har   : HArithChkSq 3503 := by decide +kernel
private theorem c3503_r     : LeafR 3503      := by decide +kernel
private theorem c3503_e'    : LeafE' 3503     := by decide +kernel
private theorem c3503_f1    : LeafF1 3503     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3503_s2    : S2ChkSq 3503    := by decide +kernel
private theorem c3503_s3    : S3ChkSq 3503    := by decide +kernel
private theorem c3503_iso   : LeafIso 3503    := by decide +kernel
private theorem c3503_nof2  : NoF2ChkSq 3503  := by decide +kernel
private theorem c3503_nof3  : NoF3ChkSq 3503  := by decide +kernel
private theorem c3503_nof4z : NoF4zChkSq 3503 := by decide +kernel
theorem C'_3503 : C' 3503 :=
  ⟨c3503_sqf, c3503_range, c3503_ell, leafNSq_of_sq c3503_nsq, leafHAr_of_sq c3503_har,
   c3503_r, c3503_e', c3503_f1, leafS2_of_sq c3503_s2, leafS3_of_sq c3503_s3,
   c3503_iso, leafR8_of_sq c3503_nof2 c3503_nof3 c3503_nof4z⟩
theorem not_tile'_3503 (D : CongruentDissection 3503) : False :=
  not_tile_of_conditions' 3503 C'_3503 D

private theorem c3511_sqf   : LeafSqf 3511   := by decide +kernel
private theorem c3511_range : LeafRange 3511  := by decide +kernel
private theorem c3511_ell   : LeafEll 3511    := by decide +kernel
private theorem c3511_nsq   : NSqChkSq 3511   := by decide +kernel
private theorem c3511_har   : HArithChkSq 3511 := by decide +kernel
private theorem c3511_r     : LeafR 3511      := by decide +kernel
private theorem c3511_e'    : LeafE' 3511     := by decide +kernel
private theorem c3511_f1    : LeafF1 3511     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3511_s2    : S2ChkSq 3511    := by decide +kernel
private theorem c3511_s3    : S3ChkSq 3511    := by decide +kernel
private theorem c3511_iso   : LeafIso 3511    := by decide +kernel
private theorem c3511_nof2  : NoF2ChkSq 3511  := by decide +kernel
private theorem c3511_nof3  : NoF3ChkSq 3511  := by decide +kernel
private theorem c3511_nof4z : NoF4zChkSq 3511 := by decide +kernel
theorem C'_3511 : C' 3511 :=
  ⟨c3511_sqf, c3511_range, c3511_ell, leafNSq_of_sq c3511_nsq, leafHAr_of_sq c3511_har,
   c3511_r, c3511_e', c3511_f1, leafS2_of_sq c3511_s2, leafS3_of_sq c3511_s3,
   c3511_iso, leafR8_of_sq c3511_nof2 c3511_nof3 c3511_nof4z⟩
theorem not_tile'_3511 (D : CongruentDissection 3511) : False :=
  not_tile_of_conditions' 3511 C'_3511 D

private theorem c3513_sqf   : LeafSqf 3513   := by decide +kernel
private theorem c3513_range : LeafRange 3513  := by decide +kernel
private theorem c3513_ell   : LeafEll 3513    := by decide +kernel
private theorem c3513_nsq   : NSqChkSq 3513   := by decide +kernel
private theorem c3513_har   : HArithChkSq 3513 := by decide +kernel
private theorem c3513_r     : LeafR 3513      := by decide +kernel
private theorem c3513_e'    : LeafE' 3513     := by decide +kernel
private theorem c3513_f1    : LeafF1 3513     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3513_s2    : S2ChkSq 3513    := by decide +kernel
private theorem c3513_s3    : S3ChkSq 3513    := by decide +kernel
private theorem c3513_iso   : LeafIso 3513    := by decide +kernel
private theorem c3513_nof2  : NoF2ChkSq 3513  := by decide +kernel
private theorem c3513_nof3  : NoF3ChkSq 3513  := by decide +kernel
private theorem c3513_nof4z : NoF4zChkSq 3513 := by decide +kernel
theorem C'_3513 : C' 3513 :=
  ⟨c3513_sqf, c3513_range, c3513_ell, leafNSq_of_sq c3513_nsq, leafHAr_of_sq c3513_har,
   c3513_r, c3513_e', c3513_f1, leafS2_of_sq c3513_s2, leafS3_of_sq c3513_s3,
   c3513_iso, leafR8_of_sq c3513_nof2 c3513_nof3 c3513_nof4z⟩
theorem not_tile'_3513 (D : CongruentDissection 3513) : False :=
  not_tile_of_conditions' 3513 C'_3513 D

end Erdos634.Draft.AllN2

/- AllN2Check164: N = 3426, 3427, 3437, 3439, 3443
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3426_sqf   : LeafSqf 3426   := by decide +kernel
private theorem c3426_range : LeafRange 3426  := by decide +kernel
private theorem c3426_ell   : LeafEll 3426    := by decide +kernel
private theorem c3426_nsq   : NSqChkSq 3426   := by decide +kernel
private theorem c3426_har   : HArithChkSq 3426 := by decide +kernel
private theorem c3426_r     : LeafR 3426      := by decide +kernel
private theorem c3426_e'    : LeafE' 3426     := by decide +kernel
private theorem c3426_f1    : LeafF1 3426     := Or.inl (by decide)
private theorem c3426_s2    : S2ChkSq 3426    := by decide +kernel
private theorem c3426_s3    : S3ChkSq 3426    := by decide +kernel
private theorem c3426_iso   : LeafIso 3426    := by decide +kernel
private theorem c3426_nof2  : NoF2ChkSq 3426  := by decide +kernel
private theorem c3426_nof3  : NoF3ChkSq 3426  := by decide +kernel
private theorem c3426_nof4z : NoF4zChkSq 3426 := by decide +kernel
theorem C'_3426 : C' 3426 :=
  ⟨c3426_sqf, c3426_range, c3426_ell, leafNSq_of_sq c3426_nsq, leafHAr_of_sq c3426_har,
   c3426_r, c3426_e', c3426_f1, leafS2_of_sq c3426_s2, leafS3_of_sq c3426_s3,
   c3426_iso, leafR8_of_sq c3426_nof2 c3426_nof3 c3426_nof4z⟩
theorem not_tile'_3426 (D : CongruentDissection 3426) : False :=
  not_tile_of_conditions' 3426 C'_3426 D

private theorem c3427_sqf   : LeafSqf 3427   := by decide +kernel
private theorem c3427_range : LeafRange 3427  := by decide +kernel
private theorem c3427_ell   : LeafEll 3427    := by decide +kernel
private theorem c3427_nsq   : NSqChkSq 3427   := by decide +kernel
private theorem c3427_har   : HArithChkSq 3427 := by decide +kernel
private theorem c3427_r     : LeafR 3427      := by decide +kernel
private theorem c3427_e'    : LeafE' 3427     := by decide +kernel
private theorem c3427_f1    : LeafF1 3427     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3427_s2    : S2ChkSq 3427    := by decide +kernel
private theorem c3427_s3    : S3ChkSq 3427    := by decide +kernel
private theorem c3427_iso   : LeafIso 3427    := by decide +kernel
private theorem c3427_nof2  : NoF2ChkSq 3427  := by decide +kernel
private theorem c3427_nof3  : NoF3ChkSq 3427  := by decide +kernel
private theorem c3427_nof4z : NoF4zChkSq 3427 := by decide +kernel
theorem C'_3427 : C' 3427 :=
  ⟨c3427_sqf, c3427_range, c3427_ell, leafNSq_of_sq c3427_nsq, leafHAr_of_sq c3427_har,
   c3427_r, c3427_e', c3427_f1, leafS2_of_sq c3427_s2, leafS3_of_sq c3427_s3,
   c3427_iso, leafR8_of_sq c3427_nof2 c3427_nof3 c3427_nof4z⟩
theorem not_tile'_3427 (D : CongruentDissection 3427) : False :=
  not_tile_of_conditions' 3427 C'_3427 D

private theorem c3437_sqf   : LeafSqf 3437   := by decide +kernel
private theorem c3437_range : LeafRange 3437  := by decide +kernel
private theorem c3437_ell   : LeafEll 3437    := by decide +kernel
private theorem c3437_nsq   : NSqChkSq 3437   := by decide +kernel
private theorem c3437_har   : HArithChkSq 3437 := by decide +kernel
private theorem c3437_r     : LeafR 3437      := by decide +kernel
private theorem c3437_e'    : LeafE' 3437     := by decide +kernel
private theorem c3437_f1    : LeafF1 3437     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3437_s2    : S2ChkSq 3437    := by decide +kernel
private theorem c3437_s3    : S3ChkSq 3437    := by decide +kernel
private theorem c3437_iso   : LeafIso 3437    := by decide +kernel
private theorem c3437_nof2  : NoF2ChkSq 3437  := by decide +kernel
private theorem c3437_nof3  : NoF3ChkSq 3437  := by decide +kernel
private theorem c3437_nof4z : NoF4zChkSq 3437 := by decide +kernel
theorem C'_3437 : C' 3437 :=
  ⟨c3437_sqf, c3437_range, c3437_ell, leafNSq_of_sq c3437_nsq, leafHAr_of_sq c3437_har,
   c3437_r, c3437_e', c3437_f1, leafS2_of_sq c3437_s2, leafS3_of_sq c3437_s3,
   c3437_iso, leafR8_of_sq c3437_nof2 c3437_nof3 c3437_nof4z⟩
theorem not_tile'_3437 (D : CongruentDissection 3437) : False :=
  not_tile_of_conditions' 3437 C'_3437 D

private theorem c3439_sqf   : LeafSqf 3439   := by decide +kernel
private theorem c3439_range : LeafRange 3439  := by decide +kernel
private theorem c3439_ell   : LeafEll 3439    := by decide +kernel
private theorem c3439_nsq   : NSqChkSq 3439   := by decide +kernel
private theorem c3439_har   : HArithChkSq 3439 := by decide +kernel
private theorem c3439_r     : LeafR 3439      := by decide +kernel
private theorem c3439_e'    : LeafE' 3439     := by decide +kernel
private theorem c3439_f1    : LeafF1 3439     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3439_s2    : S2ChkSq 3439    := by decide +kernel
private theorem c3439_s3    : S3ChkSq 3439    := by decide +kernel
private theorem c3439_iso   : LeafIso 3439    := by decide +kernel
private theorem c3439_nof2  : NoF2ChkSq 3439  := by decide +kernel
private theorem c3439_nof3  : NoF3ChkSq 3439  := by decide +kernel
private theorem c3439_nof4z : NoF4zChkSq 3439 := by decide +kernel
theorem C'_3439 : C' 3439 :=
  ⟨c3439_sqf, c3439_range, c3439_ell, leafNSq_of_sq c3439_nsq, leafHAr_of_sq c3439_har,
   c3439_r, c3439_e', c3439_f1, leafS2_of_sq c3439_s2, leafS3_of_sq c3439_s3,
   c3439_iso, leafR8_of_sq c3439_nof2 c3439_nof3 c3439_nof4z⟩
theorem not_tile'_3439 (D : CongruentDissection 3439) : False :=
  not_tile_of_conditions' 3439 C'_3439 D

private theorem c3443_sqf   : LeafSqf 3443   := by decide +kernel
private theorem c3443_range : LeafRange 3443  := by decide +kernel
private theorem c3443_ell   : LeafEll 3443    := by decide +kernel
private theorem c3443_nsq   : NSqChkSq 3443   := by decide +kernel
private theorem c3443_har   : HArithChkSq 3443 := by decide +kernel
private theorem c3443_r     : LeafR 3443      := by decide +kernel
private theorem c3443_e'    : LeafE' 3443     := by decide +kernel
private theorem c3443_f1    : LeafF1 3443     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3443_s2    : S2ChkSq 3443    := by decide +kernel
private theorem c3443_s3    : S3ChkSq 3443    := by decide +kernel
private theorem c3443_iso   : LeafIso 3443    := by decide +kernel
private theorem c3443_nof2  : NoF2ChkSq 3443  := by decide +kernel
private theorem c3443_nof3  : NoF3ChkSq 3443  := by decide +kernel
private theorem c3443_nof4z : NoF4zChkSq 3443 := by decide +kernel
theorem C'_3443 : C' 3443 :=
  ⟨c3443_sqf, c3443_range, c3443_ell, leafNSq_of_sq c3443_nsq, leafHAr_of_sq c3443_har,
   c3443_r, c3443_e', c3443_f1, leafS2_of_sq c3443_s2, leafS3_of_sq c3443_s3,
   c3443_iso, leafR8_of_sq c3443_nof2 c3443_nof3 c3443_nof4z⟩
theorem not_tile'_3443 (D : CongruentDissection 3443) : False :=
  not_tile_of_conditions' 3443 C'_3443 D

end Erdos634.Draft.AllN2

/- AllN2Check244: N = 4465, 4466, 4467, 4470, 4471
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4465_sqf   : LeafSqf 4465   := by decide +kernel
private theorem c4465_range : LeafRange 4465  := by decide +kernel
private theorem c4465_ell   : LeafEll 4465    := by decide +kernel
private theorem c4465_nsq   : NSqChkSq 4465   := by decide +kernel
private theorem c4465_har   : HArithChkSq 4465 := by decide +kernel
private theorem c4465_r     : LeafR 4465      := by decide +kernel
private theorem c4465_e'    : LeafE' 4465     := by decide +kernel
private theorem c4465_f1    : LeafF1 4465     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4465_s2    : S2ChkSq 4465    := by decide +kernel
private theorem c4465_s3    : S3ChkSq 4465    := by decide +kernel
private theorem c4465_iso   : LeafIso 4465    := by decide +kernel
private theorem c4465_nof2  : NoF2ChkSq 4465  := by decide +kernel
private theorem c4465_nof3  : NoF3ChkSq 4465  := by decide +kernel
private theorem c4465_nof4z : NoF4zChkSq 4465 := by decide +kernel
theorem C'_4465 : C' 4465 :=
  ⟨c4465_sqf, c4465_range, c4465_ell, leafNSq_of_sq c4465_nsq, leafHAr_of_sq c4465_har,
   c4465_r, c4465_e', c4465_f1, leafS2_of_sq c4465_s2, leafS3_of_sq c4465_s3,
   c4465_iso, leafR8_of_sq c4465_nof2 c4465_nof3 c4465_nof4z⟩
theorem not_tile'_4465 (D : CongruentDissection 4465) : False :=
  not_tile_of_conditions' 4465 C'_4465 D

private theorem c4466_sqf   : LeafSqf 4466   := by decide +kernel
private theorem c4466_range : LeafRange 4466  := by decide +kernel
private theorem c4466_ell   : LeafEll 4466    := by decide +kernel
private theorem c4466_nsq   : NSqChkSq 4466   := by decide +kernel
private theorem c4466_har   : HArithChkSq 4466 := by decide +kernel
private theorem c4466_r     : LeafR 4466      := by decide +kernel
private theorem c4466_e'    : LeafE' 4466     := by decide +kernel
private theorem c4466_f1    : LeafF1 4466     := Or.inl (by decide)
private theorem c4466_s2    : S2ChkSq 4466    := by decide +kernel
private theorem c4466_s3    : S3ChkSq 4466    := by decide +kernel
private theorem c4466_iso   : LeafIso 4466    := by decide +kernel
private theorem c4466_nof2  : NoF2ChkSq 4466  := by decide +kernel
private theorem c4466_nof3  : NoF3ChkSq 4466  := by decide +kernel
private theorem c4466_nof4z : NoF4zChkSq 4466 := by decide +kernel
theorem C'_4466 : C' 4466 :=
  ⟨c4466_sqf, c4466_range, c4466_ell, leafNSq_of_sq c4466_nsq, leafHAr_of_sq c4466_har,
   c4466_r, c4466_e', c4466_f1, leafS2_of_sq c4466_s2, leafS3_of_sq c4466_s3,
   c4466_iso, leafR8_of_sq c4466_nof2 c4466_nof3 c4466_nof4z⟩
theorem not_tile'_4466 (D : CongruentDissection 4466) : False :=
  not_tile_of_conditions' 4466 C'_4466 D

private theorem c4467_sqf   : LeafSqf 4467   := by decide +kernel
private theorem c4467_range : LeafRange 4467  := by decide +kernel
private theorem c4467_ell   : LeafEll 4467    := by decide +kernel
private theorem c4467_nsq   : NSqChkSq 4467   := by decide +kernel
private theorem c4467_har   : HArithChkSq 4467 := by decide +kernel
private theorem c4467_r     : LeafR 4467      := by decide +kernel
private theorem c4467_e'    : LeafE' 4467     := by decide +kernel
private theorem c4467_f1    : LeafF1 4467     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4467_s2    : S2ChkSq 4467    := by decide +kernel
private theorem c4467_s3    : S3ChkSq 4467    := by decide +kernel
private theorem c4467_iso   : LeafIso 4467    := by decide +kernel
private theorem c4467_nof2  : NoF2ChkSq 4467  := by decide +kernel
private theorem c4467_nof3  : NoF3ChkSq 4467  := by decide +kernel
private theorem c4467_nof4z : NoF4zChkSq 4467 := by decide +kernel
theorem C'_4467 : C' 4467 :=
  ⟨c4467_sqf, c4467_range, c4467_ell, leafNSq_of_sq c4467_nsq, leafHAr_of_sq c4467_har,
   c4467_r, c4467_e', c4467_f1, leafS2_of_sq c4467_s2, leafS3_of_sq c4467_s3,
   c4467_iso, leafR8_of_sq c4467_nof2 c4467_nof3 c4467_nof4z⟩
theorem not_tile'_4467 (D : CongruentDissection 4467) : False :=
  not_tile_of_conditions' 4467 C'_4467 D

private theorem c4470_sqf   : LeafSqf 4470   := by decide +kernel
private theorem c4470_range : LeafRange 4470  := by decide +kernel
private theorem c4470_ell   : LeafEll 4470    := by decide +kernel
private theorem c4470_nsq   : NSqChkSq 4470   := by decide +kernel
private theorem c4470_har   : HArithChkSq 4470 := by decide +kernel
private theorem c4470_r     : LeafR 4470      := by decide +kernel
private theorem c4470_e'    : LeafE' 4470     := by decide +kernel
private theorem c4470_f1    : LeafF1 4470     := Or.inl (by decide)
private theorem c4470_s2    : S2ChkSq 4470    := by decide +kernel
private theorem c4470_s3    : S3ChkSq 4470    := by decide +kernel
private theorem c4470_iso   : LeafIso 4470    := by decide +kernel
private theorem c4470_nof2  : NoF2ChkSq 4470  := by decide +kernel
private theorem c4470_nof3  : NoF3ChkSq 4470  := by decide +kernel
private theorem c4470_nof4z : NoF4zChkSq 4470 := by decide +kernel
theorem C'_4470 : C' 4470 :=
  ⟨c4470_sqf, c4470_range, c4470_ell, leafNSq_of_sq c4470_nsq, leafHAr_of_sq c4470_har,
   c4470_r, c4470_e', c4470_f1, leafS2_of_sq c4470_s2, leafS3_of_sq c4470_s3,
   c4470_iso, leafR8_of_sq c4470_nof2 c4470_nof3 c4470_nof4z⟩
theorem not_tile'_4470 (D : CongruentDissection 4470) : False :=
  not_tile_of_conditions' 4470 C'_4470 D

private theorem c4471_sqf   : LeafSqf 4471   := by decide +kernel
private theorem c4471_range : LeafRange 4471  := by decide +kernel
private theorem c4471_ell   : LeafEll 4471    := by decide +kernel
private theorem c4471_nsq   : NSqChkSq 4471   := by decide +kernel
private theorem c4471_har   : HArithChkSq 4471 := by decide +kernel
private theorem c4471_r     : LeafR 4471      := by decide +kernel
private theorem c4471_e'    : LeafE' 4471     := by decide +kernel
private theorem c4471_f1    : LeafF1 4471     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4471_s2    : S2ChkSq 4471    := by decide +kernel
private theorem c4471_s3    : S3ChkSq 4471    := by decide +kernel
private theorem c4471_iso   : LeafIso 4471    := by decide +kernel
private theorem c4471_nof2  : NoF2ChkSq 4471  := by decide +kernel
private theorem c4471_nof3  : NoF3ChkSq 4471  := by decide +kernel
private theorem c4471_nof4z : NoF4zChkSq 4471 := by decide +kernel
theorem C'_4471 : C' 4471 :=
  ⟨c4471_sqf, c4471_range, c4471_ell, leafNSq_of_sq c4471_nsq, leafHAr_of_sq c4471_har,
   c4471_r, c4471_e', c4471_f1, leafS2_of_sq c4471_s2, leafS3_of_sq c4471_s3,
   c4471_iso, leafR8_of_sq c4471_nof2 c4471_nof3 c4471_nof4z⟩
theorem not_tile'_4471 (D : CongruentDissection 4471) : False :=
  not_tile_of_conditions' 4471 C'_4471 D

end Erdos634.Draft.AllN2

/- AllN2Check265: N = 4730, 4735, 4737, 4738, 4739
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4730_sqf   : LeafSqf 4730   := by decide +kernel
private theorem c4730_range : LeafRange 4730  := by decide +kernel
private theorem c4730_ell   : LeafEll 4730    := by decide +kernel
private theorem c4730_nsq   : NSqChkSq 4730   := by decide +kernel
private theorem c4730_har   : HArithChkSq 4730 := by decide +kernel
private theorem c4730_r     : LeafR 4730      := by decide +kernel
private theorem c4730_e'    : LeafE' 4730     := by decide +kernel
private theorem c4730_f1    : LeafF1 4730     := Or.inl (by decide)
private theorem c4730_s2    : S2ChkSq 4730    := by decide +kernel
private theorem c4730_s3    : S3ChkSq 4730    := by decide +kernel
private theorem c4730_iso   : LeafIso 4730    := by decide +kernel
private theorem c4730_nof2  : NoF2ChkSq 4730  := by decide +kernel
private theorem c4730_nof3  : NoF3ChkSq 4730  := by decide +kernel
private theorem c4730_nof4z : NoF4zChkSq 4730 := by decide +kernel
theorem C'_4730 : C' 4730 :=
  ⟨c4730_sqf, c4730_range, c4730_ell, leafNSq_of_sq c4730_nsq, leafHAr_of_sq c4730_har,
   c4730_r, c4730_e', c4730_f1, leafS2_of_sq c4730_s2, leafS3_of_sq c4730_s3,
   c4730_iso, leafR8_of_sq c4730_nof2 c4730_nof3 c4730_nof4z⟩
theorem not_tile'_4730 (D : CongruentDissection 4730) : False :=
  not_tile_of_conditions' 4730 C'_4730 D

private theorem c4735_sqf   : LeafSqf 4735   := by decide +kernel
private theorem c4735_range : LeafRange 4735  := by decide +kernel
private theorem c4735_ell   : LeafEll 4735    := by decide +kernel
private theorem c4735_nsq   : NSqChkSq 4735   := by decide +kernel
private theorem c4735_har   : HArithChkSq 4735 := by decide +kernel
private theorem c4735_r     : LeafR 4735      := by decide +kernel
private theorem c4735_e'    : LeafE' 4735     := by decide +kernel
private theorem c4735_f1    : LeafF1 4735     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4735_s2    : S2ChkSq 4735    := by decide +kernel
private theorem c4735_s3    : S3ChkSq 4735    := by decide +kernel
private theorem c4735_iso   : LeafIso 4735    := by decide +kernel
private theorem c4735_nof2  : NoF2ChkSq 4735  := by decide +kernel
private theorem c4735_nof3  : NoF3ChkSq 4735  := by decide +kernel
private theorem c4735_nof4z : NoF4zChkSq 4735 := by decide +kernel
theorem C'_4735 : C' 4735 :=
  ⟨c4735_sqf, c4735_range, c4735_ell, leafNSq_of_sq c4735_nsq, leafHAr_of_sq c4735_har,
   c4735_r, c4735_e', c4735_f1, leafS2_of_sq c4735_s2, leafS3_of_sq c4735_s3,
   c4735_iso, leafR8_of_sq c4735_nof2 c4735_nof3 c4735_nof4z⟩
theorem not_tile'_4735 (D : CongruentDissection 4735) : False :=
  not_tile_of_conditions' 4735 C'_4735 D

private theorem c4737_sqf   : LeafSqf 4737   := by decide +kernel
private theorem c4737_range : LeafRange 4737  := by decide +kernel
private theorem c4737_ell   : LeafEll 4737    := by decide +kernel
private theorem c4737_nsq   : NSqChkSq 4737   := by decide +kernel
private theorem c4737_har   : HArithChkSq 4737 := by decide +kernel
private theorem c4737_r     : LeafR 4737      := by decide +kernel
private theorem c4737_e'    : LeafE' 4737     := by decide +kernel
private theorem c4737_f1    : LeafF1 4737     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4737_s2    : S2ChkSq 4737    := by decide +kernel
private theorem c4737_s3    : S3ChkSq 4737    := by decide +kernel
private theorem c4737_iso   : LeafIso 4737    := by decide +kernel
private theorem c4737_nof2  : NoF2ChkSq 4737  := by decide +kernel
private theorem c4737_nof3  : NoF3ChkSq 4737  := by decide +kernel
private theorem c4737_nof4z : NoF4zChkSq 4737 := by decide +kernel
theorem C'_4737 : C' 4737 :=
  ⟨c4737_sqf, c4737_range, c4737_ell, leafNSq_of_sq c4737_nsq, leafHAr_of_sq c4737_har,
   c4737_r, c4737_e', c4737_f1, leafS2_of_sq c4737_s2, leafS3_of_sq c4737_s3,
   c4737_iso, leafR8_of_sq c4737_nof2 c4737_nof3 c4737_nof4z⟩
theorem not_tile'_4737 (D : CongruentDissection 4737) : False :=
  not_tile_of_conditions' 4737 C'_4737 D

private theorem c4738_sqf   : LeafSqf 4738   := by decide +kernel
private theorem c4738_range : LeafRange 4738  := by decide +kernel
private theorem c4738_ell   : LeafEll 4738    := by decide +kernel
private theorem c4738_nsq   : NSqChkSq 4738   := by decide +kernel
private theorem c4738_har   : HArithChkSq 4738 := by decide +kernel
private theorem c4738_r     : LeafR 4738      := by decide +kernel
private theorem c4738_e'    : LeafE' 4738     := by decide +kernel
private theorem c4738_f1    : LeafF1 4738     := Or.inl (by decide)
private theorem c4738_s2    : S2ChkSq 4738    := by decide +kernel
private theorem c4738_s3    : S3ChkSq 4738    := by decide +kernel
private theorem c4738_iso   : LeafIso 4738    := by decide +kernel
private theorem c4738_nof2  : NoF2ChkSq 4738  := by decide +kernel
private theorem c4738_nof3  : NoF3ChkSq 4738  := by decide +kernel
private theorem c4738_nof4z : NoF4zChkSq 4738 := by decide +kernel
theorem C'_4738 : C' 4738 :=
  ⟨c4738_sqf, c4738_range, c4738_ell, leafNSq_of_sq c4738_nsq, leafHAr_of_sq c4738_har,
   c4738_r, c4738_e', c4738_f1, leafS2_of_sq c4738_s2, leafS3_of_sq c4738_s3,
   c4738_iso, leafR8_of_sq c4738_nof2 c4738_nof3 c4738_nof4z⟩
theorem not_tile'_4738 (D : CongruentDissection 4738) : False :=
  not_tile_of_conditions' 4738 C'_4738 D

private theorem c4739_sqf   : LeafSqf 4739   := by decide +kernel
private theorem c4739_range : LeafRange 4739  := by decide +kernel
private theorem c4739_ell   : LeafEll 4739    := by decide +kernel
private theorem c4739_nsq   : NSqChkSq 4739   := by decide +kernel
private theorem c4739_har   : HArithChkSq 4739 := by decide +kernel
private theorem c4739_r     : LeafR 4739      := by decide +kernel
private theorem c4739_e'    : LeafE' 4739     := by decide +kernel
private theorem c4739_f1    : LeafF1 4739     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4739_s2    : S2ChkSq 4739    := by decide +kernel
private theorem c4739_s3    : S3ChkSq 4739    := by decide +kernel
private theorem c4739_iso   : LeafIso 4739    := by decide +kernel
private theorem c4739_nof2  : NoF2ChkSq 4739  := by decide +kernel
private theorem c4739_nof3  : NoF3ChkSq 4739  := by decide +kernel
private theorem c4739_nof4z : NoF4zChkSq 4739 := by decide +kernel
theorem C'_4739 : C' 4739 :=
  ⟨c4739_sqf, c4739_range, c4739_ell, leafNSq_of_sq c4739_nsq, leafHAr_of_sq c4739_har,
   c4739_r, c4739_e', c4739_f1, leafS2_of_sq c4739_s2, leafS3_of_sq c4739_s3,
   c4739_iso, leafR8_of_sq c4739_nof2 c4739_nof3 c4739_nof4z⟩
theorem not_tile'_4739 (D : CongruentDissection 4739) : False :=
  not_tile_of_conditions' 4739 C'_4739 D

end Erdos634.Draft.AllN2

/- AllN2Check108: N = 2711, 2717, 2719, 2721, 2723
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2711_sqf   : LeafSqf 2711   := by decide +kernel
private theorem c2711_range : LeafRange 2711  := by decide +kernel
private theorem c2711_ell   : LeafEll 2711    := by decide +kernel
private theorem c2711_nsq   : NSqChkSq 2711   := by decide +kernel
private theorem c2711_har   : HArithChkSq 2711 := by decide +kernel
private theorem c2711_r     : LeafR 2711      := by decide +kernel
private theorem c2711_e'    : LeafE' 2711     := by decide +kernel
private theorem c2711_f1    : LeafF1 2711     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2711_s2    : S2ChkSq 2711    := by decide +kernel
private theorem c2711_s3    : S3ChkSq 2711    := by decide +kernel
private theorem c2711_iso   : LeafIso 2711    := by decide +kernel
private theorem c2711_nof2  : NoF2ChkSq 2711  := by decide +kernel
private theorem c2711_nof3  : NoF3ChkSq 2711  := by decide +kernel
private theorem c2711_nof4z : NoF4zChkSq 2711 := by decide +kernel
theorem C'_2711 : C' 2711 :=
  ⟨c2711_sqf, c2711_range, c2711_ell, leafNSq_of_sq c2711_nsq, leafHAr_of_sq c2711_har,
   c2711_r, c2711_e', c2711_f1, leafS2_of_sq c2711_s2, leafS3_of_sq c2711_s3,
   c2711_iso, leafR8_of_sq c2711_nof2 c2711_nof3 c2711_nof4z⟩
theorem not_tile'_2711 (D : CongruentDissection 2711) : False :=
  not_tile_of_conditions' 2711 C'_2711 D

private theorem c2717_sqf   : LeafSqf 2717   := by decide +kernel
private theorem c2717_range : LeafRange 2717  := by decide +kernel
private theorem c2717_ell   : LeafEll 2717    := by decide +kernel
private theorem c2717_nsq   : NSqChkSq 2717   := by decide +kernel
private theorem c2717_har   : HArithChkSq 2717 := by decide +kernel
private theorem c2717_r     : LeafR 2717      := by decide +kernel
private theorem c2717_e'    : LeafE' 2717     := by decide +kernel
private theorem c2717_f1    : LeafF1 2717     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2717_s2    : S2ChkSq 2717    := by decide +kernel
private theorem c2717_s3    : S3ChkSq 2717    := by decide +kernel
private theorem c2717_iso   : LeafIso 2717    := by decide +kernel
private theorem c2717_nof2  : NoF2ChkSq 2717  := by decide +kernel
private theorem c2717_nof3  : NoF3ChkSq 2717  := by decide +kernel
private theorem c2717_nof4z : NoF4zChkSq 2717 := by decide +kernel
theorem C'_2717 : C' 2717 :=
  ⟨c2717_sqf, c2717_range, c2717_ell, leafNSq_of_sq c2717_nsq, leafHAr_of_sq c2717_har,
   c2717_r, c2717_e', c2717_f1, leafS2_of_sq c2717_s2, leafS3_of_sq c2717_s3,
   c2717_iso, leafR8_of_sq c2717_nof2 c2717_nof3 c2717_nof4z⟩
theorem not_tile'_2717 (D : CongruentDissection 2717) : False :=
  not_tile_of_conditions' 2717 C'_2717 D

private theorem c2719_sqf   : LeafSqf 2719   := by decide +kernel
private theorem c2719_range : LeafRange 2719  := by decide +kernel
private theorem c2719_ell   : LeafEll 2719    := by decide +kernel
private theorem c2719_nsq   : NSqChkSq 2719   := by decide +kernel
private theorem c2719_har   : HArithChkSq 2719 := by decide +kernel
private theorem c2719_r     : LeafR 2719      := by decide +kernel
private theorem c2719_e'    : LeafE' 2719     := by decide +kernel
private theorem c2719_f1    : LeafF1 2719     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2719_s2    : S2ChkSq 2719    := by decide +kernel
private theorem c2719_s3    : S3ChkSq 2719    := by decide +kernel
private theorem c2719_iso   : LeafIso 2719    := by decide +kernel
private theorem c2719_nof2  : NoF2ChkSq 2719  := by decide +kernel
private theorem c2719_nof3  : NoF3ChkSq 2719  := by decide +kernel
private theorem c2719_nof4z : NoF4zChkSq 2719 := by decide +kernel
theorem C'_2719 : C' 2719 :=
  ⟨c2719_sqf, c2719_range, c2719_ell, leafNSq_of_sq c2719_nsq, leafHAr_of_sq c2719_har,
   c2719_r, c2719_e', c2719_f1, leafS2_of_sq c2719_s2, leafS3_of_sq c2719_s3,
   c2719_iso, leafR8_of_sq c2719_nof2 c2719_nof3 c2719_nof4z⟩
theorem not_tile'_2719 (D : CongruentDissection 2719) : False :=
  not_tile_of_conditions' 2719 C'_2719 D

private theorem c2721_sqf   : LeafSqf 2721   := by decide +kernel
private theorem c2721_range : LeafRange 2721  := by decide +kernel
private theorem c2721_ell   : LeafEll 2721    := by decide +kernel
private theorem c2721_nsq   : NSqChkSq 2721   := by decide +kernel
private theorem c2721_har   : HArithChkSq 2721 := by decide +kernel
private theorem c2721_r     : LeafR 2721      := by decide +kernel
private theorem c2721_e'    : LeafE' 2721     := by decide +kernel
private theorem c2721_f1    : LeafF1 2721     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2721_s2    : S2ChkSq 2721    := by decide +kernel
private theorem c2721_s3    : S3ChkSq 2721    := by decide +kernel
private theorem c2721_iso   : LeafIso 2721    := by decide +kernel
private theorem c2721_nof2  : NoF2ChkSq 2721  := by decide +kernel
private theorem c2721_nof3  : NoF3ChkSq 2721  := by decide +kernel
private theorem c2721_nof4z : NoF4zChkSq 2721 := by decide +kernel
theorem C'_2721 : C' 2721 :=
  ⟨c2721_sqf, c2721_range, c2721_ell, leafNSq_of_sq c2721_nsq, leafHAr_of_sq c2721_har,
   c2721_r, c2721_e', c2721_f1, leafS2_of_sq c2721_s2, leafS3_of_sq c2721_s3,
   c2721_iso, leafR8_of_sq c2721_nof2 c2721_nof3 c2721_nof4z⟩
theorem not_tile'_2721 (D : CongruentDissection 2721) : False :=
  not_tile_of_conditions' 2721 C'_2721 D

private theorem c2723_sqf   : LeafSqf 2723   := by decide +kernel
private theorem c2723_range : LeafRange 2723  := by decide +kernel
private theorem c2723_ell   : LeafEll 2723    := by decide +kernel
private theorem c2723_nsq   : NSqChkSq 2723   := by decide +kernel
private theorem c2723_har   : HArithChkSq 2723 := by decide +kernel
private theorem c2723_r     : LeafR 2723      := by decide +kernel
private theorem c2723_e'    : LeafE' 2723     := by decide +kernel
private theorem c2723_f1    : LeafF1 2723     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2723_s2    : S2ChkSq 2723    := by decide +kernel
private theorem c2723_s3    : S3ChkSq 2723    := by decide +kernel
private theorem c2723_iso   : LeafIso 2723    := by decide +kernel
private theorem c2723_nof2  : NoF2ChkSq 2723  := by decide +kernel
private theorem c2723_nof3  : NoF3ChkSq 2723  := by decide +kernel
private theorem c2723_nof4z : NoF4zChkSq 2723 := by decide +kernel
theorem C'_2723 : C' 2723 :=
  ⟨c2723_sqf, c2723_range, c2723_ell, leafNSq_of_sq c2723_nsq, leafHAr_of_sq c2723_har,
   c2723_r, c2723_e', c2723_f1, leafS2_of_sq c2723_s2, leafS3_of_sq c2723_s3,
   c2723_iso, leafR8_of_sq c2723_nof2 c2723_nof3 c2723_nof4z⟩
theorem not_tile'_2723 (D : CongruentDissection 2723) : False :=
  not_tile_of_conditions' 2723 C'_2723 D

end Erdos634.Draft.AllN2

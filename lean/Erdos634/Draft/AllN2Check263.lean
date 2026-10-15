/- AllN2Check263: N = 4703, 4710, 4711, 4713, 4715
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4703_sqf   : LeafSqf 4703   := by decide +kernel
private theorem c4703_range : LeafRange 4703  := by decide +kernel
private theorem c4703_ell   : LeafEll 4703    := by decide +kernel
private theorem c4703_nsq   : NSqChkSq 4703   := by decide +kernel
private theorem c4703_har   : HArithChkSq 4703 := by decide +kernel
private theorem c4703_r     : LeafR 4703      := by decide +kernel
private theorem c4703_e'    : LeafE' 4703     := by decide +kernel
private theorem c4703_f1    : LeafF1 4703     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4703_s2    : S2ChkSq 4703    := by decide +kernel
private theorem c4703_s3    : S3ChkSq 4703    := by decide +kernel
private theorem c4703_iso   : LeafIso 4703    := by decide +kernel
private theorem c4703_nof2  : NoF2ChkSq 4703  := by decide +kernel
private theorem c4703_nof3  : NoF3ChkSq 4703  := by decide +kernel
private theorem c4703_nof4z : NoF4zChkSq 4703 := by decide +kernel
theorem C'_4703 : C' 4703 :=
  ⟨c4703_sqf, c4703_range, c4703_ell, leafNSq_of_sq c4703_nsq, leafHAr_of_sq c4703_har,
   c4703_r, c4703_e', c4703_f1, leafS2_of_sq c4703_s2, leafS3_of_sq c4703_s3,
   c4703_iso, leafR8_of_sq c4703_nof2 c4703_nof3 c4703_nof4z⟩
theorem not_tile'_4703 (D : CongruentDissection 4703) : False :=
  not_tile_of_conditions' 4703 C'_4703 D

private theorem c4710_sqf   : LeafSqf 4710   := by decide +kernel
private theorem c4710_range : LeafRange 4710  := by decide +kernel
private theorem c4710_ell   : LeafEll 4710    := by decide +kernel
private theorem c4710_nsq   : NSqChkSq 4710   := by decide +kernel
private theorem c4710_har   : HArithChkSq 4710 := by decide +kernel
private theorem c4710_r     : LeafR 4710      := by decide +kernel
private theorem c4710_e'    : LeafE' 4710     := by decide +kernel
private theorem c4710_f1    : LeafF1 4710     := Or.inl (by decide)
private theorem c4710_s2    : S2ChkSq 4710    := by decide +kernel
private theorem c4710_s3    : S3ChkSq 4710    := by decide +kernel
private theorem c4710_iso   : LeafIso 4710    := by decide +kernel
private theorem c4710_nof2  : NoF2ChkSq 4710  := by decide +kernel
private theorem c4710_nof3  : NoF3ChkSq 4710  := by decide +kernel
private theorem c4710_nof4z : NoF4zChkSq 4710 := by decide +kernel
theorem C'_4710 : C' 4710 :=
  ⟨c4710_sqf, c4710_range, c4710_ell, leafNSq_of_sq c4710_nsq, leafHAr_of_sq c4710_har,
   c4710_r, c4710_e', c4710_f1, leafS2_of_sq c4710_s2, leafS3_of_sq c4710_s3,
   c4710_iso, leafR8_of_sq c4710_nof2 c4710_nof3 c4710_nof4z⟩
theorem not_tile'_4710 (D : CongruentDissection 4710) : False :=
  not_tile_of_conditions' 4710 C'_4710 D

private theorem c4711_sqf   : LeafSqf 4711   := by decide +kernel
private theorem c4711_range : LeafRange 4711  := by decide +kernel
private theorem c4711_ell   : LeafEll 4711    := by decide +kernel
private theorem c4711_nsq   : NSqChkSq 4711   := by decide +kernel
private theorem c4711_har   : HArithChkSq 4711 := by decide +kernel
private theorem c4711_r     : LeafR 4711      := by decide +kernel
private theorem c4711_e'    : LeafE' 4711     := by decide +kernel
private theorem c4711_f1    : LeafF1 4711     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4711_s2    : S2ChkSq 4711    := by decide +kernel
private theorem c4711_s3    : S3ChkSq 4711    := by decide +kernel
private theorem c4711_iso   : LeafIso 4711    := by decide +kernel
private theorem c4711_nof2  : NoF2ChkSq 4711  := by decide +kernel
private theorem c4711_nof3  : NoF3ChkSq 4711  := by decide +kernel
private theorem c4711_nof4z : NoF4zChkSq 4711 := by decide +kernel
theorem C'_4711 : C' 4711 :=
  ⟨c4711_sqf, c4711_range, c4711_ell, leafNSq_of_sq c4711_nsq, leafHAr_of_sq c4711_har,
   c4711_r, c4711_e', c4711_f1, leafS2_of_sq c4711_s2, leafS3_of_sq c4711_s3,
   c4711_iso, leafR8_of_sq c4711_nof2 c4711_nof3 c4711_nof4z⟩
theorem not_tile'_4711 (D : CongruentDissection 4711) : False :=
  not_tile_of_conditions' 4711 C'_4711 D

private theorem c4713_sqf   : LeafSqf 4713   := by decide +kernel
private theorem c4713_range : LeafRange 4713  := by decide +kernel
private theorem c4713_ell   : LeafEll 4713    := by decide +kernel
private theorem c4713_nsq   : NSqChkSq 4713   := by decide +kernel
private theorem c4713_har   : HArithChkSq 4713 := by decide +kernel
private theorem c4713_r     : LeafR 4713      := by decide +kernel
private theorem c4713_e'    : LeafE' 4713     := by decide +kernel
private theorem c4713_f1    : LeafF1 4713     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4713_s2    : S2ChkSq 4713    := by decide +kernel
private theorem c4713_s3    : S3ChkSq 4713    := by decide +kernel
private theorem c4713_iso   : LeafIso 4713    := by decide +kernel
private theorem c4713_nof2  : NoF2ChkSq 4713  := by decide +kernel
private theorem c4713_nof3  : NoF3ChkSq 4713  := by decide +kernel
private theorem c4713_nof4z : NoF4zChkSq 4713 := by decide +kernel
theorem C'_4713 : C' 4713 :=
  ⟨c4713_sqf, c4713_range, c4713_ell, leafNSq_of_sq c4713_nsq, leafHAr_of_sq c4713_har,
   c4713_r, c4713_e', c4713_f1, leafS2_of_sq c4713_s2, leafS3_of_sq c4713_s3,
   c4713_iso, leafR8_of_sq c4713_nof2 c4713_nof3 c4713_nof4z⟩
theorem not_tile'_4713 (D : CongruentDissection 4713) : False :=
  not_tile_of_conditions' 4713 C'_4713 D

private theorem c4715_sqf   : LeafSqf 4715   := by decide +kernel
private theorem c4715_range : LeafRange 4715  := by decide +kernel
private theorem c4715_ell   : LeafEll 4715    := by decide +kernel
private theorem c4715_nsq   : NSqChkSq 4715   := by decide +kernel
private theorem c4715_har   : HArithChkSq 4715 := by decide +kernel
private theorem c4715_r     : LeafR 4715      := by decide +kernel
private theorem c4715_e'    : LeafE' 4715     := by decide +kernel
private theorem c4715_f1    : LeafF1 4715     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4715_s2    : S2ChkSq 4715    := by decide +kernel
private theorem c4715_s3    : S3ChkSq 4715    := by decide +kernel
private theorem c4715_iso   : LeafIso 4715    := by decide +kernel
private theorem c4715_nof2  : NoF2ChkSq 4715  := by decide +kernel
private theorem c4715_nof3  : NoF3ChkSq 4715  := by decide +kernel
private theorem c4715_nof4z : NoF4zChkSq 4715 := by decide +kernel
theorem C'_4715 : C' 4715 :=
  ⟨c4715_sqf, c4715_range, c4715_ell, leafNSq_of_sq c4715_nsq, leafHAr_of_sq c4715_har,
   c4715_r, c4715_e', c4715_f1, leafS2_of_sq c4715_s2, leafS3_of_sq c4715_s3,
   c4715_iso, leafR8_of_sq c4715_nof2 c4715_nof3 c4715_nof4z⟩
theorem not_tile'_4715 (D : CongruentDissection 4715) : False :=
  not_tile_of_conditions' 4715 C'_4715 D

end Erdos634.Draft.AllN2

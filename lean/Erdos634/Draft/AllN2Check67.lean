/- AllN2Check67: N = 2195, 2198, 2199, 2201, 2202
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2195_sqf   : LeafSqf 2195   := by decide +kernel
private theorem c2195_range : LeafRange 2195  := by decide +kernel
private theorem c2195_ell   : LeafEll 2195    := by decide +kernel
private theorem c2195_nsq   : NSqChkSq 2195   := by decide +kernel
private theorem c2195_har   : HArithChkSq 2195 := by decide +kernel
private theorem c2195_r     : LeafR 2195      := by decide +kernel
private theorem c2195_e'    : LeafE' 2195     := by decide +kernel
private theorem c2195_f1    : LeafF1 2195     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2195_s2    : S2ChkSq 2195    := by decide +kernel
private theorem c2195_s3    : S3ChkSq 2195    := by decide +kernel
private theorem c2195_iso   : LeafIso 2195    := by decide +kernel
private theorem c2195_nof2  : NoF2ChkSq 2195  := by decide +kernel
private theorem c2195_nof3  : NoF3ChkSq 2195  := by decide +kernel
private theorem c2195_nof4z : NoF4zChkSq 2195 := by decide +kernel
theorem C'_2195 : C' 2195 :=
  ⟨c2195_sqf, c2195_range, c2195_ell, leafNSq_of_sq c2195_nsq, leafHAr_of_sq c2195_har,
   c2195_r, c2195_e', c2195_f1, leafS2_of_sq c2195_s2, leafS3_of_sq c2195_s3,
   c2195_iso, leafR8_of_sq c2195_nof2 c2195_nof3 c2195_nof4z⟩
theorem not_tile'_2195 (D : CongruentDissection 2195) : False :=
  not_tile_of_conditions' 2195 C'_2195 D

private theorem c2198_sqf   : LeafSqf 2198   := by decide +kernel
private theorem c2198_range : LeafRange 2198  := by decide +kernel
private theorem c2198_ell   : LeafEll 2198    := by decide +kernel
private theorem c2198_nsq   : NSqChkSq 2198   := by decide +kernel
private theorem c2198_har   : HArithChkSq 2198 := by decide +kernel
private theorem c2198_r     : LeafR 2198      := by decide +kernel
private theorem c2198_e'    : LeafE' 2198     := by decide +kernel
private theorem c2198_f1    : LeafF1 2198     := Or.inl (by decide)
private theorem c2198_s2    : S2ChkSq 2198    := by decide +kernel
private theorem c2198_s3    : S3ChkSq 2198    := by decide +kernel
private theorem c2198_iso   : LeafIso 2198    := by decide +kernel
private theorem c2198_nof2  : NoF2ChkSq 2198  := by decide +kernel
private theorem c2198_nof3  : NoF3ChkSq 2198  := by decide +kernel
private theorem c2198_nof4z : NoF4zChkSq 2198 := by decide +kernel
theorem C'_2198 : C' 2198 :=
  ⟨c2198_sqf, c2198_range, c2198_ell, leafNSq_of_sq c2198_nsq, leafHAr_of_sq c2198_har,
   c2198_r, c2198_e', c2198_f1, leafS2_of_sq c2198_s2, leafS3_of_sq c2198_s3,
   c2198_iso, leafR8_of_sq c2198_nof2 c2198_nof3 c2198_nof4z⟩
theorem not_tile'_2198 (D : CongruentDissection 2198) : False :=
  not_tile_of_conditions' 2198 C'_2198 D

private theorem c2199_sqf   : LeafSqf 2199   := by decide +kernel
private theorem c2199_range : LeafRange 2199  := by decide +kernel
private theorem c2199_ell   : LeafEll 2199    := by decide +kernel
private theorem c2199_nsq   : NSqChkSq 2199   := by decide +kernel
private theorem c2199_har   : HArithChkSq 2199 := by decide +kernel
private theorem c2199_r     : LeafR 2199      := by decide +kernel
private theorem c2199_e'    : LeafE' 2199     := by decide +kernel
private theorem c2199_f1    : LeafF1 2199     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2199_s2    : S2ChkSq 2199    := by decide +kernel
private theorem c2199_s3    : S3ChkSq 2199    := by decide +kernel
private theorem c2199_iso   : LeafIso 2199    := by decide +kernel
private theorem c2199_nof2  : NoF2ChkSq 2199  := by decide +kernel
private theorem c2199_nof3  : NoF3ChkSq 2199  := by decide +kernel
private theorem c2199_nof4z : NoF4zChkSq 2199 := by decide +kernel
theorem C'_2199 : C' 2199 :=
  ⟨c2199_sqf, c2199_range, c2199_ell, leafNSq_of_sq c2199_nsq, leafHAr_of_sq c2199_har,
   c2199_r, c2199_e', c2199_f1, leafS2_of_sq c2199_s2, leafS3_of_sq c2199_s3,
   c2199_iso, leafR8_of_sq c2199_nof2 c2199_nof3 c2199_nof4z⟩
theorem not_tile'_2199 (D : CongruentDissection 2199) : False :=
  not_tile_of_conditions' 2199 C'_2199 D

private theorem c2201_sqf   : LeafSqf 2201   := by decide +kernel
private theorem c2201_range : LeafRange 2201  := by decide +kernel
private theorem c2201_ell   : LeafEll 2201    := by decide +kernel
private theorem c2201_nsq   : NSqChkSq 2201   := by decide +kernel
private theorem c2201_har   : HArithChkSq 2201 := by decide +kernel
private theorem c2201_r     : LeafR 2201      := by decide +kernel
private theorem c2201_e'    : LeafE' 2201     := by decide +kernel
private theorem c2201_f1    : LeafF1 2201     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2201_s2    : S2ChkSq 2201    := by decide +kernel
private theorem c2201_s3    : S3ChkSq 2201    := by decide +kernel
private theorem c2201_iso   : LeafIso 2201    := by decide +kernel
private theorem c2201_nof2  : NoF2ChkSq 2201  := by decide +kernel
private theorem c2201_nof3  : NoF3ChkSq 2201  := by decide +kernel
private theorem c2201_nof4z : NoF4zChkSq 2201 := by decide +kernel
theorem C'_2201 : C' 2201 :=
  ⟨c2201_sqf, c2201_range, c2201_ell, leafNSq_of_sq c2201_nsq, leafHAr_of_sq c2201_har,
   c2201_r, c2201_e', c2201_f1, leafS2_of_sq c2201_s2, leafS3_of_sq c2201_s3,
   c2201_iso, leafR8_of_sq c2201_nof2 c2201_nof3 c2201_nof4z⟩
theorem not_tile'_2201 (D : CongruentDissection 2201) : False :=
  not_tile_of_conditions' 2201 C'_2201 D

private theorem c2202_sqf   : LeafSqf 2202   := by decide +kernel
private theorem c2202_range : LeafRange 2202  := by decide +kernel
private theorem c2202_ell   : LeafEll 2202    := by decide +kernel
private theorem c2202_nsq   : NSqChkSq 2202   := by decide +kernel
private theorem c2202_har   : HArithChkSq 2202 := by decide +kernel
private theorem c2202_r     : LeafR 2202      := by decide +kernel
private theorem c2202_e'    : LeafE' 2202     := by decide +kernel
private theorem c2202_f1    : LeafF1 2202     := Or.inl (by decide)
private theorem c2202_s2    : S2ChkSq 2202    := by decide +kernel
private theorem c2202_s3    : S3ChkSq 2202    := by decide +kernel
private theorem c2202_iso   : LeafIso 2202    := by decide +kernel
private theorem c2202_nof2  : NoF2ChkSq 2202  := by decide +kernel
private theorem c2202_nof3  : NoF3ChkSq 2202  := by decide +kernel
private theorem c2202_nof4z : NoF4zChkSq 2202 := by decide +kernel
theorem C'_2202 : C' 2202 :=
  ⟨c2202_sqf, c2202_range, c2202_ell, leafNSq_of_sq c2202_nsq, leafHAr_of_sq c2202_har,
   c2202_r, c2202_e', c2202_f1, leafS2_of_sq c2202_s2, leafS3_of_sq c2202_s3,
   c2202_iso, leafR8_of_sq c2202_nof2 c2202_nof3 c2202_nof4z⟩
theorem not_tile'_2202 (D : CongruentDissection 2202) : False :=
  not_tile_of_conditions' 2202 C'_2202 D

end Erdos634.Draft.AllN2

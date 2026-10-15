/- AllN2Check65: N = 2174, 2177, 2179, 2181, 2182
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2174_sqf   : LeafSqf 2174   := by decide +kernel
private theorem c2174_range : LeafRange 2174  := by decide +kernel
private theorem c2174_ell   : LeafEll 2174    := by decide +kernel
private theorem c2174_nsq   : NSqChkSq 2174   := by decide +kernel
private theorem c2174_har   : HArithChkSq 2174 := by decide +kernel
private theorem c2174_r     : LeafR 2174      := by decide +kernel
private theorem c2174_e'    : LeafE' 2174     := by decide +kernel
private theorem c2174_f1    : LeafF1 2174     := Or.inl (by decide)
private theorem c2174_s2    : S2ChkSq 2174    := by decide +kernel
private theorem c2174_s3    : S3ChkSq 2174    := by decide +kernel
private theorem c2174_iso   : LeafIso 2174    := by decide +kernel
private theorem c2174_nof2  : NoF2ChkSq 2174  := by decide +kernel
private theorem c2174_nof3  : NoF3ChkSq 2174  := by decide +kernel
private theorem c2174_nof4z : NoF4zChkSq 2174 := by decide +kernel
theorem C'_2174 : C' 2174 :=
  ⟨c2174_sqf, c2174_range, c2174_ell, leafNSq_of_sq c2174_nsq, leafHAr_of_sq c2174_har,
   c2174_r, c2174_e', c2174_f1, leafS2_of_sq c2174_s2, leafS3_of_sq c2174_s3,
   c2174_iso, leafR8_of_sq c2174_nof2 c2174_nof3 c2174_nof4z⟩
theorem not_tile'_2174 (D : CongruentDissection 2174) : False :=
  not_tile_of_conditions' 2174 C'_2174 D

private theorem c2177_sqf   : LeafSqf 2177   := by decide +kernel
private theorem c2177_range : LeafRange 2177  := by decide +kernel
private theorem c2177_ell   : LeafEll 2177    := by decide +kernel
private theorem c2177_nsq   : NSqChkSq 2177   := by decide +kernel
private theorem c2177_har   : HArithChkSq 2177 := by decide +kernel
private theorem c2177_r     : LeafR 2177      := by decide +kernel
private theorem c2177_e'    : LeafE' 2177     := by decide +kernel
private theorem c2177_f1    : LeafF1 2177     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2177_s2    : S2ChkSq 2177    := by decide +kernel
private theorem c2177_s3    : S3ChkSq 2177    := by decide +kernel
private theorem c2177_iso   : LeafIso 2177    := by decide +kernel
private theorem c2177_nof2  : NoF2ChkSq 2177  := by decide +kernel
private theorem c2177_nof3  : NoF3ChkSq 2177  := by decide +kernel
private theorem c2177_nof4z : NoF4zChkSq 2177 := by decide +kernel
theorem C'_2177 : C' 2177 :=
  ⟨c2177_sqf, c2177_range, c2177_ell, leafNSq_of_sq c2177_nsq, leafHAr_of_sq c2177_har,
   c2177_r, c2177_e', c2177_f1, leafS2_of_sq c2177_s2, leafS3_of_sq c2177_s3,
   c2177_iso, leafR8_of_sq c2177_nof2 c2177_nof3 c2177_nof4z⟩
theorem not_tile'_2177 (D : CongruentDissection 2177) : False :=
  not_tile_of_conditions' 2177 C'_2177 D

private theorem c2179_sqf   : LeafSqf 2179   := by decide +kernel
private theorem c2179_range : LeafRange 2179  := by decide +kernel
private theorem c2179_ell   : LeafEll 2179    := by decide +kernel
private theorem c2179_nsq   : NSqChkSq 2179   := by decide +kernel
private theorem c2179_har   : HArithChkSq 2179 := by decide +kernel
private theorem c2179_r     : LeafR 2179      := by decide +kernel
private theorem c2179_e'    : LeafE' 2179     := by decide +kernel
private theorem c2179_f1    : LeafF1 2179     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2179_s2    : S2ChkSq 2179    := by decide +kernel
private theorem c2179_s3    : S3ChkSq 2179    := by decide +kernel
private theorem c2179_iso   : LeafIso 2179    := by decide +kernel
private theorem c2179_nof2  : NoF2ChkSq 2179  := by decide +kernel
private theorem c2179_nof3  : NoF3ChkSq 2179  := by decide +kernel
private theorem c2179_nof4z : NoF4zChkSq 2179 := by decide +kernel
theorem C'_2179 : C' 2179 :=
  ⟨c2179_sqf, c2179_range, c2179_ell, leafNSq_of_sq c2179_nsq, leafHAr_of_sq c2179_har,
   c2179_r, c2179_e', c2179_f1, leafS2_of_sq c2179_s2, leafS3_of_sq c2179_s3,
   c2179_iso, leafR8_of_sq c2179_nof2 c2179_nof3 c2179_nof4z⟩
theorem not_tile'_2179 (D : CongruentDissection 2179) : False :=
  not_tile_of_conditions' 2179 C'_2179 D

private theorem c2181_sqf   : LeafSqf 2181   := by decide +kernel
private theorem c2181_range : LeafRange 2181  := by decide +kernel
private theorem c2181_ell   : LeafEll 2181    := by decide +kernel
private theorem c2181_nsq   : NSqChkSq 2181   := by decide +kernel
private theorem c2181_har   : HArithChkSq 2181 := by decide +kernel
private theorem c2181_r     : LeafR 2181      := by decide +kernel
private theorem c2181_e'    : LeafE' 2181     := by decide +kernel
private theorem c2181_f1    : LeafF1 2181     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2181_s2    : S2ChkSq 2181    := by decide +kernel
private theorem c2181_s3    : S3ChkSq 2181    := by decide +kernel
private theorem c2181_iso   : LeafIso 2181    := by decide +kernel
private theorem c2181_nof2  : NoF2ChkSq 2181  := by decide +kernel
private theorem c2181_nof3  : NoF3ChkSq 2181  := by decide +kernel
private theorem c2181_nof4z : NoF4zChkSq 2181 := by decide +kernel
theorem C'_2181 : C' 2181 :=
  ⟨c2181_sqf, c2181_range, c2181_ell, leafNSq_of_sq c2181_nsq, leafHAr_of_sq c2181_har,
   c2181_r, c2181_e', c2181_f1, leafS2_of_sq c2181_s2, leafS3_of_sq c2181_s3,
   c2181_iso, leafR8_of_sq c2181_nof2 c2181_nof3 c2181_nof4z⟩
theorem not_tile'_2181 (D : CongruentDissection 2181) : False :=
  not_tile_of_conditions' 2181 C'_2181 D

private theorem c2182_sqf   : LeafSqf 2182   := by decide +kernel
private theorem c2182_range : LeafRange 2182  := by decide +kernel
private theorem c2182_ell   : LeafEll 2182    := by decide +kernel
private theorem c2182_nsq   : NSqChkSq 2182   := by decide +kernel
private theorem c2182_har   : HArithChkSq 2182 := by decide +kernel
private theorem c2182_r     : LeafR 2182      := by decide +kernel
private theorem c2182_e'    : LeafE' 2182     := by decide +kernel
private theorem c2182_f1    : LeafF1 2182     := Or.inl (by decide)
private theorem c2182_s2    : S2ChkSq 2182    := by decide +kernel
private theorem c2182_s3    : S3ChkSq 2182    := by decide +kernel
private theorem c2182_iso   : LeafIso 2182    := by decide +kernel
private theorem c2182_nof2  : NoF2ChkSq 2182  := by decide +kernel
private theorem c2182_nof3  : NoF3ChkSq 2182  := by decide +kernel
private theorem c2182_nof4z : NoF4zChkSq 2182 := by decide +kernel
theorem C'_2182 : C' 2182 :=
  ⟨c2182_sqf, c2182_range, c2182_ell, leafNSq_of_sq c2182_nsq, leafHAr_of_sq c2182_har,
   c2182_r, c2182_e', c2182_f1, leafS2_of_sq c2182_s2, leafS3_of_sq c2182_s3,
   c2182_iso, leafR8_of_sq c2182_nof2 c2182_nof3 c2182_nof4z⟩
theorem not_tile'_2182 (D : CongruentDissection 2182) : False :=
  not_tile_of_conditions' 2182 C'_2182 D

end Erdos634.Draft.AllN2

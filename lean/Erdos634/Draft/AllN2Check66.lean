/- AllN2Check66: N = 2183, 2185, 2190, 2191, 2193
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2183_sqf   : LeafSqf 2183   := by decide +kernel
private theorem c2183_range : LeafRange 2183  := by decide +kernel
private theorem c2183_ell   : LeafEll 2183    := by decide +kernel
private theorem c2183_nsq   : NSqChkSq 2183   := by decide +kernel
private theorem c2183_har   : HArithChkSq 2183 := by decide +kernel
private theorem c2183_r     : LeafR 2183      := by decide +kernel
private theorem c2183_e'    : LeafE' 2183     := by decide +kernel
private theorem c2183_f1    : LeafF1 2183     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2183_s2    : S2ChkSq 2183    := by decide +kernel
private theorem c2183_s3    : S3ChkSq 2183    := by decide +kernel
private theorem c2183_iso   : LeafIso 2183    := by decide +kernel
private theorem c2183_nof2  : NoF2ChkSq 2183  := by decide +kernel
private theorem c2183_nof3  : NoF3ChkSq 2183  := by decide +kernel
private theorem c2183_nof4z : NoF4zChkSq 2183 := by decide +kernel
theorem C'_2183 : C' 2183 :=
  ⟨c2183_sqf, c2183_range, c2183_ell, leafNSq_of_sq c2183_nsq, leafHAr_of_sq c2183_har,
   c2183_r, c2183_e', c2183_f1, leafS2_of_sq c2183_s2, leafS3_of_sq c2183_s3,
   c2183_iso, leafR8_of_sq c2183_nof2 c2183_nof3 c2183_nof4z⟩
theorem not_tile'_2183 (D : CongruentDissection 2183) : False :=
  not_tile_of_conditions' 2183 C'_2183 D

private theorem c2185_sqf   : LeafSqf 2185   := by decide +kernel
private theorem c2185_range : LeafRange 2185  := by decide +kernel
private theorem c2185_ell   : LeafEll 2185    := by decide +kernel
private theorem c2185_nsq   : NSqChkSq 2185   := by decide +kernel
private theorem c2185_har   : HArithChkSq 2185 := by decide +kernel
private theorem c2185_r     : LeafR 2185      := by decide +kernel
private theorem c2185_e'    : LeafE' 2185     := by decide +kernel
private theorem c2185_f1    : LeafF1 2185     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2185_s2    : S2ChkSq 2185    := by decide +kernel
private theorem c2185_s3    : S3ChkSq 2185    := by decide +kernel
private theorem c2185_iso   : LeafIso 2185    := by decide +kernel
private theorem c2185_nof2  : NoF2ChkSq 2185  := by decide +kernel
private theorem c2185_nof3  : NoF3ChkSq 2185  := by decide +kernel
private theorem c2185_nof4z : NoF4zChkSq 2185 := by decide +kernel
theorem C'_2185 : C' 2185 :=
  ⟨c2185_sqf, c2185_range, c2185_ell, leafNSq_of_sq c2185_nsq, leafHAr_of_sq c2185_har,
   c2185_r, c2185_e', c2185_f1, leafS2_of_sq c2185_s2, leafS3_of_sq c2185_s3,
   c2185_iso, leafR8_of_sq c2185_nof2 c2185_nof3 c2185_nof4z⟩
theorem not_tile'_2185 (D : CongruentDissection 2185) : False :=
  not_tile_of_conditions' 2185 C'_2185 D

private theorem c2190_sqf   : LeafSqf 2190   := by decide +kernel
private theorem c2190_range : LeafRange 2190  := by decide +kernel
private theorem c2190_ell   : LeafEll 2190    := by decide +kernel
private theorem c2190_nsq   : NSqChkSq 2190   := by decide +kernel
private theorem c2190_har   : HArithChkSq 2190 := by decide +kernel
private theorem c2190_r     : LeafR 2190      := by decide +kernel
private theorem c2190_e'    : LeafE' 2190     := by decide +kernel
private theorem c2190_f1    : LeafF1 2190     := Or.inl (by decide)
private theorem c2190_s2    : S2ChkSq 2190    := by decide +kernel
private theorem c2190_s3    : S3ChkSq 2190    := by decide +kernel
private theorem c2190_iso   : LeafIso 2190    := by decide +kernel
private theorem c2190_nof2  : NoF2ChkSq 2190  := by decide +kernel
private theorem c2190_nof3  : NoF3ChkSq 2190  := by decide +kernel
private theorem c2190_nof4z : NoF4zChkSq 2190 := by decide +kernel
theorem C'_2190 : C' 2190 :=
  ⟨c2190_sqf, c2190_range, c2190_ell, leafNSq_of_sq c2190_nsq, leafHAr_of_sq c2190_har,
   c2190_r, c2190_e', c2190_f1, leafS2_of_sq c2190_s2, leafS3_of_sq c2190_s3,
   c2190_iso, leafR8_of_sq c2190_nof2 c2190_nof3 c2190_nof4z⟩
theorem not_tile'_2190 (D : CongruentDissection 2190) : False :=
  not_tile_of_conditions' 2190 C'_2190 D

private theorem c2191_sqf   : LeafSqf 2191   := by decide +kernel
private theorem c2191_range : LeafRange 2191  := by decide +kernel
private theorem c2191_ell   : LeafEll 2191    := by decide +kernel
private theorem c2191_nsq   : NSqChkSq 2191   := by decide +kernel
private theorem c2191_har   : HArithChkSq 2191 := by decide +kernel
private theorem c2191_r     : LeafR 2191      := by decide +kernel
private theorem c2191_e'    : LeafE' 2191     := by decide +kernel
private theorem c2191_f1    : LeafF1 2191     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2191_s2    : S2ChkSq 2191    := by decide +kernel
private theorem c2191_s3    : S3ChkSq 2191    := by decide +kernel
private theorem c2191_iso   : LeafIso 2191    := by decide +kernel
private theorem c2191_nof2  : NoF2ChkSq 2191  := by decide +kernel
private theorem c2191_nof3  : NoF3ChkSq 2191  := by decide +kernel
private theorem c2191_nof4z : NoF4zChkSq 2191 := by decide +kernel
theorem C'_2191 : C' 2191 :=
  ⟨c2191_sqf, c2191_range, c2191_ell, leafNSq_of_sq c2191_nsq, leafHAr_of_sq c2191_har,
   c2191_r, c2191_e', c2191_f1, leafS2_of_sq c2191_s2, leafS3_of_sq c2191_s3,
   c2191_iso, leafR8_of_sq c2191_nof2 c2191_nof3 c2191_nof4z⟩
theorem not_tile'_2191 (D : CongruentDissection 2191) : False :=
  not_tile_of_conditions' 2191 C'_2191 D

private theorem c2193_sqf   : LeafSqf 2193   := by decide +kernel
private theorem c2193_range : LeafRange 2193  := by decide +kernel
private theorem c2193_ell   : LeafEll 2193    := by decide +kernel
private theorem c2193_nsq   : NSqChkSq 2193   := by decide +kernel
private theorem c2193_har   : HArithChkSq 2193 := by decide +kernel
private theorem c2193_r     : LeafR 2193      := by decide +kernel
private theorem c2193_e'    : LeafE' 2193     := by decide +kernel
private theorem c2193_f1    : LeafF1 2193     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2193_s2    : S2ChkSq 2193    := by decide +kernel
private theorem c2193_s3    : S3ChkSq 2193    := by decide +kernel
private theorem c2193_iso   : LeafIso 2193    := by decide +kernel
private theorem c2193_nof2  : NoF2ChkSq 2193  := by decide +kernel
private theorem c2193_nof3  : NoF3ChkSq 2193  := by decide +kernel
private theorem c2193_nof4z : NoF4zChkSq 2193 := by decide +kernel
theorem C'_2193 : C' 2193 :=
  ⟨c2193_sqf, c2193_range, c2193_ell, leafNSq_of_sq c2193_nsq, leafHAr_of_sq c2193_har,
   c2193_r, c2193_e', c2193_f1, leafS2_of_sq c2193_s2, leafS3_of_sq c2193_s3,
   c2193_iso, leafR8_of_sq c2193_nof2 c2193_nof3 c2193_nof4z⟩
theorem not_tile'_2193 (D : CongruentDissection 2193) : False :=
  not_tile_of_conditions' 2193 C'_2193 D

end Erdos634.Draft.AllN2

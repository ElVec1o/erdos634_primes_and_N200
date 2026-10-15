/- AllN2Check146: N = 3193, 3197, 3199, 3203, 3206
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3193_sqf   : LeafSqf 3193   := by decide +kernel
private theorem c3193_range : LeafRange 3193  := by decide +kernel
private theorem c3193_ell   : LeafEll 3193    := by decide +kernel
private theorem c3193_nsq   : NSqChkSq 3193   := by decide +kernel
private theorem c3193_har   : HArithChkSq 3193 := by decide +kernel
private theorem c3193_r     : LeafR 3193      := by decide +kernel
private theorem c3193_e'    : LeafE' 3193     := by decide +kernel
private theorem c3193_f1    : LeafF1 3193     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3193_s2    : S2ChkSq 3193    := by decide +kernel
private theorem c3193_s3    : S3ChkSq 3193    := by decide +kernel
private theorem c3193_iso   : LeafIso 3193    := by decide +kernel
private theorem c3193_nof2  : NoF2ChkSq 3193  := by decide +kernel
private theorem c3193_nof3  : NoF3ChkSq 3193  := by decide +kernel
private theorem c3193_nof4z : NoF4zChkSq 3193 := by decide +kernel
theorem C'_3193 : C' 3193 :=
  ⟨c3193_sqf, c3193_range, c3193_ell, leafNSq_of_sq c3193_nsq, leafHAr_of_sq c3193_har,
   c3193_r, c3193_e', c3193_f1, leafS2_of_sq c3193_s2, leafS3_of_sq c3193_s3,
   c3193_iso, leafR8_of_sq c3193_nof2 c3193_nof3 c3193_nof4z⟩
theorem not_tile'_3193 (D : CongruentDissection 3193) : False :=
  not_tile_of_conditions' 3193 C'_3193 D

private theorem c3197_sqf   : LeafSqf 3197   := by decide +kernel
private theorem c3197_range : LeafRange 3197  := by decide +kernel
private theorem c3197_ell   : LeafEll 3197    := by decide +kernel
private theorem c3197_nsq   : NSqChkSq 3197   := by decide +kernel
private theorem c3197_har   : HArithChkSq 3197 := by decide +kernel
private theorem c3197_r     : LeafR 3197      := by decide +kernel
private theorem c3197_e'    : LeafE' 3197     := by decide +kernel
private theorem c3197_f1    : LeafF1 3197     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3197_s2    : S2ChkSq 3197    := by decide +kernel
private theorem c3197_s3    : S3ChkSq 3197    := by decide +kernel
private theorem c3197_iso   : LeafIso 3197    := by decide +kernel
private theorem c3197_nof2  : NoF2ChkSq 3197  := by decide +kernel
private theorem c3197_nof3  : NoF3ChkSq 3197  := by decide +kernel
private theorem c3197_nof4z : NoF4zChkSq 3197 := by decide +kernel
theorem C'_3197 : C' 3197 :=
  ⟨c3197_sqf, c3197_range, c3197_ell, leafNSq_of_sq c3197_nsq, leafHAr_of_sq c3197_har,
   c3197_r, c3197_e', c3197_f1, leafS2_of_sq c3197_s2, leafS3_of_sq c3197_s3,
   c3197_iso, leafR8_of_sq c3197_nof2 c3197_nof3 c3197_nof4z⟩
theorem not_tile'_3197 (D : CongruentDissection 3197) : False :=
  not_tile_of_conditions' 3197 C'_3197 D

private theorem c3199_sqf   : LeafSqf 3199   := by decide +kernel
private theorem c3199_range : LeafRange 3199  := by decide +kernel
private theorem c3199_ell   : LeafEll 3199    := by decide +kernel
private theorem c3199_nsq   : NSqChkSq 3199   := by decide +kernel
private theorem c3199_har   : HArithChkSq 3199 := by decide +kernel
private theorem c3199_r     : LeafR 3199      := by decide +kernel
private theorem c3199_e'    : LeafE' 3199     := by decide +kernel
private theorem c3199_f1    : LeafF1 3199     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3199_s2    : S2ChkSq 3199    := by decide +kernel
private theorem c3199_s3    : S3ChkSq 3199    := by decide +kernel
private theorem c3199_iso   : LeafIso 3199    := by decide +kernel
private theorem c3199_nof2  : NoF2ChkSq 3199  := by decide +kernel
private theorem c3199_nof3  : NoF3ChkSq 3199  := by decide +kernel
private theorem c3199_nof4z : NoF4zChkSq 3199 := by decide +kernel
theorem C'_3199 : C' 3199 :=
  ⟨c3199_sqf, c3199_range, c3199_ell, leafNSq_of_sq c3199_nsq, leafHAr_of_sq c3199_har,
   c3199_r, c3199_e', c3199_f1, leafS2_of_sq c3199_s2, leafS3_of_sq c3199_s3,
   c3199_iso, leafR8_of_sq c3199_nof2 c3199_nof3 c3199_nof4z⟩
theorem not_tile'_3199 (D : CongruentDissection 3199) : False :=
  not_tile_of_conditions' 3199 C'_3199 D

private theorem c3203_sqf   : LeafSqf 3203   := by decide +kernel
private theorem c3203_range : LeafRange 3203  := by decide +kernel
private theorem c3203_ell   : LeafEll 3203    := by decide +kernel
private theorem c3203_nsq   : NSqChkSq 3203   := by decide +kernel
private theorem c3203_har   : HArithChkSq 3203 := by decide +kernel
private theorem c3203_r     : LeafR 3203      := by decide +kernel
private theorem c3203_e'    : LeafE' 3203     := by decide +kernel
private theorem c3203_f1    : LeafF1 3203     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3203_s2    : S2ChkSq 3203    := by decide +kernel
private theorem c3203_s3    : S3ChkSq 3203    := by decide +kernel
private theorem c3203_iso   : LeafIso 3203    := by decide +kernel
private theorem c3203_nof2  : NoF2ChkSq 3203  := by decide +kernel
private theorem c3203_nof3  : NoF3ChkSq 3203  := by decide +kernel
private theorem c3203_nof4z : NoF4zChkSq 3203 := by decide +kernel
theorem C'_3203 : C' 3203 :=
  ⟨c3203_sqf, c3203_range, c3203_ell, leafNSq_of_sq c3203_nsq, leafHAr_of_sq c3203_har,
   c3203_r, c3203_e', c3203_f1, leafS2_of_sq c3203_s2, leafS3_of_sq c3203_s3,
   c3203_iso, leafR8_of_sq c3203_nof2 c3203_nof3 c3203_nof4z⟩
theorem not_tile'_3203 (D : CongruentDissection 3203) : False :=
  not_tile_of_conditions' 3203 C'_3203 D

private theorem c3206_sqf   : LeafSqf 3206   := by decide +kernel
private theorem c3206_range : LeafRange 3206  := by decide +kernel
private theorem c3206_ell   : LeafEll 3206    := by decide +kernel
private theorem c3206_nsq   : NSqChkSq 3206   := by decide +kernel
private theorem c3206_har   : HArithChkSq 3206 := by decide +kernel
private theorem c3206_r     : LeafR 3206      := by decide +kernel
private theorem c3206_e'    : LeafE' 3206     := by decide +kernel
private theorem c3206_f1    : LeafF1 3206     := Or.inl (by decide)
private theorem c3206_s2    : S2ChkSq 3206    := by decide +kernel
private theorem c3206_s3    : S3ChkSq 3206    := by decide +kernel
private theorem c3206_iso   : LeafIso 3206    := by decide +kernel
private theorem c3206_nof2  : NoF2ChkSq 3206  := by decide +kernel
private theorem c3206_nof3  : NoF3ChkSq 3206  := by decide +kernel
private theorem c3206_nof4z : NoF4zChkSq 3206 := by decide +kernel
theorem C'_3206 : C' 3206 :=
  ⟨c3206_sqf, c3206_range, c3206_ell, leafNSq_of_sq c3206_nsq, leafHAr_of_sq c3206_har,
   c3206_r, c3206_e', c3206_f1, leafS2_of_sq c3206_s2, leafS3_of_sq c3206_s3,
   c3206_iso, leafR8_of_sq c3206_nof2 c3206_nof3 c3206_nof4z⟩
theorem not_tile'_3206 (D : CongruentDissection 3206) : False :=
  not_tile_of_conditions' 3206 C'_3206 D

end Erdos634.Draft.AllN2

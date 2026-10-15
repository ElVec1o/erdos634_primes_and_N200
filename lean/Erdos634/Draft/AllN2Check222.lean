/- AllN2Check222: N = 4197, 4198, 4199, 4202, 4206
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4197_sqf   : LeafSqf 4197   := by decide +kernel
private theorem c4197_range : LeafRange 4197  := by decide +kernel
private theorem c4197_ell   : LeafEll 4197    := by decide +kernel
private theorem c4197_nsq   : NSqChkSq 4197   := by decide +kernel
private theorem c4197_har   : HArithChkSq 4197 := by decide +kernel
private theorem c4197_r     : LeafR 4197      := by decide +kernel
private theorem c4197_e'    : LeafE' 4197     := by decide +kernel
private theorem c4197_f1    : LeafF1 4197     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4197_s2    : S2ChkSq 4197    := by decide +kernel
private theorem c4197_s3    : S3ChkSq 4197    := by decide +kernel
private theorem c4197_iso   : LeafIso 4197    := by decide +kernel
private theorem c4197_nof2  : NoF2ChkSq 4197  := by decide +kernel
private theorem c4197_nof3  : NoF3ChkSq 4197  := by decide +kernel
private theorem c4197_nof4z : NoF4zChkSq 4197 := by decide +kernel
theorem C'_4197 : C' 4197 :=
  ⟨c4197_sqf, c4197_range, c4197_ell, leafNSq_of_sq c4197_nsq, leafHAr_of_sq c4197_har,
   c4197_r, c4197_e', c4197_f1, leafS2_of_sq c4197_s2, leafS3_of_sq c4197_s3,
   c4197_iso, leafR8_of_sq c4197_nof2 c4197_nof3 c4197_nof4z⟩
theorem not_tile'_4197 (D : CongruentDissection 4197) : False :=
  not_tile_of_conditions' 4197 C'_4197 D

private theorem c4198_sqf   : LeafSqf 4198   := by decide +kernel
private theorem c4198_range : LeafRange 4198  := by decide +kernel
private theorem c4198_ell   : LeafEll 4198    := by decide +kernel
private theorem c4198_nsq   : NSqChkSq 4198   := by decide +kernel
private theorem c4198_har   : HArithChkSq 4198 := by decide +kernel
private theorem c4198_r     : LeafR 4198      := by decide +kernel
private theorem c4198_e'    : LeafE' 4198     := by decide +kernel
private theorem c4198_f1    : LeafF1 4198     := Or.inl (by decide)
private theorem c4198_s2    : S2ChkSq 4198    := by decide +kernel
private theorem c4198_s3    : S3ChkSq 4198    := by decide +kernel
private theorem c4198_iso   : LeafIso 4198    := by decide +kernel
private theorem c4198_nof2  : NoF2ChkSq 4198  := by decide +kernel
private theorem c4198_nof3  : NoF3ChkSq 4198  := by decide +kernel
private theorem c4198_nof4z : NoF4zChkSq 4198 := by decide +kernel
theorem C'_4198 : C' 4198 :=
  ⟨c4198_sqf, c4198_range, c4198_ell, leafNSq_of_sq c4198_nsq, leafHAr_of_sq c4198_har,
   c4198_r, c4198_e', c4198_f1, leafS2_of_sq c4198_s2, leafS3_of_sq c4198_s3,
   c4198_iso, leafR8_of_sq c4198_nof2 c4198_nof3 c4198_nof4z⟩
theorem not_tile'_4198 (D : CongruentDissection 4198) : False :=
  not_tile_of_conditions' 4198 C'_4198 D

private theorem c4199_sqf   : LeafSqf 4199   := by decide +kernel
private theorem c4199_range : LeafRange 4199  := by decide +kernel
private theorem c4199_ell   : LeafEll 4199    := by decide +kernel
private theorem c4199_nsq   : NSqChkSq 4199   := by decide +kernel
private theorem c4199_har   : HArithChkSq 4199 := by decide +kernel
private theorem c4199_r     : LeafR 4199      := by decide +kernel
private theorem c4199_e'    : LeafE' 4199     := by decide +kernel
private theorem c4199_f1    : LeafF1 4199     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4199_s2    : S2ChkSq 4199    := by decide +kernel
private theorem c4199_s3    : S3ChkSq 4199    := by decide +kernel
private theorem c4199_iso   : LeafIso 4199    := by decide +kernel
private theorem c4199_nof2  : NoF2ChkSq 4199  := by decide +kernel
private theorem c4199_nof3  : NoF3ChkSq 4199  := by decide +kernel
private theorem c4199_nof4z : NoF4zChkSq 4199 := by decide +kernel
theorem C'_4199 : C' 4199 :=
  ⟨c4199_sqf, c4199_range, c4199_ell, leafNSq_of_sq c4199_nsq, leafHAr_of_sq c4199_har,
   c4199_r, c4199_e', c4199_f1, leafS2_of_sq c4199_s2, leafS3_of_sq c4199_s3,
   c4199_iso, leafR8_of_sq c4199_nof2 c4199_nof3 c4199_nof4z⟩
theorem not_tile'_4199 (D : CongruentDissection 4199) : False :=
  not_tile_of_conditions' 4199 C'_4199 D

private theorem c4202_sqf   : LeafSqf 4202   := by decide +kernel
private theorem c4202_range : LeafRange 4202  := by decide +kernel
private theorem c4202_ell   : LeafEll 4202    := by decide +kernel
private theorem c4202_nsq   : NSqChkSq 4202   := by decide +kernel
private theorem c4202_har   : HArithChkSq 4202 := by decide +kernel
private theorem c4202_r     : LeafR 4202      := by decide +kernel
private theorem c4202_e'    : LeafE' 4202     := by decide +kernel
private theorem c4202_f1    : LeafF1 4202     := Or.inl (by decide)
private theorem c4202_s2    : S2ChkSq 4202    := by decide +kernel
private theorem c4202_s3    : S3ChkSq 4202    := by decide +kernel
private theorem c4202_iso   : LeafIso 4202    := by decide +kernel
private theorem c4202_nof2  : NoF2ChkSq 4202  := by decide +kernel
private theorem c4202_nof3  : NoF3ChkSq 4202  := by decide +kernel
private theorem c4202_nof4z : NoF4zChkSq 4202 := by decide +kernel
theorem C'_4202 : C' 4202 :=
  ⟨c4202_sqf, c4202_range, c4202_ell, leafNSq_of_sq c4202_nsq, leafHAr_of_sq c4202_har,
   c4202_r, c4202_e', c4202_f1, leafS2_of_sq c4202_s2, leafS3_of_sq c4202_s3,
   c4202_iso, leafR8_of_sq c4202_nof2 c4202_nof3 c4202_nof4z⟩
theorem not_tile'_4202 (D : CongruentDissection 4202) : False :=
  not_tile_of_conditions' 4202 C'_4202 D

private theorem c4206_sqf   : LeafSqf 4206   := by decide +kernel
private theorem c4206_range : LeafRange 4206  := by decide +kernel
private theorem c4206_ell   : LeafEll 4206    := by decide +kernel
private theorem c4206_nsq   : NSqChkSq 4206   := by decide +kernel
private theorem c4206_har   : HArithChkSq 4206 := by decide +kernel
private theorem c4206_r     : LeafR 4206      := by decide +kernel
private theorem c4206_e'    : LeafE' 4206     := by decide +kernel
private theorem c4206_f1    : LeafF1 4206     := Or.inl (by decide)
private theorem c4206_s2    : S2ChkSq 4206    := by decide +kernel
private theorem c4206_s3    : S3ChkSq 4206    := by decide +kernel
private theorem c4206_iso   : LeafIso 4206    := by decide +kernel
private theorem c4206_nof2  : NoF2ChkSq 4206  := by decide +kernel
private theorem c4206_nof3  : NoF3ChkSq 4206  := by decide +kernel
private theorem c4206_nof4z : NoF4zChkSq 4206 := by decide +kernel
theorem C'_4206 : C' 4206 :=
  ⟨c4206_sqf, c4206_range, c4206_ell, leafNSq_of_sq c4206_nsq, leafHAr_of_sq c4206_har,
   c4206_r, c4206_e', c4206_f1, leafS2_of_sq c4206_s2, leafS3_of_sq c4206_s3,
   c4206_iso, leafR8_of_sq c4206_nof2 c4206_nof3 c4206_nof4z⟩
theorem not_tile'_4206 (D : CongruentDissection 4206) : False :=
  not_tile_of_conditions' 4206 C'_4206 D

end Erdos634.Draft.AllN2

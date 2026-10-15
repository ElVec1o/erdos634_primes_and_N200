/- AllN2Check262: N = 4694, 4697, 4699, 4701, 4702
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4694_sqf   : LeafSqf 4694   := by decide +kernel
private theorem c4694_range : LeafRange 4694  := by decide +kernel
private theorem c4694_ell   : LeafEll 4694    := by decide +kernel
private theorem c4694_nsq   : NSqChkSq 4694   := by decide +kernel
private theorem c4694_har   : HArithChkSq 4694 := by decide +kernel
private theorem c4694_r     : LeafR 4694      := by decide +kernel
private theorem c4694_e'    : LeafE' 4694     := by decide +kernel
private theorem c4694_f1    : LeafF1 4694     := Or.inl (by decide)
private theorem c4694_s2    : S2ChkSq 4694    := by decide +kernel
private theorem c4694_s3    : S3ChkSq 4694    := by decide +kernel
private theorem c4694_iso   : LeafIso 4694    := by decide +kernel
private theorem c4694_nof2  : NoF2ChkSq 4694  := by decide +kernel
private theorem c4694_nof3  : NoF3ChkSq 4694  := by decide +kernel
private theorem c4694_nof4z : NoF4zChkSq 4694 := by decide +kernel
theorem C'_4694 : C' 4694 :=
  ⟨c4694_sqf, c4694_range, c4694_ell, leafNSq_of_sq c4694_nsq, leafHAr_of_sq c4694_har,
   c4694_r, c4694_e', c4694_f1, leafS2_of_sq c4694_s2, leafS3_of_sq c4694_s3,
   c4694_iso, leafR8_of_sq c4694_nof2 c4694_nof3 c4694_nof4z⟩
theorem not_tile'_4694 (D : CongruentDissection 4694) : False :=
  not_tile_of_conditions' 4694 C'_4694 D

private theorem c4697_sqf   : LeafSqf 4697   := by decide +kernel
private theorem c4697_range : LeafRange 4697  := by decide +kernel
private theorem c4697_ell   : LeafEll 4697    := by decide +kernel
private theorem c4697_nsq   : NSqChkSq 4697   := by decide +kernel
private theorem c4697_har   : HArithChkSq 4697 := by decide +kernel
private theorem c4697_r     : LeafR 4697      := by decide +kernel
private theorem c4697_e'    : LeafE' 4697     := by decide +kernel
private theorem c4697_f1    : LeafF1 4697     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4697_s2    : S2ChkSq 4697    := by decide +kernel
private theorem c4697_s3    : S3ChkSq 4697    := by decide +kernel
private theorem c4697_iso   : LeafIso 4697    := by decide +kernel
private theorem c4697_nof2  : NoF2ChkSq 4697  := by decide +kernel
private theorem c4697_nof3  : NoF3ChkSq 4697  := by decide +kernel
private theorem c4697_nof4z : NoF4zChkSq 4697 := by decide +kernel
theorem C'_4697 : C' 4697 :=
  ⟨c4697_sqf, c4697_range, c4697_ell, leafNSq_of_sq c4697_nsq, leafHAr_of_sq c4697_har,
   c4697_r, c4697_e', c4697_f1, leafS2_of_sq c4697_s2, leafS3_of_sq c4697_s3,
   c4697_iso, leafR8_of_sq c4697_nof2 c4697_nof3 c4697_nof4z⟩
theorem not_tile'_4697 (D : CongruentDissection 4697) : False :=
  not_tile_of_conditions' 4697 C'_4697 D

private theorem c4699_sqf   : LeafSqf 4699   := by decide +kernel
private theorem c4699_range : LeafRange 4699  := by decide +kernel
private theorem c4699_ell   : LeafEll 4699    := by decide +kernel
private theorem c4699_nsq   : NSqChkSq 4699   := by decide +kernel
private theorem c4699_har   : HArithChkSq 4699 := by decide +kernel
private theorem c4699_r     : LeafR 4699      := by decide +kernel
private theorem c4699_e'    : LeafE' 4699     := by decide +kernel
private theorem c4699_f1    : LeafF1 4699     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4699_s2    : S2ChkSq 4699    := by decide +kernel
private theorem c4699_s3    : S3ChkSq 4699    := by decide +kernel
private theorem c4699_iso   : LeafIso 4699    := by decide +kernel
private theorem c4699_nof2  : NoF2ChkSq 4699  := by decide +kernel
private theorem c4699_nof3  : NoF3ChkSq 4699  := by decide +kernel
private theorem c4699_nof4z : NoF4zChkSq 4699 := by decide +kernel
theorem C'_4699 : C' 4699 :=
  ⟨c4699_sqf, c4699_range, c4699_ell, leafNSq_of_sq c4699_nsq, leafHAr_of_sq c4699_har,
   c4699_r, c4699_e', c4699_f1, leafS2_of_sq c4699_s2, leafS3_of_sq c4699_s3,
   c4699_iso, leafR8_of_sq c4699_nof2 c4699_nof3 c4699_nof4z⟩
theorem not_tile'_4699 (D : CongruentDissection 4699) : False :=
  not_tile_of_conditions' 4699 C'_4699 D

private theorem c4701_sqf   : LeafSqf 4701   := by decide +kernel
private theorem c4701_range : LeafRange 4701  := by decide +kernel
private theorem c4701_ell   : LeafEll 4701    := by decide +kernel
private theorem c4701_nsq   : NSqChkSq 4701   := by decide +kernel
private theorem c4701_har   : HArithChkSq 4701 := by decide +kernel
private theorem c4701_r     : LeafR 4701      := by decide +kernel
private theorem c4701_e'    : LeafE' 4701     := by decide +kernel
private theorem c4701_f1    : LeafF1 4701     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4701_s2    : S2ChkSq 4701    := by decide +kernel
private theorem c4701_s3    : S3ChkSq 4701    := by decide +kernel
private theorem c4701_iso   : LeafIso 4701    := by decide +kernel
private theorem c4701_nof2  : NoF2ChkSq 4701  := by decide +kernel
private theorem c4701_nof3  : NoF3ChkSq 4701  := by decide +kernel
private theorem c4701_nof4z : NoF4zChkSq 4701 := by decide +kernel
theorem C'_4701 : C' 4701 :=
  ⟨c4701_sqf, c4701_range, c4701_ell, leafNSq_of_sq c4701_nsq, leafHAr_of_sq c4701_har,
   c4701_r, c4701_e', c4701_f1, leafS2_of_sq c4701_s2, leafS3_of_sq c4701_s3,
   c4701_iso, leafR8_of_sq c4701_nof2 c4701_nof3 c4701_nof4z⟩
theorem not_tile'_4701 (D : CongruentDissection 4701) : False :=
  not_tile_of_conditions' 4701 C'_4701 D

private theorem c4702_sqf   : LeafSqf 4702   := by decide +kernel
private theorem c4702_range : LeafRange 4702  := by decide +kernel
private theorem c4702_ell   : LeafEll 4702    := by decide +kernel
private theorem c4702_nsq   : NSqChkSq 4702   := by decide +kernel
private theorem c4702_har   : HArithChkSq 4702 := by decide +kernel
private theorem c4702_r     : LeafR 4702      := by decide +kernel
private theorem c4702_e'    : LeafE' 4702     := by decide +kernel
private theorem c4702_f1    : LeafF1 4702     := Or.inl (by decide)
private theorem c4702_s2    : S2ChkSq 4702    := by decide +kernel
private theorem c4702_s3    : S3ChkSq 4702    := by decide +kernel
private theorem c4702_iso   : LeafIso 4702    := by decide +kernel
private theorem c4702_nof2  : NoF2ChkSq 4702  := by decide +kernel
private theorem c4702_nof3  : NoF3ChkSq 4702  := by decide +kernel
private theorem c4702_nof4z : NoF4zChkSq 4702 := by decide +kernel
theorem C'_4702 : C' 4702 :=
  ⟨c4702_sqf, c4702_range, c4702_ell, leafNSq_of_sq c4702_nsq, leafHAr_of_sq c4702_har,
   c4702_r, c4702_e', c4702_f1, leafS2_of_sq c4702_s2, leafS3_of_sq c4702_s3,
   c4702_iso, leafR8_of_sq c4702_nof2 c4702_nof3 c4702_nof4z⟩
theorem not_tile'_4702 (D : CongruentDissection 4702) : False :=
  not_tile_of_conditions' 4702 C'_4702 D

end Erdos634.Draft.AllN2

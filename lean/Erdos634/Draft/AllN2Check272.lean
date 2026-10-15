/- AllN2Check272: N = 4822, 4823, 4826, 4827, 4829
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4822_sqf   : LeafSqf 4822   := by decide +kernel
private theorem c4822_range : LeafRange 4822  := by decide +kernel
private theorem c4822_ell   : LeafEll 4822    := by decide +kernel
private theorem c4822_nsq   : NSqChkSq 4822   := by decide +kernel
private theorem c4822_har   : HArithChkSq 4822 := by decide +kernel
private theorem c4822_r     : LeafR 4822      := by decide +kernel
private theorem c4822_e'    : LeafE' 4822     := by decide +kernel
private theorem c4822_f1    : LeafF1 4822     := Or.inl (by decide)
private theorem c4822_s2    : S2ChkSq 4822    := by decide +kernel
private theorem c4822_s3    : S3ChkSq 4822    := by decide +kernel
private theorem c4822_iso   : LeafIso 4822    := by decide +kernel
private theorem c4822_nof2  : NoF2ChkSq 4822  := by decide +kernel
private theorem c4822_nof3  : NoF3ChkSq 4822  := by decide +kernel
private theorem c4822_nof4z : NoF4zChkSq 4822 := by decide +kernel
theorem C'_4822 : C' 4822 :=
  ⟨c4822_sqf, c4822_range, c4822_ell, leafNSq_of_sq c4822_nsq, leafHAr_of_sq c4822_har,
   c4822_r, c4822_e', c4822_f1, leafS2_of_sq c4822_s2, leafS3_of_sq c4822_s3,
   c4822_iso, leafR8_of_sq c4822_nof2 c4822_nof3 c4822_nof4z⟩
theorem not_tile'_4822 (D : CongruentDissection 4822) : False :=
  not_tile_of_conditions' 4822 C'_4822 D

private theorem c4823_sqf   : LeafSqf 4823   := by decide +kernel
private theorem c4823_range : LeafRange 4823  := by decide +kernel
private theorem c4823_ell   : LeafEll 4823    := by decide +kernel
private theorem c4823_nsq   : NSqChkSq 4823   := by decide +kernel
private theorem c4823_har   : HArithChkSq 4823 := by decide +kernel
private theorem c4823_r     : LeafR 4823      := by decide +kernel
private theorem c4823_e'    : LeafE' 4823     := by decide +kernel
private theorem c4823_f1    : LeafF1 4823     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4823_s2    : S2ChkSq 4823    := by decide +kernel
private theorem c4823_s3    : S3ChkSq 4823    := by decide +kernel
private theorem c4823_iso   : LeafIso 4823    := by decide +kernel
private theorem c4823_nof2  : NoF2ChkSq 4823  := by decide +kernel
private theorem c4823_nof3  : NoF3ChkSq 4823  := by decide +kernel
private theorem c4823_nof4z : NoF4zChkSq 4823 := by decide +kernel
theorem C'_4823 : C' 4823 :=
  ⟨c4823_sqf, c4823_range, c4823_ell, leafNSq_of_sq c4823_nsq, leafHAr_of_sq c4823_har,
   c4823_r, c4823_e', c4823_f1, leafS2_of_sq c4823_s2, leafS3_of_sq c4823_s3,
   c4823_iso, leafR8_of_sq c4823_nof2 c4823_nof3 c4823_nof4z⟩
theorem not_tile'_4823 (D : CongruentDissection 4823) : False :=
  not_tile_of_conditions' 4823 C'_4823 D

private theorem c4826_sqf   : LeafSqf 4826   := by decide +kernel
private theorem c4826_range : LeafRange 4826  := by decide +kernel
private theorem c4826_ell   : LeafEll 4826    := by decide +kernel
private theorem c4826_nsq   : NSqChkSq 4826   := by decide +kernel
private theorem c4826_har   : HArithChkSq 4826 := by decide +kernel
private theorem c4826_r     : LeafR 4826      := by decide +kernel
private theorem c4826_e'    : LeafE' 4826     := by decide +kernel
private theorem c4826_f1    : LeafF1 4826     := Or.inl (by decide)
private theorem c4826_s2    : S2ChkSq 4826    := by decide +kernel
private theorem c4826_s3    : S3ChkSq 4826    := by decide +kernel
private theorem c4826_iso   : LeafIso 4826    := by decide +kernel
private theorem c4826_nof2  : NoF2ChkSq 4826  := by decide +kernel
private theorem c4826_nof3  : NoF3ChkSq 4826  := by decide +kernel
private theorem c4826_nof4z : NoF4zChkSq 4826 := by decide +kernel
theorem C'_4826 : C' 4826 :=
  ⟨c4826_sqf, c4826_range, c4826_ell, leafNSq_of_sq c4826_nsq, leafHAr_of_sq c4826_har,
   c4826_r, c4826_e', c4826_f1, leafS2_of_sq c4826_s2, leafS3_of_sq c4826_s3,
   c4826_iso, leafR8_of_sq c4826_nof2 c4826_nof3 c4826_nof4z⟩
theorem not_tile'_4826 (D : CongruentDissection 4826) : False :=
  not_tile_of_conditions' 4826 C'_4826 D

private theorem c4827_sqf   : LeafSqf 4827   := by decide +kernel
private theorem c4827_range : LeafRange 4827  := by decide +kernel
private theorem c4827_ell   : LeafEll 4827    := by decide +kernel
private theorem c4827_nsq   : NSqChkSq 4827   := by decide +kernel
private theorem c4827_har   : HArithChkSq 4827 := by decide +kernel
private theorem c4827_r     : LeafR 4827      := by decide +kernel
private theorem c4827_e'    : LeafE' 4827     := by decide +kernel
private theorem c4827_f1    : LeafF1 4827     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4827_s2    : S2ChkSq 4827    := by decide +kernel
private theorem c4827_s3    : S3ChkSq 4827    := by decide +kernel
private theorem c4827_iso   : LeafIso 4827    := by decide +kernel
private theorem c4827_nof2  : NoF2ChkSq 4827  := by decide +kernel
private theorem c4827_nof3  : NoF3ChkSq 4827  := by decide +kernel
private theorem c4827_nof4z : NoF4zChkSq 4827 := by decide +kernel
theorem C'_4827 : C' 4827 :=
  ⟨c4827_sqf, c4827_range, c4827_ell, leafNSq_of_sq c4827_nsq, leafHAr_of_sq c4827_har,
   c4827_r, c4827_e', c4827_f1, leafS2_of_sq c4827_s2, leafS3_of_sq c4827_s3,
   c4827_iso, leafR8_of_sq c4827_nof2 c4827_nof3 c4827_nof4z⟩
theorem not_tile'_4827 (D : CongruentDissection 4827) : False :=
  not_tile_of_conditions' 4827 C'_4827 D

private theorem c4829_sqf   : LeafSqf 4829   := by decide +kernel
private theorem c4829_range : LeafRange 4829  := by decide +kernel
private theorem c4829_ell   : LeafEll 4829    := by decide +kernel
private theorem c4829_nsq   : NSqChkSq 4829   := by decide +kernel
private theorem c4829_har   : HArithChkSq 4829 := by decide +kernel
private theorem c4829_r     : LeafR 4829      := by decide +kernel
private theorem c4829_e'    : LeafE' 4829     := by decide +kernel
private theorem c4829_f1    : LeafF1 4829     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4829_s2    : S2ChkSq 4829    := by decide +kernel
private theorem c4829_s3    : S3ChkSq 4829    := by decide +kernel
private theorem c4829_iso   : LeafIso 4829    := by decide +kernel
private theorem c4829_nof2  : NoF2ChkSq 4829  := by decide +kernel
private theorem c4829_nof3  : NoF3ChkSq 4829  := by decide +kernel
private theorem c4829_nof4z : NoF4zChkSq 4829 := by decide +kernel
theorem C'_4829 : C' 4829 :=
  ⟨c4829_sqf, c4829_range, c4829_ell, leafNSq_of_sq c4829_nsq, leafHAr_of_sq c4829_har,
   c4829_r, c4829_e', c4829_f1, leafS2_of_sq c4829_s2, leafS3_of_sq c4829_s3,
   c4829_iso, leafR8_of_sq c4829_nof2 c4829_nof3 c4829_nof4z⟩
theorem not_tile'_4829 (D : CongruentDissection 4829) : False :=
  not_tile_of_conditions' 4829 C'_4829 D

end Erdos634.Draft.AllN2

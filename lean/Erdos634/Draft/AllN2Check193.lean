/- AllN2Check193: N = 3815, 3817, 3823, 3827, 3829
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3815_sqf   : LeafSqf 3815   := by decide +kernel
private theorem c3815_range : LeafRange 3815  := by decide +kernel
private theorem c3815_ell   : LeafEll 3815    := by decide +kernel
private theorem c3815_nsq   : NSqChkSq 3815   := by decide +kernel
private theorem c3815_har   : HArithChkSq 3815 := by decide +kernel
private theorem c3815_r     : LeafR 3815      := by decide +kernel
private theorem c3815_e'    : LeafE' 3815     := by decide +kernel
private theorem c3815_f1    : LeafF1 3815     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3815_s2    : S2ChkSq 3815    := by decide +kernel
private theorem c3815_s3    : S3ChkSq 3815    := by decide +kernel
private theorem c3815_iso   : LeafIso 3815    := by decide +kernel
private theorem c3815_nof2  : NoF2ChkSq 3815  := by decide +kernel
private theorem c3815_nof3  : NoF3ChkSq 3815  := by decide +kernel
private theorem c3815_nof4z : NoF4zChkSq 3815 := by decide +kernel
theorem C'_3815 : C' 3815 :=
  ⟨c3815_sqf, c3815_range, c3815_ell, leafNSq_of_sq c3815_nsq, leafHAr_of_sq c3815_har,
   c3815_r, c3815_e', c3815_f1, leafS2_of_sq c3815_s2, leafS3_of_sq c3815_s3,
   c3815_iso, leafR8_of_sq c3815_nof2 c3815_nof3 c3815_nof4z⟩
theorem not_tile'_3815 (D : CongruentDissection 3815) : False :=
  not_tile_of_conditions' 3815 C'_3815 D

private theorem c3817_sqf   : LeafSqf 3817   := by decide +kernel
private theorem c3817_range : LeafRange 3817  := by decide +kernel
private theorem c3817_ell   : LeafEll 3817    := by decide +kernel
private theorem c3817_nsq   : NSqChkSq 3817   := by decide +kernel
private theorem c3817_har   : HArithChkSq 3817 := by decide +kernel
private theorem c3817_r     : LeafR 3817      := by decide +kernel
private theorem c3817_e'    : LeafE' 3817     := by decide +kernel
private theorem c3817_f1    : LeafF1 3817     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3817_s2    : S2ChkSq 3817    := by decide +kernel
private theorem c3817_s3    : S3ChkSq 3817    := by decide +kernel
private theorem c3817_iso   : LeafIso 3817    := by decide +kernel
private theorem c3817_nof2  : NoF2ChkSq 3817  := by decide +kernel
private theorem c3817_nof3  : NoF3ChkSq 3817  := by decide +kernel
private theorem c3817_nof4z : NoF4zChkSq 3817 := by decide +kernel
theorem C'_3817 : C' 3817 :=
  ⟨c3817_sqf, c3817_range, c3817_ell, leafNSq_of_sq c3817_nsq, leafHAr_of_sq c3817_har,
   c3817_r, c3817_e', c3817_f1, leafS2_of_sq c3817_s2, leafS3_of_sq c3817_s3,
   c3817_iso, leafR8_of_sq c3817_nof2 c3817_nof3 c3817_nof4z⟩
theorem not_tile'_3817 (D : CongruentDissection 3817) : False :=
  not_tile_of_conditions' 3817 C'_3817 D

private theorem c3823_sqf   : LeafSqf 3823   := by decide +kernel
private theorem c3823_range : LeafRange 3823  := by decide +kernel
private theorem c3823_ell   : LeafEll 3823    := by decide +kernel
private theorem c3823_nsq   : NSqChkSq 3823   := by decide +kernel
private theorem c3823_har   : HArithChkSq 3823 := by decide +kernel
private theorem c3823_r     : LeafR 3823      := by decide +kernel
private theorem c3823_e'    : LeafE' 3823     := by decide +kernel
private theorem c3823_f1    : LeafF1 3823     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3823_s2    : S2ChkSq 3823    := by decide +kernel
private theorem c3823_s3    : S3ChkSq 3823    := by decide +kernel
private theorem c3823_iso   : LeafIso 3823    := by decide +kernel
private theorem c3823_nof2  : NoF2ChkSq 3823  := by decide +kernel
private theorem c3823_nof3  : NoF3ChkSq 3823  := by decide +kernel
private theorem c3823_nof4z : NoF4zChkSq 3823 := by decide +kernel
theorem C'_3823 : C' 3823 :=
  ⟨c3823_sqf, c3823_range, c3823_ell, leafNSq_of_sq c3823_nsq, leafHAr_of_sq c3823_har,
   c3823_r, c3823_e', c3823_f1, leafS2_of_sq c3823_s2, leafS3_of_sq c3823_s3,
   c3823_iso, leafR8_of_sq c3823_nof2 c3823_nof3 c3823_nof4z⟩
theorem not_tile'_3823 (D : CongruentDissection 3823) : False :=
  not_tile_of_conditions' 3823 C'_3823 D

private theorem c3827_sqf   : LeafSqf 3827   := by decide +kernel
private theorem c3827_range : LeafRange 3827  := by decide +kernel
private theorem c3827_ell   : LeafEll 3827    := by decide +kernel
private theorem c3827_nsq   : NSqChkSq 3827   := by decide +kernel
private theorem c3827_har   : HArithChkSq 3827 := by decide +kernel
private theorem c3827_r     : LeafR 3827      := by decide +kernel
private theorem c3827_e'    : LeafE' 3827     := by decide +kernel
private theorem c3827_f1    : LeafF1 3827     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3827_s2    : S2ChkSq 3827    := by decide +kernel
private theorem c3827_s3    : S3ChkSq 3827    := by decide +kernel
private theorem c3827_iso   : LeafIso 3827    := by decide +kernel
private theorem c3827_nof2  : NoF2ChkSq 3827  := by decide +kernel
private theorem c3827_nof3  : NoF3ChkSq 3827  := by decide +kernel
private theorem c3827_nof4z : NoF4zChkSq 3827 := by decide +kernel
theorem C'_3827 : C' 3827 :=
  ⟨c3827_sqf, c3827_range, c3827_ell, leafNSq_of_sq c3827_nsq, leafHAr_of_sq c3827_har,
   c3827_r, c3827_e', c3827_f1, leafS2_of_sq c3827_s2, leafS3_of_sq c3827_s3,
   c3827_iso, leafR8_of_sq c3827_nof2 c3827_nof3 c3827_nof4z⟩
theorem not_tile'_3827 (D : CongruentDissection 3827) : False :=
  not_tile_of_conditions' 3827 C'_3827 D

private theorem c3829_sqf   : LeafSqf 3829   := by decide +kernel
private theorem c3829_range : LeafRange 3829  := by decide +kernel
private theorem c3829_ell   : LeafEll 3829    := by decide +kernel
private theorem c3829_nsq   : NSqChkSq 3829   := by decide +kernel
private theorem c3829_har   : HArithChkSq 3829 := by decide +kernel
private theorem c3829_r     : LeafR 3829      := by decide +kernel
private theorem c3829_e'    : LeafE' 3829     := by decide +kernel
private theorem c3829_f1    : LeafF1 3829     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3829_s2    : S2ChkSq 3829    := by decide +kernel
private theorem c3829_s3    : S3ChkSq 3829    := by decide +kernel
private theorem c3829_iso   : LeafIso 3829    := by decide +kernel
private theorem c3829_nof2  : NoF2ChkSq 3829  := by decide +kernel
private theorem c3829_nof3  : NoF3ChkSq 3829  := by decide +kernel
private theorem c3829_nof4z : NoF4zChkSq 3829 := by decide +kernel
theorem C'_3829 : C' 3829 :=
  ⟨c3829_sqf, c3829_range, c3829_ell, leafNSq_of_sq c3829_nsq, leafHAr_of_sq c3829_har,
   c3829_r, c3829_e', c3829_f1, leafS2_of_sq c3829_s2, leafS3_of_sq c3829_s3,
   c3829_iso, leafR8_of_sq c3829_nof2 c3829_nof3 c3829_nof4z⟩
theorem not_tile'_3829 (D : CongruentDissection 3829) : False :=
  not_tile_of_conditions' 3829 C'_3829 D

end Erdos634.Draft.AllN2

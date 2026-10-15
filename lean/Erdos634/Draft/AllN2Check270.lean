/- AllN2Check270: N = 4795, 4798, 4799, 4803, 4807
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4795_sqf   : LeafSqf 4795   := by decide +kernel
private theorem c4795_range : LeafRange 4795  := by decide +kernel
private theorem c4795_ell   : LeafEll 4795    := by decide +kernel
private theorem c4795_nsq   : NSqChkSq 4795   := by decide +kernel
private theorem c4795_har   : HArithChkSq 4795 := by decide +kernel
private theorem c4795_r     : LeafR 4795      := by decide +kernel
private theorem c4795_e'    : LeafE' 4795     := by decide +kernel
private theorem c4795_f1    : LeafF1 4795     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4795_s2    : S2ChkSq 4795    := by decide +kernel
private theorem c4795_s3    : S3ChkSq 4795    := by decide +kernel
private theorem c4795_iso   : LeafIso 4795    := by decide +kernel
private theorem c4795_nof2  : NoF2ChkSq 4795  := by decide +kernel
private theorem c4795_nof3  : NoF3ChkSq 4795  := by decide +kernel
private theorem c4795_nof4z : NoF4zChkSq 4795 := by decide +kernel
theorem C'_4795 : C' 4795 :=
  ⟨c4795_sqf, c4795_range, c4795_ell, leafNSq_of_sq c4795_nsq, leafHAr_of_sq c4795_har,
   c4795_r, c4795_e', c4795_f1, leafS2_of_sq c4795_s2, leafS3_of_sq c4795_s3,
   c4795_iso, leafR8_of_sq c4795_nof2 c4795_nof3 c4795_nof4z⟩
theorem not_tile'_4795 (D : CongruentDissection 4795) : False :=
  not_tile_of_conditions' 4795 C'_4795 D

private theorem c4798_sqf   : LeafSqf 4798   := by decide +kernel
private theorem c4798_range : LeafRange 4798  := by decide +kernel
private theorem c4798_ell   : LeafEll 4798    := by decide +kernel
private theorem c4798_nsq   : NSqChkSq 4798   := by decide +kernel
private theorem c4798_har   : HArithChkSq 4798 := by decide +kernel
private theorem c4798_r     : LeafR 4798      := by decide +kernel
private theorem c4798_e'    : LeafE' 4798     := by decide +kernel
private theorem c4798_f1    : LeafF1 4798     := Or.inl (by decide)
private theorem c4798_s2    : S2ChkSq 4798    := by decide +kernel
private theorem c4798_s3    : S3ChkSq 4798    := by decide +kernel
private theorem c4798_iso   : LeafIso 4798    := by decide +kernel
private theorem c4798_nof2  : NoF2ChkSq 4798  := by decide +kernel
private theorem c4798_nof3  : NoF3ChkSq 4798  := by decide +kernel
private theorem c4798_nof4z : NoF4zChkSq 4798 := by decide +kernel
theorem C'_4798 : C' 4798 :=
  ⟨c4798_sqf, c4798_range, c4798_ell, leafNSq_of_sq c4798_nsq, leafHAr_of_sq c4798_har,
   c4798_r, c4798_e', c4798_f1, leafS2_of_sq c4798_s2, leafS3_of_sq c4798_s3,
   c4798_iso, leafR8_of_sq c4798_nof2 c4798_nof3 c4798_nof4z⟩
theorem not_tile'_4798 (D : CongruentDissection 4798) : False :=
  not_tile_of_conditions' 4798 C'_4798 D

private theorem c4799_sqf   : LeafSqf 4799   := by decide +kernel
private theorem c4799_range : LeafRange 4799  := by decide +kernel
private theorem c4799_ell   : LeafEll 4799    := by decide +kernel
private theorem c4799_nsq   : NSqChkSq 4799   := by decide +kernel
private theorem c4799_har   : HArithChkSq 4799 := by decide +kernel
private theorem c4799_r     : LeafR 4799      := by decide +kernel
private theorem c4799_e'    : LeafE' 4799     := by decide +kernel
private theorem c4799_f1    : LeafF1 4799     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4799_s2    : S2ChkSq 4799    := by decide +kernel
private theorem c4799_s3    : S3ChkSq 4799    := by decide +kernel
private theorem c4799_iso   : LeafIso 4799    := by decide +kernel
private theorem c4799_nof2  : NoF2ChkSq 4799  := by decide +kernel
private theorem c4799_nof3  : NoF3ChkSq 4799  := by decide +kernel
private theorem c4799_nof4z : NoF4zChkSq 4799 := by decide +kernel
theorem C'_4799 : C' 4799 :=
  ⟨c4799_sqf, c4799_range, c4799_ell, leafNSq_of_sq c4799_nsq, leafHAr_of_sq c4799_har,
   c4799_r, c4799_e', c4799_f1, leafS2_of_sq c4799_s2, leafS3_of_sq c4799_s3,
   c4799_iso, leafR8_of_sq c4799_nof2 c4799_nof3 c4799_nof4z⟩
theorem not_tile'_4799 (D : CongruentDissection 4799) : False :=
  not_tile_of_conditions' 4799 C'_4799 D

private theorem c4803_sqf   : LeafSqf 4803   := by decide +kernel
private theorem c4803_range : LeafRange 4803  := by decide +kernel
private theorem c4803_ell   : LeafEll 4803    := by decide +kernel
private theorem c4803_nsq   : NSqChkSq 4803   := by decide +kernel
private theorem c4803_har   : HArithChkSq 4803 := by decide +kernel
private theorem c4803_r     : LeafR 4803      := by decide +kernel
private theorem c4803_e'    : LeafE' 4803     := by decide +kernel
private theorem c4803_f1    : LeafF1 4803     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4803_s2    : S2ChkSq 4803    := by decide +kernel
private theorem c4803_s3    : S3ChkSq 4803    := by decide +kernel
private theorem c4803_iso   : LeafIso 4803    := by decide +kernel
private theorem c4803_nof2  : NoF2ChkSq 4803  := by decide +kernel
private theorem c4803_nof3  : NoF3ChkSq 4803  := by decide +kernel
private theorem c4803_nof4z : NoF4zChkSq 4803 := by decide +kernel
theorem C'_4803 : C' 4803 :=
  ⟨c4803_sqf, c4803_range, c4803_ell, leafNSq_of_sq c4803_nsq, leafHAr_of_sq c4803_har,
   c4803_r, c4803_e', c4803_f1, leafS2_of_sq c4803_s2, leafS3_of_sq c4803_s3,
   c4803_iso, leafR8_of_sq c4803_nof2 c4803_nof3 c4803_nof4z⟩
theorem not_tile'_4803 (D : CongruentDissection 4803) : False :=
  not_tile_of_conditions' 4803 C'_4803 D

private theorem c4807_sqf   : LeafSqf 4807   := by decide +kernel
private theorem c4807_range : LeafRange 4807  := by decide +kernel
private theorem c4807_ell   : LeafEll 4807    := by decide +kernel
private theorem c4807_nsq   : NSqChkSq 4807   := by decide +kernel
private theorem c4807_har   : HArithChkSq 4807 := by decide +kernel
private theorem c4807_r     : LeafR 4807      := by decide +kernel
private theorem c4807_e'    : LeafE' 4807     := by decide +kernel
private theorem c4807_f1    : LeafF1 4807     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4807_s2    : S2ChkSq 4807    := by decide +kernel
private theorem c4807_s3    : S3ChkSq 4807    := by decide +kernel
private theorem c4807_iso   : LeafIso 4807    := by decide +kernel
private theorem c4807_nof2  : NoF2ChkSq 4807  := by decide +kernel
private theorem c4807_nof3  : NoF3ChkSq 4807  := by decide +kernel
private theorem c4807_nof4z : NoF4zChkSq 4807 := by decide +kernel
theorem C'_4807 : C' 4807 :=
  ⟨c4807_sqf, c4807_range, c4807_ell, leafNSq_of_sq c4807_nsq, leafHAr_of_sq c4807_har,
   c4807_r, c4807_e', c4807_f1, leafS2_of_sq c4807_s2, leafS3_of_sq c4807_s3,
   c4807_iso, leafR8_of_sq c4807_nof2 c4807_nof3 c4807_nof4z⟩
theorem not_tile'_4807 (D : CongruentDissection 4807) : False :=
  not_tile_of_conditions' 4807 C'_4807 D

end Erdos634.Draft.AllN2

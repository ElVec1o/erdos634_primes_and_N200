/- AllN2Check195: N = 3839, 3846, 3847, 3849, 3851
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3839_sqf   : LeafSqf 3839   := by decide +kernel
private theorem c3839_range : LeafRange 3839  := by decide +kernel
private theorem c3839_ell   : LeafEll 3839    := by decide +kernel
private theorem c3839_nsq   : NSqChkSq 3839   := by decide +kernel
private theorem c3839_har   : HArithChkSq 3839 := by decide +kernel
private theorem c3839_r     : LeafR 3839      := by decide +kernel
private theorem c3839_e'    : LeafE' 3839     := by decide +kernel
private theorem c3839_f1    : LeafF1 3839     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3839_s2    : S2ChkSq 3839    := by decide +kernel
private theorem c3839_s3    : S3ChkSq 3839    := by decide +kernel
private theorem c3839_iso   : LeafIso 3839    := by decide +kernel
private theorem c3839_nof2  : NoF2ChkSq 3839  := by decide +kernel
private theorem c3839_nof3  : NoF3ChkSq 3839  := by decide +kernel
private theorem c3839_nof4z : NoF4zChkSq 3839 := by decide +kernel
theorem C'_3839 : C' 3839 :=
  ⟨c3839_sqf, c3839_range, c3839_ell, leafNSq_of_sq c3839_nsq, leafHAr_of_sq c3839_har,
   c3839_r, c3839_e', c3839_f1, leafS2_of_sq c3839_s2, leafS3_of_sq c3839_s3,
   c3839_iso, leafR8_of_sq c3839_nof2 c3839_nof3 c3839_nof4z⟩
theorem not_tile'_3839 (D : CongruentDissection 3839) : False :=
  not_tile_of_conditions' 3839 C'_3839 D

private theorem c3846_sqf   : LeafSqf 3846   := by decide +kernel
private theorem c3846_range : LeafRange 3846  := by decide +kernel
private theorem c3846_ell   : LeafEll 3846    := by decide +kernel
private theorem c3846_nsq   : NSqChkSq 3846   := by decide +kernel
private theorem c3846_har   : HArithChkSq 3846 := by decide +kernel
private theorem c3846_r     : LeafR 3846      := by decide +kernel
private theorem c3846_e'    : LeafE' 3846     := by decide +kernel
private theorem c3846_f1    : LeafF1 3846     := Or.inl (by decide)
private theorem c3846_s2    : S2ChkSq 3846    := by decide +kernel
private theorem c3846_s3    : S3ChkSq 3846    := by decide +kernel
private theorem c3846_iso   : LeafIso 3846    := by decide +kernel
private theorem c3846_nof2  : NoF2ChkSq 3846  := by decide +kernel
private theorem c3846_nof3  : NoF3ChkSq 3846  := by decide +kernel
private theorem c3846_nof4z : NoF4zChkSq 3846 := by decide +kernel
theorem C'_3846 : C' 3846 :=
  ⟨c3846_sqf, c3846_range, c3846_ell, leafNSq_of_sq c3846_nsq, leafHAr_of_sq c3846_har,
   c3846_r, c3846_e', c3846_f1, leafS2_of_sq c3846_s2, leafS3_of_sq c3846_s3,
   c3846_iso, leafR8_of_sq c3846_nof2 c3846_nof3 c3846_nof4z⟩
theorem not_tile'_3846 (D : CongruentDissection 3846) : False :=
  not_tile_of_conditions' 3846 C'_3846 D

private theorem c3847_sqf   : LeafSqf 3847   := by decide +kernel
private theorem c3847_range : LeafRange 3847  := by decide +kernel
private theorem c3847_ell   : LeafEll 3847    := by decide +kernel
private theorem c3847_nsq   : NSqChkSq 3847   := by decide +kernel
private theorem c3847_har   : HArithChkSq 3847 := by decide +kernel
private theorem c3847_r     : LeafR 3847      := by decide +kernel
private theorem c3847_e'    : LeafE' 3847     := by decide +kernel
private theorem c3847_f1    : LeafF1 3847     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3847_s2    : S2ChkSq 3847    := by decide +kernel
private theorem c3847_s3    : S3ChkSq 3847    := by decide +kernel
private theorem c3847_iso   : LeafIso 3847    := by decide +kernel
private theorem c3847_nof2  : NoF2ChkSq 3847  := by decide +kernel
private theorem c3847_nof3  : NoF3ChkSq 3847  := by decide +kernel
private theorem c3847_nof4z : NoF4zChkSq 3847 := by decide +kernel
theorem C'_3847 : C' 3847 :=
  ⟨c3847_sqf, c3847_range, c3847_ell, leafNSq_of_sq c3847_nsq, leafHAr_of_sq c3847_har,
   c3847_r, c3847_e', c3847_f1, leafS2_of_sq c3847_s2, leafS3_of_sq c3847_s3,
   c3847_iso, leafR8_of_sq c3847_nof2 c3847_nof3 c3847_nof4z⟩
theorem not_tile'_3847 (D : CongruentDissection 3847) : False :=
  not_tile_of_conditions' 3847 C'_3847 D

private theorem c3849_sqf   : LeafSqf 3849   := by decide +kernel
private theorem c3849_range : LeafRange 3849  := by decide +kernel
private theorem c3849_ell   : LeafEll 3849    := by decide +kernel
private theorem c3849_nsq   : NSqChkSq 3849   := by decide +kernel
private theorem c3849_har   : HArithChkSq 3849 := by decide +kernel
private theorem c3849_r     : LeafR 3849      := by decide +kernel
private theorem c3849_e'    : LeafE' 3849     := by decide +kernel
private theorem c3849_f1    : LeafF1 3849     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3849_s2    : S2ChkSq 3849    := by decide +kernel
private theorem c3849_s3    : S3ChkSq 3849    := by decide +kernel
private theorem c3849_iso   : LeafIso 3849    := by decide +kernel
private theorem c3849_nof2  : NoF2ChkSq 3849  := by decide +kernel
private theorem c3849_nof3  : NoF3ChkSq 3849  := by decide +kernel
private theorem c3849_nof4z : NoF4zChkSq 3849 := by decide +kernel
theorem C'_3849 : C' 3849 :=
  ⟨c3849_sqf, c3849_range, c3849_ell, leafNSq_of_sq c3849_nsq, leafHAr_of_sq c3849_har,
   c3849_r, c3849_e', c3849_f1, leafS2_of_sq c3849_s2, leafS3_of_sq c3849_s3,
   c3849_iso, leafR8_of_sq c3849_nof2 c3849_nof3 c3849_nof4z⟩
theorem not_tile'_3849 (D : CongruentDissection 3849) : False :=
  not_tile_of_conditions' 3849 C'_3849 D

private theorem c3851_sqf   : LeafSqf 3851   := by decide +kernel
private theorem c3851_range : LeafRange 3851  := by decide +kernel
private theorem c3851_ell   : LeafEll 3851    := by decide +kernel
private theorem c3851_nsq   : NSqChkSq 3851   := by decide +kernel
private theorem c3851_har   : HArithChkSq 3851 := by decide +kernel
private theorem c3851_r     : LeafR 3851      := by decide +kernel
private theorem c3851_e'    : LeafE' 3851     := by decide +kernel
private theorem c3851_f1    : LeafF1 3851     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3851_s2    : S2ChkSq 3851    := by decide +kernel
private theorem c3851_s3    : S3ChkSq 3851    := by decide +kernel
private theorem c3851_iso   : LeafIso 3851    := by decide +kernel
private theorem c3851_nof2  : NoF2ChkSq 3851  := by decide +kernel
private theorem c3851_nof3  : NoF3ChkSq 3851  := by decide +kernel
private theorem c3851_nof4z : NoF4zChkSq 3851 := by decide +kernel
theorem C'_3851 : C' 3851 :=
  ⟨c3851_sqf, c3851_range, c3851_ell, leafNSq_of_sq c3851_nsq, leafHAr_of_sq c3851_har,
   c3851_r, c3851_e', c3851_f1, leafS2_of_sq c3851_s2, leafS3_of_sq c3851_s3,
   c3851_iso, leafR8_of_sq c3851_nof2 c3851_nof3 c3851_nof4z⟩
theorem not_tile'_3851 (D : CongruentDissection 3851) : False :=
  not_tile_of_conditions' 3851 C'_3851 D

end Erdos634.Draft.AllN2

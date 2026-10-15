/- AllN2Check46: N = 1837, 1839, 1841, 1851, 1855
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1837_sqf   : LeafSqf 1837   := by decide +kernel
private theorem c1837_range : LeafRange 1837  := by decide +kernel
private theorem c1837_ell   : LeafEll 1837    := by decide +kernel
private theorem c1837_nsq   : NSqChkSq 1837   := by decide +kernel
private theorem c1837_har   : HArithChkSq 1837 := by decide +kernel
private theorem c1837_r     : LeafR 1837      := by decide +kernel
private theorem c1837_e'    : LeafE' 1837     := by decide +kernel
private theorem c1837_f1    : LeafF1 1837     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1837_s2    : S2ChkSq 1837    := by decide +kernel
private theorem c1837_s3    : S3ChkSq 1837    := by decide +kernel
private theorem c1837_iso   : LeafIso 1837    := by decide +kernel
private theorem c1837_nof2  : NoF2ChkSq 1837  := by decide +kernel
private theorem c1837_nof3  : NoF3ChkSq 1837  := by decide +kernel
private theorem c1837_nof4z : NoF4zChkSq 1837 := by decide +kernel
theorem C'_1837 : C' 1837 :=
  ⟨c1837_sqf, c1837_range, c1837_ell, leafNSq_of_sq c1837_nsq, leafHAr_of_sq c1837_har,
   c1837_r, c1837_e', c1837_f1, leafS2_of_sq c1837_s2, leafS3_of_sq c1837_s3,
   c1837_iso, leafR8_of_sq c1837_nof2 c1837_nof3 c1837_nof4z⟩
theorem not_tile'_1837 (D : CongruentDissection 1837) : False :=
  not_tile_of_conditions' 1837 C'_1837 D

private theorem c1839_sqf   : LeafSqf 1839   := by decide +kernel
private theorem c1839_range : LeafRange 1839  := by decide +kernel
private theorem c1839_ell   : LeafEll 1839    := by decide +kernel
private theorem c1839_nsq   : NSqChkSq 1839   := by decide +kernel
private theorem c1839_har   : HArithChkSq 1839 := by decide +kernel
private theorem c1839_r     : LeafR 1839      := by decide +kernel
private theorem c1839_e'    : LeafE' 1839     := by decide +kernel
private theorem c1839_f1    : LeafF1 1839     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1839_s2    : S2ChkSq 1839    := by decide +kernel
private theorem c1839_s3    : S3ChkSq 1839    := by decide +kernel
private theorem c1839_iso   : LeafIso 1839    := by decide +kernel
private theorem c1839_nof2  : NoF2ChkSq 1839  := by decide +kernel
private theorem c1839_nof3  : NoF3ChkSq 1839  := by decide +kernel
private theorem c1839_nof4z : NoF4zChkSq 1839 := by decide +kernel
theorem C'_1839 : C' 1839 :=
  ⟨c1839_sqf, c1839_range, c1839_ell, leafNSq_of_sq c1839_nsq, leafHAr_of_sq c1839_har,
   c1839_r, c1839_e', c1839_f1, leafS2_of_sq c1839_s2, leafS3_of_sq c1839_s3,
   c1839_iso, leafR8_of_sq c1839_nof2 c1839_nof3 c1839_nof4z⟩
theorem not_tile'_1839 (D : CongruentDissection 1839) : False :=
  not_tile_of_conditions' 1839 C'_1839 D

private theorem c1841_sqf   : LeafSqf 1841   := by decide +kernel
private theorem c1841_range : LeafRange 1841  := by decide +kernel
private theorem c1841_ell   : LeafEll 1841    := by decide +kernel
private theorem c1841_nsq   : NSqChkSq 1841   := by decide +kernel
private theorem c1841_har   : HArithChkSq 1841 := by decide +kernel
private theorem c1841_r     : LeafR 1841      := by decide +kernel
private theorem c1841_e'    : LeafE' 1841     := by decide +kernel
private theorem c1841_f1    : LeafF1 1841     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1841_s2    : S2ChkSq 1841    := by decide +kernel
private theorem c1841_s3    : S3ChkSq 1841    := by decide +kernel
private theorem c1841_iso   : LeafIso 1841    := by decide +kernel
private theorem c1841_nof2  : NoF2ChkSq 1841  := by decide +kernel
private theorem c1841_nof3  : NoF3ChkSq 1841  := by decide +kernel
private theorem c1841_nof4z : NoF4zChkSq 1841 := by decide +kernel
theorem C'_1841 : C' 1841 :=
  ⟨c1841_sqf, c1841_range, c1841_ell, leafNSq_of_sq c1841_nsq, leafHAr_of_sq c1841_har,
   c1841_r, c1841_e', c1841_f1, leafS2_of_sq c1841_s2, leafS3_of_sq c1841_s3,
   c1841_iso, leafR8_of_sq c1841_nof2 c1841_nof3 c1841_nof4z⟩
theorem not_tile'_1841 (D : CongruentDissection 1841) : False :=
  not_tile_of_conditions' 1841 C'_1841 D

private theorem c1851_sqf   : LeafSqf 1851   := by decide +kernel
private theorem c1851_range : LeafRange 1851  := by decide +kernel
private theorem c1851_ell   : LeafEll 1851    := by decide +kernel
private theorem c1851_nsq   : NSqChkSq 1851   := by decide +kernel
private theorem c1851_har   : HArithChkSq 1851 := by decide +kernel
private theorem c1851_r     : LeafR 1851      := by decide +kernel
private theorem c1851_e'    : LeafE' 1851     := by decide +kernel
private theorem c1851_f1    : LeafF1 1851     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1851_s2    : S2ChkSq 1851    := by decide +kernel
private theorem c1851_s3    : S3ChkSq 1851    := by decide +kernel
private theorem c1851_iso   : LeafIso 1851    := by decide +kernel
private theorem c1851_nof2  : NoF2ChkSq 1851  := by decide +kernel
private theorem c1851_nof3  : NoF3ChkSq 1851  := by decide +kernel
private theorem c1851_nof4z : NoF4zChkSq 1851 := by decide +kernel
theorem C'_1851 : C' 1851 :=
  ⟨c1851_sqf, c1851_range, c1851_ell, leafNSq_of_sq c1851_nsq, leafHAr_of_sq c1851_har,
   c1851_r, c1851_e', c1851_f1, leafS2_of_sq c1851_s2, leafS3_of_sq c1851_s3,
   c1851_iso, leafR8_of_sq c1851_nof2 c1851_nof3 c1851_nof4z⟩
theorem not_tile'_1851 (D : CongruentDissection 1851) : False :=
  not_tile_of_conditions' 1851 C'_1851 D

private theorem c1855_sqf   : LeafSqf 1855   := by decide +kernel
private theorem c1855_range : LeafRange 1855  := by decide +kernel
private theorem c1855_ell   : LeafEll 1855    := by decide +kernel
private theorem c1855_nsq   : NSqChkSq 1855   := by decide +kernel
private theorem c1855_har   : HArithChkSq 1855 := by decide +kernel
private theorem c1855_r     : LeafR 1855      := by decide +kernel
private theorem c1855_e'    : LeafE' 1855     := by decide +kernel
private theorem c1855_f1    : LeafF1 1855     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1855_s2    : S2ChkSq 1855    := by decide +kernel
private theorem c1855_s3    : S3ChkSq 1855    := by decide +kernel
private theorem c1855_iso   : LeafIso 1855    := by decide +kernel
private theorem c1855_nof2  : NoF2ChkSq 1855  := by decide +kernel
private theorem c1855_nof3  : NoF3ChkSq 1855  := by decide +kernel
private theorem c1855_nof4z : NoF4zChkSq 1855 := by decide +kernel
theorem C'_1855 : C' 1855 :=
  ⟨c1855_sqf, c1855_range, c1855_ell, leafNSq_of_sq c1855_nsq, leafHAr_of_sq c1855_har,
   c1855_r, c1855_e', c1855_f1, leafS2_of_sq c1855_s2, leafS3_of_sq c1855_s3,
   c1855_iso, leafR8_of_sq c1855_nof2 c1855_nof3 c1855_nof4z⟩
theorem not_tile'_1855 (D : CongruentDissection 1855) : False :=
  not_tile_of_conditions' 1855 C'_1855 D

end Erdos634.Draft.AllN2

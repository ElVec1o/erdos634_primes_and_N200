/- AllN2Check197: N = 3863, 3867, 3873, 3878, 3882
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3863_sqf   : LeafSqf 3863   := by decide +kernel
private theorem c3863_range : LeafRange 3863  := by decide +kernel
private theorem c3863_ell   : LeafEll 3863    := by decide +kernel
private theorem c3863_nsq   : NSqChkSq 3863   := by decide +kernel
private theorem c3863_har   : HArithChkSq 3863 := by decide +kernel
private theorem c3863_r     : LeafR 3863      := by decide +kernel
private theorem c3863_e'    : LeafE' 3863     := by decide +kernel
private theorem c3863_f1    : LeafF1 3863     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3863_s2    : S2ChkSq 3863    := by decide +kernel
private theorem c3863_s3    : S3ChkSq 3863    := by decide +kernel
private theorem c3863_iso   : LeafIso 3863    := by decide +kernel
private theorem c3863_nof2  : NoF2ChkSq 3863  := by decide +kernel
private theorem c3863_nof3  : NoF3ChkSq 3863  := by decide +kernel
private theorem c3863_nof4z : NoF4zChkSq 3863 := by decide +kernel
theorem C'_3863 : C' 3863 :=
  ⟨c3863_sqf, c3863_range, c3863_ell, leafNSq_of_sq c3863_nsq, leafHAr_of_sq c3863_har,
   c3863_r, c3863_e', c3863_f1, leafS2_of_sq c3863_s2, leafS3_of_sq c3863_s3,
   c3863_iso, leafR8_of_sq c3863_nof2 c3863_nof3 c3863_nof4z⟩
theorem not_tile'_3863 (D : CongruentDissection 3863) : False :=
  not_tile_of_conditions' 3863 C'_3863 D

private theorem c3867_sqf   : LeafSqf 3867   := by decide +kernel
private theorem c3867_range : LeafRange 3867  := by decide +kernel
private theorem c3867_ell   : LeafEll 3867    := by decide +kernel
private theorem c3867_nsq   : NSqChkSq 3867   := by decide +kernel
private theorem c3867_har   : HArithChkSq 3867 := by decide +kernel
private theorem c3867_r     : LeafR 3867      := by decide +kernel
private theorem c3867_e'    : LeafE' 3867     := by decide +kernel
private theorem c3867_f1    : LeafF1 3867     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3867_s2    : S2ChkSq 3867    := by decide +kernel
private theorem c3867_s3    : S3ChkSq 3867    := by decide +kernel
private theorem c3867_iso   : LeafIso 3867    := by decide +kernel
private theorem c3867_nof2  : NoF2ChkSq 3867  := by decide +kernel
private theorem c3867_nof3  : NoF3ChkSq 3867  := by decide +kernel
private theorem c3867_nof4z : NoF4zChkSq 3867 := by decide +kernel
theorem C'_3867 : C' 3867 :=
  ⟨c3867_sqf, c3867_range, c3867_ell, leafNSq_of_sq c3867_nsq, leafHAr_of_sq c3867_har,
   c3867_r, c3867_e', c3867_f1, leafS2_of_sq c3867_s2, leafS3_of_sq c3867_s3,
   c3867_iso, leafR8_of_sq c3867_nof2 c3867_nof3 c3867_nof4z⟩
theorem not_tile'_3867 (D : CongruentDissection 3867) : False :=
  not_tile_of_conditions' 3867 C'_3867 D

private theorem c3873_sqf   : LeafSqf 3873   := by decide +kernel
private theorem c3873_range : LeafRange 3873  := by decide +kernel
private theorem c3873_ell   : LeafEll 3873    := by decide +kernel
private theorem c3873_nsq   : NSqChkSq 3873   := by decide +kernel
private theorem c3873_har   : HArithChkSq 3873 := by decide +kernel
private theorem c3873_r     : LeafR 3873      := by decide +kernel
private theorem c3873_e'    : LeafE' 3873     := by decide +kernel
private theorem c3873_f1    : LeafF1 3873     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3873_s2    : S2ChkSq 3873    := by decide +kernel
private theorem c3873_s3    : S3ChkSq 3873    := by decide +kernel
private theorem c3873_iso   : LeafIso 3873    := by decide +kernel
private theorem c3873_nof2  : NoF2ChkSq 3873  := by decide +kernel
private theorem c3873_nof3  : NoF3ChkSq 3873  := by decide +kernel
private theorem c3873_nof4z : NoF4zChkSq 3873 := by decide +kernel
theorem C'_3873 : C' 3873 :=
  ⟨c3873_sqf, c3873_range, c3873_ell, leafNSq_of_sq c3873_nsq, leafHAr_of_sq c3873_har,
   c3873_r, c3873_e', c3873_f1, leafS2_of_sq c3873_s2, leafS3_of_sq c3873_s3,
   c3873_iso, leafR8_of_sq c3873_nof2 c3873_nof3 c3873_nof4z⟩
theorem not_tile'_3873 (D : CongruentDissection 3873) : False :=
  not_tile_of_conditions' 3873 C'_3873 D

private theorem c3878_sqf   : LeafSqf 3878   := by decide +kernel
private theorem c3878_range : LeafRange 3878  := by decide +kernel
private theorem c3878_ell   : LeafEll 3878    := by decide +kernel
private theorem c3878_nsq   : NSqChkSq 3878   := by decide +kernel
private theorem c3878_har   : HArithChkSq 3878 := by decide +kernel
private theorem c3878_r     : LeafR 3878      := by decide +kernel
private theorem c3878_e'    : LeafE' 3878     := by decide +kernel
private theorem c3878_f1    : LeafF1 3878     := Or.inl (by decide)
private theorem c3878_s2    : S2ChkSq 3878    := by decide +kernel
private theorem c3878_s3    : S3ChkSq 3878    := by decide +kernel
private theorem c3878_iso   : LeafIso 3878    := by decide +kernel
private theorem c3878_nof2  : NoF2ChkSq 3878  := by decide +kernel
private theorem c3878_nof3  : NoF3ChkSq 3878  := by decide +kernel
private theorem c3878_nof4z : NoF4zChkSq 3878 := by decide +kernel
theorem C'_3878 : C' 3878 :=
  ⟨c3878_sqf, c3878_range, c3878_ell, leafNSq_of_sq c3878_nsq, leafHAr_of_sq c3878_har,
   c3878_r, c3878_e', c3878_f1, leafS2_of_sq c3878_s2, leafS3_of_sq c3878_s3,
   c3878_iso, leafR8_of_sq c3878_nof2 c3878_nof3 c3878_nof4z⟩
theorem not_tile'_3878 (D : CongruentDissection 3878) : False :=
  not_tile_of_conditions' 3878 C'_3878 D

private theorem c3882_sqf   : LeafSqf 3882   := by decide +kernel
private theorem c3882_range : LeafRange 3882  := by decide +kernel
private theorem c3882_ell   : LeafEll 3882    := by decide +kernel
private theorem c3882_nsq   : NSqChkSq 3882   := by decide +kernel
private theorem c3882_har   : HArithChkSq 3882 := by decide +kernel
private theorem c3882_r     : LeafR 3882      := by decide +kernel
private theorem c3882_e'    : LeafE' 3882     := by decide +kernel
private theorem c3882_f1    : LeafF1 3882     := Or.inl (by decide)
private theorem c3882_s2    : S2ChkSq 3882    := by decide +kernel
private theorem c3882_s3    : S3ChkSq 3882    := by decide +kernel
private theorem c3882_iso   : LeafIso 3882    := by decide +kernel
private theorem c3882_nof2  : NoF2ChkSq 3882  := by decide +kernel
private theorem c3882_nof3  : NoF3ChkSq 3882  := by decide +kernel
private theorem c3882_nof4z : NoF4zChkSq 3882 := by decide +kernel
theorem C'_3882 : C' 3882 :=
  ⟨c3882_sqf, c3882_range, c3882_ell, leafNSq_of_sq c3882_nsq, leafHAr_of_sq c3882_har,
   c3882_r, c3882_e', c3882_f1, leafS2_of_sq c3882_s2, leafS3_of_sq c3882_s3,
   c3882_iso, leafR8_of_sq c3882_nof2 c3882_nof3 c3882_nof4z⟩
theorem not_tile'_3882 (D : CongruentDissection 3882) : False :=
  not_tile_of_conditions' 3882 C'_3882 D

end Erdos634.Draft.AllN2

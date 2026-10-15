/- AllN2Check277: N = 4870, 4871, 4873, 4879, 4881
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4870_sqf   : LeafSqf 4870   := by decide +kernel
private theorem c4870_range : LeafRange 4870  := by decide +kernel
private theorem c4870_ell   : LeafEll 4870    := by decide +kernel
private theorem c4870_nsq   : NSqChkSq 4870   := by decide +kernel
private theorem c4870_har   : HArithChkSq 4870 := by decide +kernel
private theorem c4870_r     : LeafR 4870      := by decide +kernel
private theorem c4870_e'    : LeafE' 4870     := by decide +kernel
private theorem c4870_f1    : LeafF1 4870     := Or.inl (by decide)
private theorem c4870_s2    : S2ChkSq 4870    := by decide +kernel
private theorem c4870_s3    : S3ChkSq 4870    := by decide +kernel
private theorem c4870_iso   : LeafIso 4870    := by decide +kernel
private theorem c4870_nof2  : NoF2ChkSq 4870  := by decide +kernel
private theorem c4870_nof3  : NoF3ChkSq 4870  := by decide +kernel
private theorem c4870_nof4z : NoF4zChkSq 4870 := by decide +kernel
theorem C'_4870 : C' 4870 :=
  ⟨c4870_sqf, c4870_range, c4870_ell, leafNSq_of_sq c4870_nsq, leafHAr_of_sq c4870_har,
   c4870_r, c4870_e', c4870_f1, leafS2_of_sq c4870_s2, leafS3_of_sq c4870_s3,
   c4870_iso, leafR8_of_sq c4870_nof2 c4870_nof3 c4870_nof4z⟩
theorem not_tile'_4870 (D : CongruentDissection 4870) : False :=
  not_tile_of_conditions' 4870 C'_4870 D

private theorem c4871_sqf   : LeafSqf 4871   := by decide +kernel
private theorem c4871_range : LeafRange 4871  := by decide +kernel
private theorem c4871_ell   : LeafEll 4871    := by decide +kernel
private theorem c4871_nsq   : NSqChkSq 4871   := by decide +kernel
private theorem c4871_har   : HArithChkSq 4871 := by decide +kernel
private theorem c4871_r     : LeafR 4871      := by decide +kernel
private theorem c4871_e'    : LeafE' 4871     := by decide +kernel
private theorem c4871_f1    : LeafF1 4871     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4871_s2    : S2ChkSq 4871    := by decide +kernel
private theorem c4871_s3    : S3ChkSq 4871    := by decide +kernel
private theorem c4871_iso   : LeafIso 4871    := by decide +kernel
private theorem c4871_nof2  : NoF2ChkSq 4871  := by decide +kernel
private theorem c4871_nof3  : NoF3ChkSq 4871  := by decide +kernel
private theorem c4871_nof4z : NoF4zChkSq 4871 := by decide +kernel
theorem C'_4871 : C' 4871 :=
  ⟨c4871_sqf, c4871_range, c4871_ell, leafNSq_of_sq c4871_nsq, leafHAr_of_sq c4871_har,
   c4871_r, c4871_e', c4871_f1, leafS2_of_sq c4871_s2, leafS3_of_sq c4871_s3,
   c4871_iso, leafR8_of_sq c4871_nof2 c4871_nof3 c4871_nof4z⟩
theorem not_tile'_4871 (D : CongruentDissection 4871) : False :=
  not_tile_of_conditions' 4871 C'_4871 D

private theorem c4873_sqf   : LeafSqf 4873   := by decide +kernel
private theorem c4873_range : LeafRange 4873  := by decide +kernel
private theorem c4873_ell   : LeafEll 4873    := by decide +kernel
private theorem c4873_nsq   : NSqChkSq 4873   := by decide +kernel
private theorem c4873_har   : HArithChkSq 4873 := by decide +kernel
private theorem c4873_r     : LeafR 4873      := by decide +kernel
private theorem c4873_e'    : LeafE' 4873     := by decide +kernel
private theorem c4873_f1    : LeafF1 4873     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4873_s2    : S2ChkSq 4873    := by decide +kernel
private theorem c4873_s3    : S3ChkSq 4873    := by decide +kernel
private theorem c4873_iso   : LeafIso 4873    := by decide +kernel
private theorem c4873_nof2  : NoF2ChkSq 4873  := by decide +kernel
private theorem c4873_nof3  : NoF3ChkSq 4873  := by decide +kernel
private theorem c4873_nof4z : NoF4zChkSq 4873 := by decide +kernel
theorem C'_4873 : C' 4873 :=
  ⟨c4873_sqf, c4873_range, c4873_ell, leafNSq_of_sq c4873_nsq, leafHAr_of_sq c4873_har,
   c4873_r, c4873_e', c4873_f1, leafS2_of_sq c4873_s2, leafS3_of_sq c4873_s3,
   c4873_iso, leafR8_of_sq c4873_nof2 c4873_nof3 c4873_nof4z⟩
theorem not_tile'_4873 (D : CongruentDissection 4873) : False :=
  not_tile_of_conditions' 4873 C'_4873 D

private theorem c4879_sqf   : LeafSqf 4879   := by decide +kernel
private theorem c4879_range : LeafRange 4879  := by decide +kernel
private theorem c4879_ell   : LeafEll 4879    := by decide +kernel
private theorem c4879_nsq   : NSqChkSq 4879   := by decide +kernel
private theorem c4879_har   : HArithChkSq 4879 := by decide +kernel
private theorem c4879_r     : LeafR 4879      := by decide +kernel
private theorem c4879_e'    : LeafE' 4879     := by decide +kernel
private theorem c4879_f1    : LeafF1 4879     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4879_s2    : S2ChkSq 4879    := by decide +kernel
private theorem c4879_s3    : S3ChkSq 4879    := by decide +kernel
private theorem c4879_iso   : LeafIso 4879    := by decide +kernel
private theorem c4879_nof2  : NoF2ChkSq 4879  := by decide +kernel
private theorem c4879_nof3  : NoF3ChkSq 4879  := by decide +kernel
private theorem c4879_nof4z : NoF4zChkSq 4879 := by decide +kernel
theorem C'_4879 : C' 4879 :=
  ⟨c4879_sqf, c4879_range, c4879_ell, leafNSq_of_sq c4879_nsq, leafHAr_of_sq c4879_har,
   c4879_r, c4879_e', c4879_f1, leafS2_of_sq c4879_s2, leafS3_of_sq c4879_s3,
   c4879_iso, leafR8_of_sq c4879_nof2 c4879_nof3 c4879_nof4z⟩
theorem not_tile'_4879 (D : CongruentDissection 4879) : False :=
  not_tile_of_conditions' 4879 C'_4879 D

private theorem c4881_sqf   : LeafSqf 4881   := by decide +kernel
private theorem c4881_range : LeafRange 4881  := by decide +kernel
private theorem c4881_ell   : LeafEll 4881    := by decide +kernel
private theorem c4881_nsq   : NSqChkSq 4881   := by decide +kernel
private theorem c4881_har   : HArithChkSq 4881 := by decide +kernel
private theorem c4881_r     : LeafR 4881      := by decide +kernel
private theorem c4881_e'    : LeafE' 4881     := by decide +kernel
private theorem c4881_f1    : LeafF1 4881     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4881_s2    : S2ChkSq 4881    := by decide +kernel
private theorem c4881_s3    : S3ChkSq 4881    := by decide +kernel
private theorem c4881_iso   : LeafIso 4881    := by decide +kernel
private theorem c4881_nof2  : NoF2ChkSq 4881  := by decide +kernel
private theorem c4881_nof3  : NoF3ChkSq 4881  := by decide +kernel
private theorem c4881_nof4z : NoF4zChkSq 4881 := by decide +kernel
theorem C'_4881 : C' 4881 :=
  ⟨c4881_sqf, c4881_range, c4881_ell, leafNSq_of_sq c4881_nsq, leafHAr_of_sq c4881_har,
   c4881_r, c4881_e', c4881_f1, leafS2_of_sq c4881_s2, leafS3_of_sq c4881_s3,
   c4881_iso, leafR8_of_sq c4881_nof2 c4881_nof3 c4881_nof4z⟩
theorem not_tile'_4881 (D : CongruentDissection 4881) : False :=
  not_tile_of_conditions' 4881 C'_4881 D

end Erdos634.Draft.AllN2

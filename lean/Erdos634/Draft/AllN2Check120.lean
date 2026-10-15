/- AllN2Check120: N = 2870, 2874, 2878, 2879, 2881
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2870_sqf   : LeafSqf 2870   := by decide +kernel
private theorem c2870_range : LeafRange 2870  := by decide +kernel
private theorem c2870_ell   : LeafEll 2870    := by decide +kernel
private theorem c2870_nsq   : NSqChkSq 2870   := by decide +kernel
private theorem c2870_har   : HArithChkSq 2870 := by decide +kernel
private theorem c2870_r     : LeafR 2870      := by decide +kernel
private theorem c2870_e'    : LeafE' 2870     := by decide +kernel
private theorem c2870_f1    : LeafF1 2870     := Or.inl (by decide)
private theorem c2870_s2    : S2ChkSq 2870    := by decide +kernel
private theorem c2870_s3    : S3ChkSq 2870    := by decide +kernel
private theorem c2870_iso   : LeafIso 2870    := by decide +kernel
private theorem c2870_nof2  : NoF2ChkSq 2870  := by decide +kernel
private theorem c2870_nof3  : NoF3ChkSq 2870  := by decide +kernel
private theorem c2870_nof4z : NoF4zChkSq 2870 := by decide +kernel
theorem C'_2870 : C' 2870 :=
  ⟨c2870_sqf, c2870_range, c2870_ell, leafNSq_of_sq c2870_nsq, leafHAr_of_sq c2870_har,
   c2870_r, c2870_e', c2870_f1, leafS2_of_sq c2870_s2, leafS3_of_sq c2870_s3,
   c2870_iso, leafR8_of_sq c2870_nof2 c2870_nof3 c2870_nof4z⟩
theorem not_tile'_2870 (D : CongruentDissection 2870) : False :=
  not_tile_of_conditions' 2870 C'_2870 D

private theorem c2874_sqf   : LeafSqf 2874   := by decide +kernel
private theorem c2874_range : LeafRange 2874  := by decide +kernel
private theorem c2874_ell   : LeafEll 2874    := by decide +kernel
private theorem c2874_nsq   : NSqChkSq 2874   := by decide +kernel
private theorem c2874_har   : HArithChkSq 2874 := by decide +kernel
private theorem c2874_r     : LeafR 2874      := by decide +kernel
private theorem c2874_e'    : LeafE' 2874     := by decide +kernel
private theorem c2874_f1    : LeafF1 2874     := Or.inl (by decide)
private theorem c2874_s2    : S2ChkSq 2874    := by decide +kernel
private theorem c2874_s3    : S3ChkSq 2874    := by decide +kernel
private theorem c2874_iso   : LeafIso 2874    := by decide +kernel
private theorem c2874_nof2  : NoF2ChkSq 2874  := by decide +kernel
private theorem c2874_nof3  : NoF3ChkSq 2874  := by decide +kernel
private theorem c2874_nof4z : NoF4zChkSq 2874 := by decide +kernel
theorem C'_2874 : C' 2874 :=
  ⟨c2874_sqf, c2874_range, c2874_ell, leafNSq_of_sq c2874_nsq, leafHAr_of_sq c2874_har,
   c2874_r, c2874_e', c2874_f1, leafS2_of_sq c2874_s2, leafS3_of_sq c2874_s3,
   c2874_iso, leafR8_of_sq c2874_nof2 c2874_nof3 c2874_nof4z⟩
theorem not_tile'_2874 (D : CongruentDissection 2874) : False :=
  not_tile_of_conditions' 2874 C'_2874 D

private theorem c2878_sqf   : LeafSqf 2878   := by decide +kernel
private theorem c2878_range : LeafRange 2878  := by decide +kernel
private theorem c2878_ell   : LeafEll 2878    := by decide +kernel
private theorem c2878_nsq   : NSqChkSq 2878   := by decide +kernel
private theorem c2878_har   : HArithChkSq 2878 := by decide +kernel
private theorem c2878_r     : LeafR 2878      := by decide +kernel
private theorem c2878_e'    : LeafE' 2878     := by decide +kernel
private theorem c2878_f1    : LeafF1 2878     := Or.inl (by decide)
private theorem c2878_s2    : S2ChkSq 2878    := by decide +kernel
private theorem c2878_s3    : S3ChkSq 2878    := by decide +kernel
private theorem c2878_iso   : LeafIso 2878    := by decide +kernel
private theorem c2878_nof2  : NoF2ChkSq 2878  := by decide +kernel
private theorem c2878_nof3  : NoF3ChkSq 2878  := by decide +kernel
private theorem c2878_nof4z : NoF4zChkSq 2878 := by decide +kernel
theorem C'_2878 : C' 2878 :=
  ⟨c2878_sqf, c2878_range, c2878_ell, leafNSq_of_sq c2878_nsq, leafHAr_of_sq c2878_har,
   c2878_r, c2878_e', c2878_f1, leafS2_of_sq c2878_s2, leafS3_of_sq c2878_s3,
   c2878_iso, leafR8_of_sq c2878_nof2 c2878_nof3 c2878_nof4z⟩
theorem not_tile'_2878 (D : CongruentDissection 2878) : False :=
  not_tile_of_conditions' 2878 C'_2878 D

private theorem c2879_sqf   : LeafSqf 2879   := by decide +kernel
private theorem c2879_range : LeafRange 2879  := by decide +kernel
private theorem c2879_ell   : LeafEll 2879    := by decide +kernel
private theorem c2879_nsq   : NSqChkSq 2879   := by decide +kernel
private theorem c2879_har   : HArithChkSq 2879 := by decide +kernel
private theorem c2879_r     : LeafR 2879      := by decide +kernel
private theorem c2879_e'    : LeafE' 2879     := by decide +kernel
private theorem c2879_f1    : LeafF1 2879     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2879_s2    : S2ChkSq 2879    := by decide +kernel
private theorem c2879_s3    : S3ChkSq 2879    := by decide +kernel
private theorem c2879_iso   : LeafIso 2879    := by decide +kernel
private theorem c2879_nof2  : NoF2ChkSq 2879  := by decide +kernel
private theorem c2879_nof3  : NoF3ChkSq 2879  := by decide +kernel
private theorem c2879_nof4z : NoF4zChkSq 2879 := by decide +kernel
theorem C'_2879 : C' 2879 :=
  ⟨c2879_sqf, c2879_range, c2879_ell, leafNSq_of_sq c2879_nsq, leafHAr_of_sq c2879_har,
   c2879_r, c2879_e', c2879_f1, leafS2_of_sq c2879_s2, leafS3_of_sq c2879_s3,
   c2879_iso, leafR8_of_sq c2879_nof2 c2879_nof3 c2879_nof4z⟩
theorem not_tile'_2879 (D : CongruentDissection 2879) : False :=
  not_tile_of_conditions' 2879 C'_2879 D

private theorem c2881_sqf   : LeafSqf 2881   := by decide +kernel
private theorem c2881_range : LeafRange 2881  := by decide +kernel
private theorem c2881_ell   : LeafEll 2881    := by decide +kernel
private theorem c2881_nsq   : NSqChkSq 2881   := by decide +kernel
private theorem c2881_har   : HArithChkSq 2881 := by decide +kernel
private theorem c2881_r     : LeafR 2881      := by decide +kernel
private theorem c2881_e'    : LeafE' 2881     := by decide +kernel
private theorem c2881_f1    : LeafF1 2881     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2881_s2    : S2ChkSq 2881    := by decide +kernel
private theorem c2881_s3    : S3ChkSq 2881    := by decide +kernel
private theorem c2881_iso   : LeafIso 2881    := by decide +kernel
private theorem c2881_nof2  : NoF2ChkSq 2881  := by decide +kernel
private theorem c2881_nof3  : NoF3ChkSq 2881  := by decide +kernel
private theorem c2881_nof4z : NoF4zChkSq 2881 := by decide +kernel
theorem C'_2881 : C' 2881 :=
  ⟨c2881_sqf, c2881_range, c2881_ell, leafNSq_of_sq c2881_nsq, leafHAr_of_sq c2881_har,
   c2881_r, c2881_e', c2881_f1, leafS2_of_sq c2881_s2, leafS3_of_sq c2881_s3,
   c2881_iso, leafR8_of_sq c2881_nof2 c2881_nof3 c2881_nof4z⟩
theorem not_tile'_2881 (D : CongruentDissection 2881) : False :=
  not_tile_of_conditions' 2881 C'_2881 D

end Erdos634.Draft.AllN2

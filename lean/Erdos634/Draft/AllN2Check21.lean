/- AllN2Check21: N = 889, 895, 917, 921, 933.
   C' N = true for each. Not in any realizable family. No sorry, no native_decide. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c889_sqf   : LeafSqf 889   := by decide +kernel
private theorem c889_range : LeafRange 889  := by decide +kernel
private theorem c889_ell   : LeafEll 889    := by decide +kernel
private theorem c889_nsq   : NSqChkSq 889   := by decide +kernel
private theorem c889_har   : HArithChkSq 889 := by decide +kernel
private theorem c889_r     : LeafR 889      := by decide +kernel
private theorem c889_e'    : LeafE' 889     := by decide +kernel
private theorem c889_f1    : LeafF1 889     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c889_s2    : S2ChkSq 889    := by decide +kernel
private theorem c889_s3    : S3ChkSq 889    := by decide +kernel
private theorem c889_iso   : LeafIso 889    := by decide +kernel
private theorem c889_nof2  : NoF2ChkSq 889  := by decide +kernel
private theorem c889_nof3  : NoF3ChkSq 889  := by decide +kernel
private theorem c889_nof4z : NoF4zChkSq 889 := by decide +kernel
theorem C'_889 : C' 889 :=
  ⟨c889_sqf, c889_range, c889_ell, leafNSq_of_sq c889_nsq, leafHAr_of_sq c889_har,
   c889_r, c889_e', c889_f1, leafS2_of_sq c889_s2, leafS3_of_sq c889_s3,
   c889_iso, leafR8_of_sq c889_nof2 c889_nof3 c889_nof4z⟩
theorem not_tile'_889 (D : CongruentDissection 889) : False :=
  not_tile_of_conditions' 889 C'_889 D

private theorem c895_sqf   : LeafSqf 895   := by decide +kernel
private theorem c895_range : LeafRange 895  := by decide +kernel
private theorem c895_ell   : LeafEll 895    := by decide +kernel
private theorem c895_nsq   : NSqChkSq 895   := by decide +kernel
private theorem c895_har   : HArithChkSq 895 := by decide +kernel
private theorem c895_r     : LeafR 895      := by decide +kernel
private theorem c895_e'    : LeafE' 895     := by decide +kernel
private theorem c895_f1    : LeafF1 895     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c895_s2    : S2ChkSq 895    := by decide +kernel
private theorem c895_s3    : S3ChkSq 895    := by decide +kernel
private theorem c895_iso   : LeafIso 895    := by decide +kernel
private theorem c895_nof2  : NoF2ChkSq 895  := by decide +kernel
private theorem c895_nof3  : NoF3ChkSq 895  := by decide +kernel
private theorem c895_nof4z : NoF4zChkSq 895 := by decide +kernel
theorem C'_895 : C' 895 :=
  ⟨c895_sqf, c895_range, c895_ell, leafNSq_of_sq c895_nsq, leafHAr_of_sq c895_har,
   c895_r, c895_e', c895_f1, leafS2_of_sq c895_s2, leafS3_of_sq c895_s3,
   c895_iso, leafR8_of_sq c895_nof2 c895_nof3 c895_nof4z⟩
theorem not_tile'_895 (D : CongruentDissection 895) : False :=
  not_tile_of_conditions' 895 C'_895 D

private theorem c917_sqf   : LeafSqf 917   := by decide +kernel
private theorem c917_range : LeafRange 917  := by decide +kernel
private theorem c917_ell   : LeafEll 917    := by decide +kernel
private theorem c917_nsq   : NSqChkSq 917   := by decide +kernel
private theorem c917_har   : HArithChkSq 917 := by decide +kernel
private theorem c917_r     : LeafR 917      := by decide +kernel
private theorem c917_e'    : LeafE' 917     := by decide +kernel
private theorem c917_f1    : LeafF1 917     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c917_s2    : S2ChkSq 917    := by decide +kernel
private theorem c917_s3    : S3ChkSq 917    := by decide +kernel
private theorem c917_iso   : LeafIso 917    := by decide +kernel
private theorem c917_nof2  : NoF2ChkSq 917  := by decide +kernel
private theorem c917_nof3  : NoF3ChkSq 917  := by decide +kernel
private theorem c917_nof4z : NoF4zChkSq 917 := by decide +kernel
theorem C'_917 : C' 917 :=
  ⟨c917_sqf, c917_range, c917_ell, leafNSq_of_sq c917_nsq, leafHAr_of_sq c917_har,
   c917_r, c917_e', c917_f1, leafS2_of_sq c917_s2, leafS3_of_sq c917_s3,
   c917_iso, leafR8_of_sq c917_nof2 c917_nof3 c917_nof4z⟩
theorem not_tile'_917 (D : CongruentDissection 917) : False :=
  not_tile_of_conditions' 917 C'_917 D

private theorem c921_sqf   : LeafSqf 921   := by decide +kernel
private theorem c921_range : LeafRange 921  := by decide +kernel
private theorem c921_ell   : LeafEll 921    := by decide +kernel
private theorem c921_nsq   : NSqChkSq 921   := by decide +kernel
private theorem c921_har   : HArithChkSq 921 := by decide +kernel
private theorem c921_r     : LeafR 921      := by decide +kernel
private theorem c921_e'    : LeafE' 921     := by decide +kernel
private theorem c921_f1    : LeafF1 921     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c921_s2    : S2ChkSq 921    := by decide +kernel
private theorem c921_s3    : S3ChkSq 921    := by decide +kernel
private theorem c921_iso   : LeafIso 921    := by decide +kernel
private theorem c921_nof2  : NoF2ChkSq 921  := by decide +kernel
private theorem c921_nof3  : NoF3ChkSq 921  := by decide +kernel
private theorem c921_nof4z : NoF4zChkSq 921 := by decide +kernel
theorem C'_921 : C' 921 :=
  ⟨c921_sqf, c921_range, c921_ell, leafNSq_of_sq c921_nsq, leafHAr_of_sq c921_har,
   c921_r, c921_e', c921_f1, leafS2_of_sq c921_s2, leafS3_of_sq c921_s3,
   c921_iso, leafR8_of_sq c921_nof2 c921_nof3 c921_nof4z⟩
theorem not_tile'_921 (D : CongruentDissection 921) : False :=
  not_tile_of_conditions' 921 C'_921 D

private theorem c933_sqf   : LeafSqf 933   := by decide +kernel
private theorem c933_range : LeafRange 933  := by decide +kernel
private theorem c933_ell   : LeafEll 933    := by decide +kernel
private theorem c933_nsq   : NSqChkSq 933   := by decide +kernel
private theorem c933_har   : HArithChkSq 933 := by decide +kernel
private theorem c933_r     : LeafR 933      := by decide +kernel
private theorem c933_e'    : LeafE' 933     := by decide +kernel
private theorem c933_f1    : LeafF1 933     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c933_s2    : S2ChkSq 933    := by decide +kernel
private theorem c933_s3    : S3ChkSq 933    := by decide +kernel
private theorem c933_iso   : LeafIso 933    := by decide +kernel
private theorem c933_nof2  : NoF2ChkSq 933  := by decide +kernel
private theorem c933_nof3  : NoF3ChkSq 933  := by decide +kernel
private theorem c933_nof4z : NoF4zChkSq 933 := by decide +kernel
theorem C'_933 : C' 933 :=
  ⟨c933_sqf, c933_range, c933_ell, leafNSq_of_sq c933_nsq, leafHAr_of_sq c933_har,
   c933_r, c933_e', c933_f1, leafS2_of_sq c933_s2, leafS3_of_sq c933_s3,
   c933_iso, leafR8_of_sq c933_nof2 c933_nof3 c933_nof4z⟩
theorem not_tile'_933 (D : CongruentDissection 933) : False :=
  not_tile_of_conditions' 933 C'_933 D

end Erdos634.Draft.AllN2

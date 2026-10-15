/- AllN2Check279: N = 4895, 4897, 4898, 4903, 4906
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4895_sqf   : LeafSqf 4895   := by decide +kernel
private theorem c4895_range : LeafRange 4895  := by decide +kernel
private theorem c4895_ell   : LeafEll 4895    := by decide +kernel
private theorem c4895_nsq   : NSqChkSq 4895   := by decide +kernel
private theorem c4895_har   : HArithChkSq 4895 := by decide +kernel
private theorem c4895_r     : LeafR 4895      := by decide +kernel
private theorem c4895_e'    : LeafE' 4895     := by decide +kernel
private theorem c4895_f1    : LeafF1 4895     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4895_s2    : S2ChkSq 4895    := by decide +kernel
private theorem c4895_s3    : S3ChkSq 4895    := by decide +kernel
private theorem c4895_iso   : LeafIso 4895    := by decide +kernel
private theorem c4895_nof2  : NoF2ChkSq 4895  := by decide +kernel
private theorem c4895_nof3  : NoF3ChkSq 4895  := by decide +kernel
private theorem c4895_nof4z : NoF4zChkSq 4895 := by decide +kernel
theorem C'_4895 : C' 4895 :=
  ⟨c4895_sqf, c4895_range, c4895_ell, leafNSq_of_sq c4895_nsq, leafHAr_of_sq c4895_har,
   c4895_r, c4895_e', c4895_f1, leafS2_of_sq c4895_s2, leafS3_of_sq c4895_s3,
   c4895_iso, leafR8_of_sq c4895_nof2 c4895_nof3 c4895_nof4z⟩
theorem not_tile'_4895 (D : CongruentDissection 4895) : False :=
  not_tile_of_conditions' 4895 C'_4895 D

private theorem c4897_sqf   : LeafSqf 4897   := by decide +kernel
private theorem c4897_range : LeafRange 4897  := by decide +kernel
private theorem c4897_ell   : LeafEll 4897    := by decide +kernel
private theorem c4897_nsq   : NSqChkSq 4897   := by decide +kernel
private theorem c4897_har   : HArithChkSq 4897 := by decide +kernel
private theorem c4897_r     : LeafR 4897      := by decide +kernel
private theorem c4897_e'    : LeafE' 4897     := by decide +kernel
private theorem c4897_f1    : LeafF1 4897     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4897_s2    : S2ChkSq 4897    := by decide +kernel
private theorem c4897_s3    : S3ChkSq 4897    := by decide +kernel
private theorem c4897_iso   : LeafIso 4897    := by decide +kernel
private theorem c4897_nof2  : NoF2ChkSq 4897  := by decide +kernel
private theorem c4897_nof3  : NoF3ChkSq 4897  := by decide +kernel
private theorem c4897_nof4z : NoF4zChkSq 4897 := by decide +kernel
theorem C'_4897 : C' 4897 :=
  ⟨c4897_sqf, c4897_range, c4897_ell, leafNSq_of_sq c4897_nsq, leafHAr_of_sq c4897_har,
   c4897_r, c4897_e', c4897_f1, leafS2_of_sq c4897_s2, leafS3_of_sq c4897_s3,
   c4897_iso, leafR8_of_sq c4897_nof2 c4897_nof3 c4897_nof4z⟩
theorem not_tile'_4897 (D : CongruentDissection 4897) : False :=
  not_tile_of_conditions' 4897 C'_4897 D

private theorem c4898_sqf   : LeafSqf 4898   := by decide +kernel
private theorem c4898_range : LeafRange 4898  := by decide +kernel
private theorem c4898_ell   : LeafEll 4898    := by decide +kernel
private theorem c4898_nsq   : NSqChkSq 4898   := by decide +kernel
private theorem c4898_har   : HArithChkSq 4898 := by decide +kernel
private theorem c4898_r     : LeafR 4898      := by decide +kernel
private theorem c4898_e'    : LeafE' 4898     := by decide +kernel
private theorem c4898_f1    : LeafF1 4898     := Or.inl (by decide)
private theorem c4898_s2    : S2ChkSq 4898    := by decide +kernel
private theorem c4898_s3    : S3ChkSq 4898    := by decide +kernel
private theorem c4898_iso   : LeafIso 4898    := by decide +kernel
private theorem c4898_nof2  : NoF2ChkSq 4898  := by decide +kernel
private theorem c4898_nof3  : NoF3ChkSq 4898  := by decide +kernel
private theorem c4898_nof4z : NoF4zChkSq 4898 := by decide +kernel
theorem C'_4898 : C' 4898 :=
  ⟨c4898_sqf, c4898_range, c4898_ell, leafNSq_of_sq c4898_nsq, leafHAr_of_sq c4898_har,
   c4898_r, c4898_e', c4898_f1, leafS2_of_sq c4898_s2, leafS3_of_sq c4898_s3,
   c4898_iso, leafR8_of_sq c4898_nof2 c4898_nof3 c4898_nof4z⟩
theorem not_tile'_4898 (D : CongruentDissection 4898) : False :=
  not_tile_of_conditions' 4898 C'_4898 D

private theorem c4903_sqf   : LeafSqf 4903   := by decide +kernel
private theorem c4903_range : LeafRange 4903  := by decide +kernel
private theorem c4903_ell   : LeafEll 4903    := by decide +kernel
private theorem c4903_nsq   : NSqChkSq 4903   := by decide +kernel
private theorem c4903_har   : HArithChkSq 4903 := by decide +kernel
private theorem c4903_r     : LeafR 4903      := by decide +kernel
private theorem c4903_e'    : LeafE' 4903     := by decide +kernel
private theorem c4903_f1    : LeafF1 4903     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4903_s2    : S2ChkSq 4903    := by decide +kernel
private theorem c4903_s3    : S3ChkSq 4903    := by decide +kernel
private theorem c4903_iso   : LeafIso 4903    := by decide +kernel
private theorem c4903_nof2  : NoF2ChkSq 4903  := by decide +kernel
private theorem c4903_nof3  : NoF3ChkSq 4903  := by decide +kernel
private theorem c4903_nof4z : NoF4zChkSq 4903 := by decide +kernel
theorem C'_4903 : C' 4903 :=
  ⟨c4903_sqf, c4903_range, c4903_ell, leafNSq_of_sq c4903_nsq, leafHAr_of_sq c4903_har,
   c4903_r, c4903_e', c4903_f1, leafS2_of_sq c4903_s2, leafS3_of_sq c4903_s3,
   c4903_iso, leafR8_of_sq c4903_nof2 c4903_nof3 c4903_nof4z⟩
theorem not_tile'_4903 (D : CongruentDissection 4903) : False :=
  not_tile_of_conditions' 4903 C'_4903 D

private theorem c4906_sqf   : LeafSqf 4906   := by decide +kernel
private theorem c4906_range : LeafRange 4906  := by decide +kernel
private theorem c4906_ell   : LeafEll 4906    := by decide +kernel
private theorem c4906_nsq   : NSqChkSq 4906   := by decide +kernel
private theorem c4906_har   : HArithChkSq 4906 := by decide +kernel
private theorem c4906_r     : LeafR 4906      := by decide +kernel
private theorem c4906_e'    : LeafE' 4906     := by decide +kernel
private theorem c4906_f1    : LeafF1 4906     := Or.inl (by decide)
private theorem c4906_s2    : S2ChkSq 4906    := by decide +kernel
private theorem c4906_s3    : S3ChkSq 4906    := by decide +kernel
private theorem c4906_iso   : LeafIso 4906    := by decide +kernel
private theorem c4906_nof2  : NoF2ChkSq 4906  := by decide +kernel
private theorem c4906_nof3  : NoF3ChkSq 4906  := by decide +kernel
private theorem c4906_nof4z : NoF4zChkSq 4906 := by decide +kernel
theorem C'_4906 : C' 4906 :=
  ⟨c4906_sqf, c4906_range, c4906_ell, leafNSq_of_sq c4906_nsq, leafHAr_of_sq c4906_har,
   c4906_r, c4906_e', c4906_f1, leafS2_of_sq c4906_s2, leafS3_of_sq c4906_s3,
   c4906_iso, leafR8_of_sq c4906_nof2 c4906_nof3 c4906_nof4z⟩
theorem not_tile'_4906 (D : CongruentDissection 4906) : False :=
  not_tile_of_conditions' 4906 C'_4906 D

end Erdos634.Draft.AllN2

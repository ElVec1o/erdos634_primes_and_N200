/- AllN2Check200: N = 3910, 3911, 3913, 3914, 3918
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3910_sqf   : LeafSqf 3910   := by decide +kernel
private theorem c3910_range : LeafRange 3910  := by decide +kernel
private theorem c3910_ell   : LeafEll 3910    := by decide +kernel
private theorem c3910_nsq   : NSqChkSq 3910   := by decide +kernel
private theorem c3910_har   : HArithChkSq 3910 := by decide +kernel
private theorem c3910_r     : LeafR 3910      := by decide +kernel
private theorem c3910_e'    : LeafE' 3910     := by decide +kernel
private theorem c3910_f1    : LeafF1 3910     := Or.inl (by decide)
private theorem c3910_s2    : S2ChkSq 3910    := by decide +kernel
private theorem c3910_s3    : S3ChkSq 3910    := by decide +kernel
private theorem c3910_iso   : LeafIso 3910    := by decide +kernel
private theorem c3910_nof2  : NoF2ChkSq 3910  := by decide +kernel
private theorem c3910_nof3  : NoF3ChkSq 3910  := by decide +kernel
private theorem c3910_nof4z : NoF4zChkSq 3910 := by decide +kernel
theorem C'_3910 : C' 3910 :=
  ⟨c3910_sqf, c3910_range, c3910_ell, leafNSq_of_sq c3910_nsq, leafHAr_of_sq c3910_har,
   c3910_r, c3910_e', c3910_f1, leafS2_of_sq c3910_s2, leafS3_of_sq c3910_s3,
   c3910_iso, leafR8_of_sq c3910_nof2 c3910_nof3 c3910_nof4z⟩
theorem not_tile'_3910 (D : CongruentDissection 3910) : False :=
  not_tile_of_conditions' 3910 C'_3910 D

private theorem c3911_sqf   : LeafSqf 3911   := by decide +kernel
private theorem c3911_range : LeafRange 3911  := by decide +kernel
private theorem c3911_ell   : LeafEll 3911    := by decide +kernel
private theorem c3911_nsq   : NSqChkSq 3911   := by decide +kernel
private theorem c3911_har   : HArithChkSq 3911 := by decide +kernel
private theorem c3911_r     : LeafR 3911      := by decide +kernel
private theorem c3911_e'    : LeafE' 3911     := by decide +kernel
private theorem c3911_f1    : LeafF1 3911     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3911_s2    : S2ChkSq 3911    := by decide +kernel
private theorem c3911_s3    : S3ChkSq 3911    := by decide +kernel
private theorem c3911_iso   : LeafIso 3911    := by decide +kernel
private theorem c3911_nof2  : NoF2ChkSq 3911  := by decide +kernel
private theorem c3911_nof3  : NoF3ChkSq 3911  := by decide +kernel
private theorem c3911_nof4z : NoF4zChkSq 3911 := by decide +kernel
theorem C'_3911 : C' 3911 :=
  ⟨c3911_sqf, c3911_range, c3911_ell, leafNSq_of_sq c3911_nsq, leafHAr_of_sq c3911_har,
   c3911_r, c3911_e', c3911_f1, leafS2_of_sq c3911_s2, leafS3_of_sq c3911_s3,
   c3911_iso, leafR8_of_sq c3911_nof2 c3911_nof3 c3911_nof4z⟩
theorem not_tile'_3911 (D : CongruentDissection 3911) : False :=
  not_tile_of_conditions' 3911 C'_3911 D

private theorem c3913_sqf   : LeafSqf 3913   := by decide +kernel
private theorem c3913_range : LeafRange 3913  := by decide +kernel
private theorem c3913_ell   : LeafEll 3913    := by decide +kernel
private theorem c3913_nsq   : NSqChkSq 3913   := by decide +kernel
private theorem c3913_har   : HArithChkSq 3913 := by decide +kernel
private theorem c3913_r     : LeafR 3913      := by decide +kernel
private theorem c3913_e'    : LeafE' 3913     := by decide +kernel
private theorem c3913_f1    : LeafF1 3913     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3913_s2    : S2ChkSq 3913    := by decide +kernel
private theorem c3913_s3    : S3ChkSq 3913    := by decide +kernel
private theorem c3913_iso   : LeafIso 3913    := by decide +kernel
private theorem c3913_nof2  : NoF2ChkSq 3913  := by decide +kernel
private theorem c3913_nof3  : NoF3ChkSq 3913  := by decide +kernel
private theorem c3913_nof4z : NoF4zChkSq 3913 := by decide +kernel
theorem C'_3913 : C' 3913 :=
  ⟨c3913_sqf, c3913_range, c3913_ell, leafNSq_of_sq c3913_nsq, leafHAr_of_sq c3913_har,
   c3913_r, c3913_e', c3913_f1, leafS2_of_sq c3913_s2, leafS3_of_sq c3913_s3,
   c3913_iso, leafR8_of_sq c3913_nof2 c3913_nof3 c3913_nof4z⟩
theorem not_tile'_3913 (D : CongruentDissection 3913) : False :=
  not_tile_of_conditions' 3913 C'_3913 D

private theorem c3914_sqf   : LeafSqf 3914   := by decide +kernel
private theorem c3914_range : LeafRange 3914  := by decide +kernel
private theorem c3914_ell   : LeafEll 3914    := by decide +kernel
private theorem c3914_nsq   : NSqChkSq 3914   := by decide +kernel
private theorem c3914_har   : HArithChkSq 3914 := by decide +kernel
private theorem c3914_r     : LeafR 3914      := by decide +kernel
private theorem c3914_e'    : LeafE' 3914     := by decide +kernel
private theorem c3914_f1    : LeafF1 3914     := Or.inl (by decide)
private theorem c3914_s2    : S2ChkSq 3914    := by decide +kernel
private theorem c3914_s3    : S3ChkSq 3914    := by decide +kernel
private theorem c3914_iso   : LeafIso 3914    := by decide +kernel
private theorem c3914_nof2  : NoF2ChkSq 3914  := by decide +kernel
private theorem c3914_nof3  : NoF3ChkSq 3914  := by decide +kernel
private theorem c3914_nof4z : NoF4zChkSq 3914 := by decide +kernel
theorem C'_3914 : C' 3914 :=
  ⟨c3914_sqf, c3914_range, c3914_ell, leafNSq_of_sq c3914_nsq, leafHAr_of_sq c3914_har,
   c3914_r, c3914_e', c3914_f1, leafS2_of_sq c3914_s2, leafS3_of_sq c3914_s3,
   c3914_iso, leafR8_of_sq c3914_nof2 c3914_nof3 c3914_nof4z⟩
theorem not_tile'_3914 (D : CongruentDissection 3914) : False :=
  not_tile_of_conditions' 3914 C'_3914 D

private theorem c3918_sqf   : LeafSqf 3918   := by decide +kernel
private theorem c3918_range : LeafRange 3918  := by decide +kernel
private theorem c3918_ell   : LeafEll 3918    := by decide +kernel
private theorem c3918_nsq   : NSqChkSq 3918   := by decide +kernel
private theorem c3918_har   : HArithChkSq 3918 := by decide +kernel
private theorem c3918_r     : LeafR 3918      := by decide +kernel
private theorem c3918_e'    : LeafE' 3918     := by decide +kernel
private theorem c3918_f1    : LeafF1 3918     := Or.inl (by decide)
private theorem c3918_s2    : S2ChkSq 3918    := by decide +kernel
private theorem c3918_s3    : S3ChkSq 3918    := by decide +kernel
private theorem c3918_iso   : LeafIso 3918    := by decide +kernel
private theorem c3918_nof2  : NoF2ChkSq 3918  := by decide +kernel
private theorem c3918_nof3  : NoF3ChkSq 3918  := by decide +kernel
private theorem c3918_nof4z : NoF4zChkSq 3918 := by decide +kernel
theorem C'_3918 : C' 3918 :=
  ⟨c3918_sqf, c3918_range, c3918_ell, leafNSq_of_sq c3918_nsq, leafHAr_of_sq c3918_har,
   c3918_r, c3918_e', c3918_f1, leafS2_of_sq c3918_s2, leafS3_of_sq c3918_s3,
   c3918_iso, leafR8_of_sq c3918_nof2 c3918_nof3 c3918_nof4z⟩
theorem not_tile'_3918 (D : CongruentDissection 3918) : False :=
  not_tile_of_conditions' 3918 C'_3918 D

end Erdos634.Draft.AllN2

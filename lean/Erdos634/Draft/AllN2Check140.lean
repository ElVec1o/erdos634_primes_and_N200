/- AllN2Check140: N = 3117, 3118, 3119, 3122, 3126
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3117_sqf   : LeafSqf 3117   := by decide +kernel
private theorem c3117_range : LeafRange 3117  := by decide +kernel
private theorem c3117_ell   : LeafEll 3117    := by decide +kernel
private theorem c3117_nsq   : NSqChkSq 3117   := by decide +kernel
private theorem c3117_har   : HArithChkSq 3117 := by decide +kernel
private theorem c3117_r     : LeafR 3117      := by decide +kernel
private theorem c3117_e'    : LeafE' 3117     := by decide +kernel
private theorem c3117_f1    : LeafF1 3117     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3117_s2    : S2ChkSq 3117    := by decide +kernel
private theorem c3117_s3    : S3ChkSq 3117    := by decide +kernel
private theorem c3117_iso   : LeafIso 3117    := by decide +kernel
private theorem c3117_nof2  : NoF2ChkSq 3117  := by decide +kernel
private theorem c3117_nof3  : NoF3ChkSq 3117  := by decide +kernel
private theorem c3117_nof4z : NoF4zChkSq 3117 := by decide +kernel
theorem C'_3117 : C' 3117 :=
  ⟨c3117_sqf, c3117_range, c3117_ell, leafNSq_of_sq c3117_nsq, leafHAr_of_sq c3117_har,
   c3117_r, c3117_e', c3117_f1, leafS2_of_sq c3117_s2, leafS3_of_sq c3117_s3,
   c3117_iso, leafR8_of_sq c3117_nof2 c3117_nof3 c3117_nof4z⟩
theorem not_tile'_3117 (D : CongruentDissection 3117) : False :=
  not_tile_of_conditions' 3117 C'_3117 D

private theorem c3118_sqf   : LeafSqf 3118   := by decide +kernel
private theorem c3118_range : LeafRange 3118  := by decide +kernel
private theorem c3118_ell   : LeafEll 3118    := by decide +kernel
private theorem c3118_nsq   : NSqChkSq 3118   := by decide +kernel
private theorem c3118_har   : HArithChkSq 3118 := by decide +kernel
private theorem c3118_r     : LeafR 3118      := by decide +kernel
private theorem c3118_e'    : LeafE' 3118     := by decide +kernel
private theorem c3118_f1    : LeafF1 3118     := Or.inl (by decide)
private theorem c3118_s2    : S2ChkSq 3118    := by decide +kernel
private theorem c3118_s3    : S3ChkSq 3118    := by decide +kernel
private theorem c3118_iso   : LeafIso 3118    := by decide +kernel
private theorem c3118_nof2  : NoF2ChkSq 3118  := by decide +kernel
private theorem c3118_nof3  : NoF3ChkSq 3118  := by decide +kernel
private theorem c3118_nof4z : NoF4zChkSq 3118 := by decide +kernel
theorem C'_3118 : C' 3118 :=
  ⟨c3118_sqf, c3118_range, c3118_ell, leafNSq_of_sq c3118_nsq, leafHAr_of_sq c3118_har,
   c3118_r, c3118_e', c3118_f1, leafS2_of_sq c3118_s2, leafS3_of_sq c3118_s3,
   c3118_iso, leafR8_of_sq c3118_nof2 c3118_nof3 c3118_nof4z⟩
theorem not_tile'_3118 (D : CongruentDissection 3118) : False :=
  not_tile_of_conditions' 3118 C'_3118 D

private theorem c3119_sqf   : LeafSqf 3119   := by decide +kernel
private theorem c3119_range : LeafRange 3119  := by decide +kernel
private theorem c3119_ell   : LeafEll 3119    := by decide +kernel
private theorem c3119_nsq   : NSqChkSq 3119   := by decide +kernel
private theorem c3119_har   : HArithChkSq 3119 := by decide +kernel
private theorem c3119_r     : LeafR 3119      := by decide +kernel
private theorem c3119_e'    : LeafE' 3119     := by decide +kernel
private theorem c3119_f1    : LeafF1 3119     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3119_s2    : S2ChkSq 3119    := by decide +kernel
private theorem c3119_s3    : S3ChkSq 3119    := by decide +kernel
private theorem c3119_iso   : LeafIso 3119    := by decide +kernel
private theorem c3119_nof2  : NoF2ChkSq 3119  := by decide +kernel
private theorem c3119_nof3  : NoF3ChkSq 3119  := by decide +kernel
private theorem c3119_nof4z : NoF4zChkSq 3119 := by decide +kernel
theorem C'_3119 : C' 3119 :=
  ⟨c3119_sqf, c3119_range, c3119_ell, leafNSq_of_sq c3119_nsq, leafHAr_of_sq c3119_har,
   c3119_r, c3119_e', c3119_f1, leafS2_of_sq c3119_s2, leafS3_of_sq c3119_s3,
   c3119_iso, leafR8_of_sq c3119_nof2 c3119_nof3 c3119_nof4z⟩
theorem not_tile'_3119 (D : CongruentDissection 3119) : False :=
  not_tile_of_conditions' 3119 C'_3119 D

private theorem c3122_sqf   : LeafSqf 3122   := by decide +kernel
private theorem c3122_range : LeafRange 3122  := by decide +kernel
private theorem c3122_ell   : LeafEll 3122    := by decide +kernel
private theorem c3122_nsq   : NSqChkSq 3122   := by decide +kernel
private theorem c3122_har   : HArithChkSq 3122 := by decide +kernel
private theorem c3122_r     : LeafR 3122      := by decide +kernel
private theorem c3122_e'    : LeafE' 3122     := by decide +kernel
private theorem c3122_f1    : LeafF1 3122     := Or.inl (by decide)
private theorem c3122_s2    : S2ChkSq 3122    := by decide +kernel
private theorem c3122_s3    : S3ChkSq 3122    := by decide +kernel
private theorem c3122_iso   : LeafIso 3122    := by decide +kernel
private theorem c3122_nof2  : NoF2ChkSq 3122  := by decide +kernel
private theorem c3122_nof3  : NoF3ChkSq 3122  := by decide +kernel
private theorem c3122_nof4z : NoF4zChkSq 3122 := by decide +kernel
theorem C'_3122 : C' 3122 :=
  ⟨c3122_sqf, c3122_range, c3122_ell, leafNSq_of_sq c3122_nsq, leafHAr_of_sq c3122_har,
   c3122_r, c3122_e', c3122_f1, leafS2_of_sq c3122_s2, leafS3_of_sq c3122_s3,
   c3122_iso, leafR8_of_sq c3122_nof2 c3122_nof3 c3122_nof4z⟩
theorem not_tile'_3122 (D : CongruentDissection 3122) : False :=
  not_tile_of_conditions' 3122 C'_3122 D

private theorem c3126_sqf   : LeafSqf 3126   := by decide +kernel
private theorem c3126_range : LeafRange 3126  := by decide +kernel
private theorem c3126_ell   : LeafEll 3126    := by decide +kernel
private theorem c3126_nsq   : NSqChkSq 3126   := by decide +kernel
private theorem c3126_har   : HArithChkSq 3126 := by decide +kernel
private theorem c3126_r     : LeafR 3126      := by decide +kernel
private theorem c3126_e'    : LeafE' 3126     := by decide +kernel
private theorem c3126_f1    : LeafF1 3126     := Or.inl (by decide)
private theorem c3126_s2    : S2ChkSq 3126    := by decide +kernel
private theorem c3126_s3    : S3ChkSq 3126    := by decide +kernel
private theorem c3126_iso   : LeafIso 3126    := by decide +kernel
private theorem c3126_nof2  : NoF2ChkSq 3126  := by decide +kernel
private theorem c3126_nof3  : NoF3ChkSq 3126  := by decide +kernel
private theorem c3126_nof4z : NoF4zChkSq 3126 := by decide +kernel
theorem C'_3126 : C' 3126 :=
  ⟨c3126_sqf, c3126_range, c3126_ell, leafNSq_of_sq c3126_nsq, leafHAr_of_sq c3126_har,
   c3126_r, c3126_e', c3126_f1, leafS2_of_sq c3126_s2, leafS3_of_sq c3126_s3,
   c3126_iso, leafR8_of_sq c3126_nof2 c3126_nof3 c3126_nof4z⟩
theorem not_tile'_3126 (D : CongruentDissection 3126) : False :=
  not_tile_of_conditions' 3126 C'_3126 D

end Erdos634.Draft.AllN2

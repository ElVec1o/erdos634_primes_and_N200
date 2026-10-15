/- AllN2Check60: N = 2103, 2110, 2111, 2114, 2118
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2103_sqf   : LeafSqf 2103   := by decide +kernel
private theorem c2103_range : LeafRange 2103  := by decide +kernel
private theorem c2103_ell   : LeafEll 2103    := by decide +kernel
private theorem c2103_nsq   : NSqChkSq 2103   := by decide +kernel
private theorem c2103_har   : HArithChkSq 2103 := by decide +kernel
private theorem c2103_r     : LeafR 2103      := by decide +kernel
private theorem c2103_e'    : LeafE' 2103     := by decide +kernel
private theorem c2103_f1    : LeafF1 2103     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2103_s2    : S2ChkSq 2103    := by decide +kernel
private theorem c2103_s3    : S3ChkSq 2103    := by decide +kernel
private theorem c2103_iso   : LeafIso 2103    := by decide +kernel
private theorem c2103_nof2  : NoF2ChkSq 2103  := by decide +kernel
private theorem c2103_nof3  : NoF3ChkSq 2103  := by decide +kernel
private theorem c2103_nof4z : NoF4zChkSq 2103 := by decide +kernel
theorem C'_2103 : C' 2103 :=
  ⟨c2103_sqf, c2103_range, c2103_ell, leafNSq_of_sq c2103_nsq, leafHAr_of_sq c2103_har,
   c2103_r, c2103_e', c2103_f1, leafS2_of_sq c2103_s2, leafS3_of_sq c2103_s3,
   c2103_iso, leafR8_of_sq c2103_nof2 c2103_nof3 c2103_nof4z⟩
theorem not_tile'_2103 (D : CongruentDissection 2103) : False :=
  not_tile_of_conditions' 2103 C'_2103 D

private theorem c2110_sqf   : LeafSqf 2110   := by decide +kernel
private theorem c2110_range : LeafRange 2110  := by decide +kernel
private theorem c2110_ell   : LeafEll 2110    := by decide +kernel
private theorem c2110_nsq   : NSqChkSq 2110   := by decide +kernel
private theorem c2110_har   : HArithChkSq 2110 := by decide +kernel
private theorem c2110_r     : LeafR 2110      := by decide +kernel
private theorem c2110_e'    : LeafE' 2110     := by decide +kernel
private theorem c2110_f1    : LeafF1 2110     := Or.inl (by decide)
private theorem c2110_s2    : S2ChkSq 2110    := by decide +kernel
private theorem c2110_s3    : S3ChkSq 2110    := by decide +kernel
private theorem c2110_iso   : LeafIso 2110    := by decide +kernel
private theorem c2110_nof2  : NoF2ChkSq 2110  := by decide +kernel
private theorem c2110_nof3  : NoF3ChkSq 2110  := by decide +kernel
private theorem c2110_nof4z : NoF4zChkSq 2110 := by decide +kernel
theorem C'_2110 : C' 2110 :=
  ⟨c2110_sqf, c2110_range, c2110_ell, leafNSq_of_sq c2110_nsq, leafHAr_of_sq c2110_har,
   c2110_r, c2110_e', c2110_f1, leafS2_of_sq c2110_s2, leafS3_of_sq c2110_s3,
   c2110_iso, leafR8_of_sq c2110_nof2 c2110_nof3 c2110_nof4z⟩
theorem not_tile'_2110 (D : CongruentDissection 2110) : False :=
  not_tile_of_conditions' 2110 C'_2110 D

private theorem c2111_sqf   : LeafSqf 2111   := by decide +kernel
private theorem c2111_range : LeafRange 2111  := by decide +kernel
private theorem c2111_ell   : LeafEll 2111    := by decide +kernel
private theorem c2111_nsq   : NSqChkSq 2111   := by decide +kernel
private theorem c2111_har   : HArithChkSq 2111 := by decide +kernel
private theorem c2111_r     : LeafR 2111      := by decide +kernel
private theorem c2111_e'    : LeafE' 2111     := by decide +kernel
private theorem c2111_f1    : LeafF1 2111     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2111_s2    : S2ChkSq 2111    := by decide +kernel
private theorem c2111_s3    : S3ChkSq 2111    := by decide +kernel
private theorem c2111_iso   : LeafIso 2111    := by decide +kernel
private theorem c2111_nof2  : NoF2ChkSq 2111  := by decide +kernel
private theorem c2111_nof3  : NoF3ChkSq 2111  := by decide +kernel
private theorem c2111_nof4z : NoF4zChkSq 2111 := by decide +kernel
theorem C'_2111 : C' 2111 :=
  ⟨c2111_sqf, c2111_range, c2111_ell, leafNSq_of_sq c2111_nsq, leafHAr_of_sq c2111_har,
   c2111_r, c2111_e', c2111_f1, leafS2_of_sq c2111_s2, leafS3_of_sq c2111_s3,
   c2111_iso, leafR8_of_sq c2111_nof2 c2111_nof3 c2111_nof4z⟩
theorem not_tile'_2111 (D : CongruentDissection 2111) : False :=
  not_tile_of_conditions' 2111 C'_2111 D

private theorem c2114_sqf   : LeafSqf 2114   := by decide +kernel
private theorem c2114_range : LeafRange 2114  := by decide +kernel
private theorem c2114_ell   : LeafEll 2114    := by decide +kernel
private theorem c2114_nsq   : NSqChkSq 2114   := by decide +kernel
private theorem c2114_har   : HArithChkSq 2114 := by decide +kernel
private theorem c2114_r     : LeafR 2114      := by decide +kernel
private theorem c2114_e'    : LeafE' 2114     := by decide +kernel
private theorem c2114_f1    : LeafF1 2114     := Or.inl (by decide)
private theorem c2114_s2    : S2ChkSq 2114    := by decide +kernel
private theorem c2114_s3    : S3ChkSq 2114    := by decide +kernel
private theorem c2114_iso   : LeafIso 2114    := by decide +kernel
private theorem c2114_nof2  : NoF2ChkSq 2114  := by decide +kernel
private theorem c2114_nof3  : NoF3ChkSq 2114  := by decide +kernel
private theorem c2114_nof4z : NoF4zChkSq 2114 := by decide +kernel
theorem C'_2114 : C' 2114 :=
  ⟨c2114_sqf, c2114_range, c2114_ell, leafNSq_of_sq c2114_nsq, leafHAr_of_sq c2114_har,
   c2114_r, c2114_e', c2114_f1, leafS2_of_sq c2114_s2, leafS3_of_sq c2114_s3,
   c2114_iso, leafR8_of_sq c2114_nof2 c2114_nof3 c2114_nof4z⟩
theorem not_tile'_2114 (D : CongruentDissection 2114) : False :=
  not_tile_of_conditions' 2114 C'_2114 D

private theorem c2118_sqf   : LeafSqf 2118   := by decide +kernel
private theorem c2118_range : LeafRange 2118  := by decide +kernel
private theorem c2118_ell   : LeafEll 2118    := by decide +kernel
private theorem c2118_nsq   : NSqChkSq 2118   := by decide +kernel
private theorem c2118_har   : HArithChkSq 2118 := by decide +kernel
private theorem c2118_r     : LeafR 2118      := by decide +kernel
private theorem c2118_e'    : LeafE' 2118     := by decide +kernel
private theorem c2118_f1    : LeafF1 2118     := Or.inl (by decide)
private theorem c2118_s2    : S2ChkSq 2118    := by decide +kernel
private theorem c2118_s3    : S3ChkSq 2118    := by decide +kernel
private theorem c2118_iso   : LeafIso 2118    := by decide +kernel
private theorem c2118_nof2  : NoF2ChkSq 2118  := by decide +kernel
private theorem c2118_nof3  : NoF3ChkSq 2118  := by decide +kernel
private theorem c2118_nof4z : NoF4zChkSq 2118 := by decide +kernel
theorem C'_2118 : C' 2118 :=
  ⟨c2118_sqf, c2118_range, c2118_ell, leafNSq_of_sq c2118_nsq, leafHAr_of_sq c2118_har,
   c2118_r, c2118_e', c2118_f1, leafS2_of_sq c2118_s2, leafS3_of_sq c2118_s3,
   c2118_iso, leafR8_of_sq c2118_nof2 c2118_nof3 c2118_nof4z⟩
theorem not_tile'_2118 (D : CongruentDissection 2118) : False :=
  not_tile_of_conditions' 2118 C'_2118 D

end Erdos634.Draft.AllN2

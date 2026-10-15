/- AllN2CheckGap200a: N = 102, 114, 115, 118, 119, 134, 138, 142
   Squarefree values below 200 that satisfy `C'` but had no instantiated exclusion (they were listed as `unknown` by
   `FDDSpectrumTable.spectrumStatus`).  Same template as `AllN2Check23`. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c102_sqf   : LeafSqf 102   := by decide +kernel
private theorem c102_range : LeafRange 102  := by decide +kernel
private theorem c102_ell   : LeafEll 102    := by decide +kernel
private theorem c102_nsq   : NSqChkSq 102   := by decide +kernel
private theorem c102_har   : HArithChkSq 102 := by decide +kernel
private theorem c102_r     : LeafR 102      := by decide +kernel
private theorem c102_e'    : LeafE' 102     := by decide +kernel
private theorem c102_f1    : LeafF1 102     := Or.inl (by decide)
private theorem c102_s2    : S2ChkSq 102    := by decide +kernel
private theorem c102_s3    : S3ChkSq 102    := by decide +kernel
private theorem c102_iso   : LeafIso 102    := by decide +kernel
private theorem c102_nof2  : NoF2ChkSq 102  := by decide +kernel
private theorem c102_nof3  : NoF3ChkSq 102  := by decide +kernel
private theorem c102_nof4z : NoF4zChkSq 102 := by decide +kernel
theorem C'_102 : C' 102 :=
  ⟨c102_sqf, c102_range, c102_ell, leafNSq_of_sq c102_nsq, leafHAr_of_sq c102_har,
   c102_r, c102_e', c102_f1, leafS2_of_sq c102_s2, leafS3_of_sq c102_s3,
   c102_iso, leafR8_of_sq c102_nof2 c102_nof3 c102_nof4z⟩
theorem not_tile'_102 (D : CongruentDissection 102) : False :=
  not_tile_of_conditions' 102 C'_102 D

private theorem c114_sqf   : LeafSqf 114   := by decide +kernel
private theorem c114_range : LeafRange 114  := by decide +kernel
private theorem c114_ell   : LeafEll 114    := by decide +kernel
private theorem c114_nsq   : NSqChkSq 114   := by decide +kernel
private theorem c114_har   : HArithChkSq 114 := by decide +kernel
private theorem c114_r     : LeafR 114      := by decide +kernel
private theorem c114_e'    : LeafE' 114     := by decide +kernel
private theorem c114_f1    : LeafF1 114     := Or.inl (by decide)
private theorem c114_s2    : S2ChkSq 114    := by decide +kernel
private theorem c114_s3    : S3ChkSq 114    := by decide +kernel
private theorem c114_iso   : LeafIso 114    := by decide +kernel
private theorem c114_nof2  : NoF2ChkSq 114  := by decide +kernel
private theorem c114_nof3  : NoF3ChkSq 114  := by decide +kernel
private theorem c114_nof4z : NoF4zChkSq 114 := by decide +kernel
theorem C'_114 : C' 114 :=
  ⟨c114_sqf, c114_range, c114_ell, leafNSq_of_sq c114_nsq, leafHAr_of_sq c114_har,
   c114_r, c114_e', c114_f1, leafS2_of_sq c114_s2, leafS3_of_sq c114_s3,
   c114_iso, leafR8_of_sq c114_nof2 c114_nof3 c114_nof4z⟩
theorem not_tile'_114 (D : CongruentDissection 114) : False :=
  not_tile_of_conditions' 114 C'_114 D

private theorem c115_sqf   : LeafSqf 115   := by decide +kernel
private theorem c115_range : LeafRange 115  := by decide +kernel
private theorem c115_ell   : LeafEll 115    := by decide +kernel
private theorem c115_nsq   : NSqChkSq 115   := by decide +kernel
private theorem c115_har   : HArithChkSq 115 := by decide +kernel
private theorem c115_r     : LeafR 115      := by decide +kernel
private theorem c115_e'    : LeafE' 115     := by decide +kernel
private theorem c115_f1    : LeafF1 115     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c115_s2    : S2ChkSq 115    := by decide +kernel
private theorem c115_s3    : S3ChkSq 115    := by decide +kernel
private theorem c115_iso   : LeafIso 115    := by decide +kernel
private theorem c115_nof2  : NoF2ChkSq 115  := by decide +kernel
private theorem c115_nof3  : NoF3ChkSq 115  := by decide +kernel
private theorem c115_nof4z : NoF4zChkSq 115 := by decide +kernel
theorem C'_115 : C' 115 :=
  ⟨c115_sqf, c115_range, c115_ell, leafNSq_of_sq c115_nsq, leafHAr_of_sq c115_har,
   c115_r, c115_e', c115_f1, leafS2_of_sq c115_s2, leafS3_of_sq c115_s3,
   c115_iso, leafR8_of_sq c115_nof2 c115_nof3 c115_nof4z⟩
theorem not_tile'_115 (D : CongruentDissection 115) : False :=
  not_tile_of_conditions' 115 C'_115 D

private theorem c118_sqf   : LeafSqf 118   := by decide +kernel
private theorem c118_range : LeafRange 118  := by decide +kernel
private theorem c118_ell   : LeafEll 118    := by decide +kernel
private theorem c118_nsq   : NSqChkSq 118   := by decide +kernel
private theorem c118_har   : HArithChkSq 118 := by decide +kernel
private theorem c118_r     : LeafR 118      := by decide +kernel
private theorem c118_e'    : LeafE' 118     := by decide +kernel
private theorem c118_f1    : LeafF1 118     := Or.inl (by decide)
private theorem c118_s2    : S2ChkSq 118    := by decide +kernel
private theorem c118_s3    : S3ChkSq 118    := by decide +kernel
private theorem c118_iso   : LeafIso 118    := by decide +kernel
private theorem c118_nof2  : NoF2ChkSq 118  := by decide +kernel
private theorem c118_nof3  : NoF3ChkSq 118  := by decide +kernel
private theorem c118_nof4z : NoF4zChkSq 118 := by decide +kernel
theorem C'_118 : C' 118 :=
  ⟨c118_sqf, c118_range, c118_ell, leafNSq_of_sq c118_nsq, leafHAr_of_sq c118_har,
   c118_r, c118_e', c118_f1, leafS2_of_sq c118_s2, leafS3_of_sq c118_s3,
   c118_iso, leafR8_of_sq c118_nof2 c118_nof3 c118_nof4z⟩
theorem not_tile'_118 (D : CongruentDissection 118) : False :=
  not_tile_of_conditions' 118 C'_118 D

private theorem c119_sqf   : LeafSqf 119   := by decide +kernel
private theorem c119_range : LeafRange 119  := by decide +kernel
private theorem c119_ell   : LeafEll 119    := by decide +kernel
private theorem c119_nsq   : NSqChkSq 119   := by decide +kernel
private theorem c119_har   : HArithChkSq 119 := by decide +kernel
private theorem c119_r     : LeafR 119      := by decide +kernel
private theorem c119_e'    : LeafE' 119     := by decide +kernel
private theorem c119_f1    : LeafF1 119     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c119_s2    : S2ChkSq 119    := by decide +kernel
private theorem c119_s3    : S3ChkSq 119    := by decide +kernel
private theorem c119_iso   : LeafIso 119    := by decide +kernel
private theorem c119_nof2  : NoF2ChkSq 119  := by decide +kernel
private theorem c119_nof3  : NoF3ChkSq 119  := by decide +kernel
private theorem c119_nof4z : NoF4zChkSq 119 := by decide +kernel
theorem C'_119 : C' 119 :=
  ⟨c119_sqf, c119_range, c119_ell, leafNSq_of_sq c119_nsq, leafHAr_of_sq c119_har,
   c119_r, c119_e', c119_f1, leafS2_of_sq c119_s2, leafS3_of_sq c119_s3,
   c119_iso, leafR8_of_sq c119_nof2 c119_nof3 c119_nof4z⟩
theorem not_tile'_119 (D : CongruentDissection 119) : False :=
  not_tile_of_conditions' 119 C'_119 D

private theorem c134_sqf   : LeafSqf 134   := by decide +kernel
private theorem c134_range : LeafRange 134  := by decide +kernel
private theorem c134_ell   : LeafEll 134    := by decide +kernel
private theorem c134_nsq   : NSqChkSq 134   := by decide +kernel
private theorem c134_har   : HArithChkSq 134 := by decide +kernel
private theorem c134_r     : LeafR 134      := by decide +kernel
private theorem c134_e'    : LeafE' 134     := by decide +kernel
private theorem c134_f1    : LeafF1 134     := Or.inl (by decide)
private theorem c134_s2    : S2ChkSq 134    := by decide +kernel
private theorem c134_s3    : S3ChkSq 134    := by decide +kernel
private theorem c134_iso   : LeafIso 134    := by decide +kernel
private theorem c134_nof2  : NoF2ChkSq 134  := by decide +kernel
private theorem c134_nof3  : NoF3ChkSq 134  := by decide +kernel
private theorem c134_nof4z : NoF4zChkSq 134 := by decide +kernel
theorem C'_134 : C' 134 :=
  ⟨c134_sqf, c134_range, c134_ell, leafNSq_of_sq c134_nsq, leafHAr_of_sq c134_har,
   c134_r, c134_e', c134_f1, leafS2_of_sq c134_s2, leafS3_of_sq c134_s3,
   c134_iso, leafR8_of_sq c134_nof2 c134_nof3 c134_nof4z⟩
theorem not_tile'_134 (D : CongruentDissection 134) : False :=
  not_tile_of_conditions' 134 C'_134 D

private theorem c138_sqf   : LeafSqf 138   := by decide +kernel
private theorem c138_range : LeafRange 138  := by decide +kernel
private theorem c138_ell   : LeafEll 138    := by decide +kernel
private theorem c138_nsq   : NSqChkSq 138   := by decide +kernel
private theorem c138_har   : HArithChkSq 138 := by decide +kernel
private theorem c138_r     : LeafR 138      := by decide +kernel
private theorem c138_e'    : LeafE' 138     := by decide +kernel
private theorem c138_f1    : LeafF1 138     := Or.inl (by decide)
private theorem c138_s2    : S2ChkSq 138    := by decide +kernel
private theorem c138_s3    : S3ChkSq 138    := by decide +kernel
private theorem c138_iso   : LeafIso 138    := by decide +kernel
private theorem c138_nof2  : NoF2ChkSq 138  := by decide +kernel
private theorem c138_nof3  : NoF3ChkSq 138  := by decide +kernel
private theorem c138_nof4z : NoF4zChkSq 138 := by decide +kernel
theorem C'_138 : C' 138 :=
  ⟨c138_sqf, c138_range, c138_ell, leafNSq_of_sq c138_nsq, leafHAr_of_sq c138_har,
   c138_r, c138_e', c138_f1, leafS2_of_sq c138_s2, leafS3_of_sq c138_s3,
   c138_iso, leafR8_of_sq c138_nof2 c138_nof3 c138_nof4z⟩
theorem not_tile'_138 (D : CongruentDissection 138) : False :=
  not_tile_of_conditions' 138 C'_138 D

private theorem c142_sqf   : LeafSqf 142   := by decide +kernel
private theorem c142_range : LeafRange 142  := by decide +kernel
private theorem c142_ell   : LeafEll 142    := by decide +kernel
private theorem c142_nsq   : NSqChkSq 142   := by decide +kernel
private theorem c142_har   : HArithChkSq 142 := by decide +kernel
private theorem c142_r     : LeafR 142      := by decide +kernel
private theorem c142_e'    : LeafE' 142     := by decide +kernel
private theorem c142_f1    : LeafF1 142     := Or.inl (by decide)
private theorem c142_s2    : S2ChkSq 142    := by decide +kernel
private theorem c142_s3    : S3ChkSq 142    := by decide +kernel
private theorem c142_iso   : LeafIso 142    := by decide +kernel
private theorem c142_nof2  : NoF2ChkSq 142  := by decide +kernel
private theorem c142_nof3  : NoF3ChkSq 142  := by decide +kernel
private theorem c142_nof4z : NoF4zChkSq 142 := by decide +kernel
theorem C'_142 : C' 142 :=
  ⟨c142_sqf, c142_range, c142_ell, leafNSq_of_sq c142_nsq, leafHAr_of_sq c142_har,
   c142_r, c142_e', c142_f1, leafS2_of_sq c142_s2, leafS3_of_sq c142_s3,
   c142_iso, leafR8_of_sq c142_nof2 c142_nof3 c142_nof4z⟩
theorem not_tile'_142 (D : CongruentDissection 142) : False :=
  not_tile_of_conditions' 142 C'_142 D

end Erdos634.Draft.AllN2

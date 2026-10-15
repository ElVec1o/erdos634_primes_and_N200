/- AllN2CheckGap200b: N = 155, 158, 166, 174, 182, 186, 187, 190
   Squarefree values below 200 that satisfy `C'` but had no instantiated exclusion (they were listed as `unknown` by
   `FDDSpectrumTable.spectrumStatus`).  Same template as `AllN2Check23`. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c155_sqf   : LeafSqf 155   := by decide +kernel
private theorem c155_range : LeafRange 155  := by decide +kernel
private theorem c155_ell   : LeafEll 155    := by decide +kernel
private theorem c155_nsq   : NSqChkSq 155   := by decide +kernel
private theorem c155_har   : HArithChkSq 155 := by decide +kernel
private theorem c155_r     : LeafR 155      := by decide +kernel
private theorem c155_e'    : LeafE' 155     := by decide +kernel
private theorem c155_f1    : LeafF1 155     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c155_s2    : S2ChkSq 155    := by decide +kernel
private theorem c155_s3    : S3ChkSq 155    := by decide +kernel
private theorem c155_iso   : LeafIso 155    := by decide +kernel
private theorem c155_nof2  : NoF2ChkSq 155  := by decide +kernel
private theorem c155_nof3  : NoF3ChkSq 155  := by decide +kernel
private theorem c155_nof4z : NoF4zChkSq 155 := by decide +kernel
theorem C'_155 : C' 155 :=
  ⟨c155_sqf, c155_range, c155_ell, leafNSq_of_sq c155_nsq, leafHAr_of_sq c155_har,
   c155_r, c155_e', c155_f1, leafS2_of_sq c155_s2, leafS3_of_sq c155_s3,
   c155_iso, leafR8_of_sq c155_nof2 c155_nof3 c155_nof4z⟩
theorem not_tile'_155 (D : CongruentDissection 155) : False :=
  not_tile_of_conditions' 155 C'_155 D

private theorem c158_sqf   : LeafSqf 158   := by decide +kernel
private theorem c158_range : LeafRange 158  := by decide +kernel
private theorem c158_ell   : LeafEll 158    := by decide +kernel
private theorem c158_nsq   : NSqChkSq 158   := by decide +kernel
private theorem c158_har   : HArithChkSq 158 := by decide +kernel
private theorem c158_r     : LeafR 158      := by decide +kernel
private theorem c158_e'    : LeafE' 158     := by decide +kernel
private theorem c158_f1    : LeafF1 158     := Or.inl (by decide)
private theorem c158_s2    : S2ChkSq 158    := by decide +kernel
private theorem c158_s3    : S3ChkSq 158    := by decide +kernel
private theorem c158_iso   : LeafIso 158    := by decide +kernel
private theorem c158_nof2  : NoF2ChkSq 158  := by decide +kernel
private theorem c158_nof3  : NoF3ChkSq 158  := by decide +kernel
private theorem c158_nof4z : NoF4zChkSq 158 := by decide +kernel
theorem C'_158 : C' 158 :=
  ⟨c158_sqf, c158_range, c158_ell, leafNSq_of_sq c158_nsq, leafHAr_of_sq c158_har,
   c158_r, c158_e', c158_f1, leafS2_of_sq c158_s2, leafS3_of_sq c158_s3,
   c158_iso, leafR8_of_sq c158_nof2 c158_nof3 c158_nof4z⟩
theorem not_tile'_158 (D : CongruentDissection 158) : False :=
  not_tile_of_conditions' 158 C'_158 D

private theorem c166_sqf   : LeafSqf 166   := by decide +kernel
private theorem c166_range : LeafRange 166  := by decide +kernel
private theorem c166_ell   : LeafEll 166    := by decide +kernel
private theorem c166_nsq   : NSqChkSq 166   := by decide +kernel
private theorem c166_har   : HArithChkSq 166 := by decide +kernel
private theorem c166_r     : LeafR 166      := by decide +kernel
private theorem c166_e'    : LeafE' 166     := by decide +kernel
private theorem c166_f1    : LeafF1 166     := Or.inl (by decide)
private theorem c166_s2    : S2ChkSq 166    := by decide +kernel
private theorem c166_s3    : S3ChkSq 166    := by decide +kernel
private theorem c166_iso   : LeafIso 166    := by decide +kernel
private theorem c166_nof2  : NoF2ChkSq 166  := by decide +kernel
private theorem c166_nof3  : NoF3ChkSq 166  := by decide +kernel
private theorem c166_nof4z : NoF4zChkSq 166 := by decide +kernel
theorem C'_166 : C' 166 :=
  ⟨c166_sqf, c166_range, c166_ell, leafNSq_of_sq c166_nsq, leafHAr_of_sq c166_har,
   c166_r, c166_e', c166_f1, leafS2_of_sq c166_s2, leafS3_of_sq c166_s3,
   c166_iso, leafR8_of_sq c166_nof2 c166_nof3 c166_nof4z⟩
theorem not_tile'_166 (D : CongruentDissection 166) : False :=
  not_tile_of_conditions' 166 C'_166 D

private theorem c174_sqf   : LeafSqf 174   := by decide +kernel
private theorem c174_range : LeafRange 174  := by decide +kernel
private theorem c174_ell   : LeafEll 174    := by decide +kernel
private theorem c174_nsq   : NSqChkSq 174   := by decide +kernel
private theorem c174_har   : HArithChkSq 174 := by decide +kernel
private theorem c174_r     : LeafR 174      := by decide +kernel
private theorem c174_e'    : LeafE' 174     := by decide +kernel
private theorem c174_f1    : LeafF1 174     := Or.inl (by decide)
private theorem c174_s2    : S2ChkSq 174    := by decide +kernel
private theorem c174_s3    : S3ChkSq 174    := by decide +kernel
private theorem c174_iso   : LeafIso 174    := by decide +kernel
private theorem c174_nof2  : NoF2ChkSq 174  := by decide +kernel
private theorem c174_nof3  : NoF3ChkSq 174  := by decide +kernel
private theorem c174_nof4z : NoF4zChkSq 174 := by decide +kernel
theorem C'_174 : C' 174 :=
  ⟨c174_sqf, c174_range, c174_ell, leafNSq_of_sq c174_nsq, leafHAr_of_sq c174_har,
   c174_r, c174_e', c174_f1, leafS2_of_sq c174_s2, leafS3_of_sq c174_s3,
   c174_iso, leafR8_of_sq c174_nof2 c174_nof3 c174_nof4z⟩
theorem not_tile'_174 (D : CongruentDissection 174) : False :=
  not_tile_of_conditions' 174 C'_174 D

private theorem c182_sqf   : LeafSqf 182   := by decide +kernel
private theorem c182_range : LeafRange 182  := by decide +kernel
private theorem c182_ell   : LeafEll 182    := by decide +kernel
private theorem c182_nsq   : NSqChkSq 182   := by decide +kernel
private theorem c182_har   : HArithChkSq 182 := by decide +kernel
private theorem c182_r     : LeafR 182      := by decide +kernel
private theorem c182_e'    : LeafE' 182     := by decide +kernel
private theorem c182_f1    : LeafF1 182     := Or.inl (by decide)
private theorem c182_s2    : S2ChkSq 182    := by decide +kernel
private theorem c182_s3    : S3ChkSq 182    := by decide +kernel
private theorem c182_iso   : LeafIso 182    := by decide +kernel
private theorem c182_nof2  : NoF2ChkSq 182  := by decide +kernel
private theorem c182_nof3  : NoF3ChkSq 182  := by decide +kernel
private theorem c182_nof4z : NoF4zChkSq 182 := by decide +kernel
theorem C'_182 : C' 182 :=
  ⟨c182_sqf, c182_range, c182_ell, leafNSq_of_sq c182_nsq, leafHAr_of_sq c182_har,
   c182_r, c182_e', c182_f1, leafS2_of_sq c182_s2, leafS3_of_sq c182_s3,
   c182_iso, leafR8_of_sq c182_nof2 c182_nof3 c182_nof4z⟩
theorem not_tile'_182 (D : CongruentDissection 182) : False :=
  not_tile_of_conditions' 182 C'_182 D

private theorem c186_sqf   : LeafSqf 186   := by decide +kernel
private theorem c186_range : LeafRange 186  := by decide +kernel
private theorem c186_ell   : LeafEll 186    := by decide +kernel
private theorem c186_nsq   : NSqChkSq 186   := by decide +kernel
private theorem c186_har   : HArithChkSq 186 := by decide +kernel
private theorem c186_r     : LeafR 186      := by decide +kernel
private theorem c186_e'    : LeafE' 186     := by decide +kernel
private theorem c186_f1    : LeafF1 186     := Or.inl (by decide)
private theorem c186_s2    : S2ChkSq 186    := by decide +kernel
private theorem c186_s3    : S3ChkSq 186    := by decide +kernel
private theorem c186_iso   : LeafIso 186    := by decide +kernel
private theorem c186_nof2  : NoF2ChkSq 186  := by decide +kernel
private theorem c186_nof3  : NoF3ChkSq 186  := by decide +kernel
private theorem c186_nof4z : NoF4zChkSq 186 := by decide +kernel
theorem C'_186 : C' 186 :=
  ⟨c186_sqf, c186_range, c186_ell, leafNSq_of_sq c186_nsq, leafHAr_of_sq c186_har,
   c186_r, c186_e', c186_f1, leafS2_of_sq c186_s2, leafS3_of_sq c186_s3,
   c186_iso, leafR8_of_sq c186_nof2 c186_nof3 c186_nof4z⟩
theorem not_tile'_186 (D : CongruentDissection 186) : False :=
  not_tile_of_conditions' 186 C'_186 D

private theorem c187_sqf   : LeafSqf 187   := by decide +kernel
private theorem c187_range : LeafRange 187  := by decide +kernel
private theorem c187_ell   : LeafEll 187    := by decide +kernel
private theorem c187_nsq   : NSqChkSq 187   := by decide +kernel
private theorem c187_har   : HArithChkSq 187 := by decide +kernel
private theorem c187_r     : LeafR 187      := by decide +kernel
private theorem c187_e'    : LeafE' 187     := by decide +kernel
private theorem c187_f1    : LeafF1 187     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c187_s2    : S2ChkSq 187    := by decide +kernel
private theorem c187_s3    : S3ChkSq 187    := by decide +kernel
private theorem c187_iso   : LeafIso 187    := by decide +kernel
private theorem c187_nof2  : NoF2ChkSq 187  := by decide +kernel
private theorem c187_nof3  : NoF3ChkSq 187  := by decide +kernel
private theorem c187_nof4z : NoF4zChkSq 187 := by decide +kernel
theorem C'_187 : C' 187 :=
  ⟨c187_sqf, c187_range, c187_ell, leafNSq_of_sq c187_nsq, leafHAr_of_sq c187_har,
   c187_r, c187_e', c187_f1, leafS2_of_sq c187_s2, leafS3_of_sq c187_s3,
   c187_iso, leafR8_of_sq c187_nof2 c187_nof3 c187_nof4z⟩
theorem not_tile'_187 (D : CongruentDissection 187) : False :=
  not_tile_of_conditions' 187 C'_187 D

private theorem c190_sqf   : LeafSqf 190   := by decide +kernel
private theorem c190_range : LeafRange 190  := by decide +kernel
private theorem c190_ell   : LeafEll 190    := by decide +kernel
private theorem c190_nsq   : NSqChkSq 190   := by decide +kernel
private theorem c190_har   : HArithChkSq 190 := by decide +kernel
private theorem c190_r     : LeafR 190      := by decide +kernel
private theorem c190_e'    : LeafE' 190     := by decide +kernel
private theorem c190_f1    : LeafF1 190     := Or.inl (by decide)
private theorem c190_s2    : S2ChkSq 190    := by decide +kernel
private theorem c190_s3    : S3ChkSq 190    := by decide +kernel
private theorem c190_iso   : LeafIso 190    := by decide +kernel
private theorem c190_nof2  : NoF2ChkSq 190  := by decide +kernel
private theorem c190_nof3  : NoF3ChkSq 190  := by decide +kernel
private theorem c190_nof4z : NoF4zChkSq 190 := by decide +kernel
theorem C'_190 : C' 190 :=
  ⟨c190_sqf, c190_range, c190_ell, leafNSq_of_sq c190_nsq, leafHAr_of_sq c190_har,
   c190_r, c190_e', c190_f1, leafS2_of_sq c190_s2, leafS3_of_sq c190_s3,
   c190_iso, leafR8_of_sq c190_nof2 c190_nof3 c190_nof4z⟩
theorem not_tile'_190 (D : CongruentDissection 190) : False :=
  not_tile_of_conditions' 190 C'_190 D

end Erdos634.Draft.AllN2

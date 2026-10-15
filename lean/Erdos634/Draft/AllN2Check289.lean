/- AllN2Check289: N = 5010, 5011, 5014, 5015, 5023
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c5010_sqf   : LeafSqf 5010   := by decide +kernel
private theorem c5010_range : LeafRange 5010  := by decide +kernel
private theorem c5010_ell   : LeafEll 5010    := by decide +kernel
private theorem c5010_nsq   : NSqChkSq 5010   := by decide +kernel
private theorem c5010_har   : HArithChkSq 5010 := by decide +kernel
private theorem c5010_r     : LeafR 5010      := by decide +kernel
private theorem c5010_e'    : LeafE' 5010     := by decide +kernel
private theorem c5010_f1    : LeafF1 5010     := Or.inl (by decide)
private theorem c5010_s2    : S2ChkSq 5010    := by decide +kernel
private theorem c5010_s3    : S3ChkSq 5010    := by decide +kernel
private theorem c5010_iso   : LeafIso 5010    := by decide +kernel
private theorem c5010_nof2  : NoF2ChkSq 5010  := by decide +kernel
private theorem c5010_nof3  : NoF3ChkSq 5010  := by decide +kernel
private theorem c5010_nof4z : NoF4zChkSq 5010 := by decide +kernel
theorem C'_5010 : C' 5010 :=
  ⟨c5010_sqf, c5010_range, c5010_ell, leafNSq_of_sq c5010_nsq, leafHAr_of_sq c5010_har,
   c5010_r, c5010_e', c5010_f1, leafS2_of_sq c5010_s2, leafS3_of_sq c5010_s3,
   c5010_iso, leafR8_of_sq c5010_nof2 c5010_nof3 c5010_nof4z⟩
theorem not_tile'_5010 (D : CongruentDissection 5010) : False :=
  not_tile_of_conditions' 5010 C'_5010 D

private theorem c5011_sqf   : LeafSqf 5011   := by decide +kernel
private theorem c5011_range : LeafRange 5011  := by decide +kernel
private theorem c5011_ell   : LeafEll 5011    := by decide +kernel
private theorem c5011_nsq   : NSqChkSq 5011   := by decide +kernel
private theorem c5011_har   : HArithChkSq 5011 := by decide +kernel
private theorem c5011_r     : LeafR 5011      := by decide +kernel
private theorem c5011_e'    : LeafE' 5011     := by decide +kernel
private theorem c5011_f1    : LeafF1 5011     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c5011_s2    : S2ChkSq 5011    := by decide +kernel
private theorem c5011_s3    : S3ChkSq 5011    := by decide +kernel
private theorem c5011_iso   : LeafIso 5011    := by decide +kernel
private theorem c5011_nof2  : NoF2ChkSq 5011  := by decide +kernel
private theorem c5011_nof3  : NoF3ChkSq 5011  := by decide +kernel
private theorem c5011_nof4z : NoF4zChkSq 5011 := by decide +kernel
theorem C'_5011 : C' 5011 :=
  ⟨c5011_sqf, c5011_range, c5011_ell, leafNSq_of_sq c5011_nsq, leafHAr_of_sq c5011_har,
   c5011_r, c5011_e', c5011_f1, leafS2_of_sq c5011_s2, leafS3_of_sq c5011_s3,
   c5011_iso, leafR8_of_sq c5011_nof2 c5011_nof3 c5011_nof4z⟩
theorem not_tile'_5011 (D : CongruentDissection 5011) : False :=
  not_tile_of_conditions' 5011 C'_5011 D

private theorem c5014_sqf   : LeafSqf 5014   := by decide +kernel
private theorem c5014_range : LeafRange 5014  := by decide +kernel
private theorem c5014_ell   : LeafEll 5014    := by decide +kernel
private theorem c5014_nsq   : NSqChkSq 5014   := by decide +kernel
private theorem c5014_har   : HArithChkSq 5014 := by decide +kernel
private theorem c5014_r     : LeafR 5014      := by decide +kernel
private theorem c5014_e'    : LeafE' 5014     := by decide +kernel
private theorem c5014_f1    : LeafF1 5014     := Or.inl (by decide)
private theorem c5014_s2    : S2ChkSq 5014    := by decide +kernel
private theorem c5014_s3    : S3ChkSq 5014    := by decide +kernel
private theorem c5014_iso   : LeafIso 5014    := by decide +kernel
private theorem c5014_nof2  : NoF2ChkSq 5014  := by decide +kernel
private theorem c5014_nof3  : NoF3ChkSq 5014  := by decide +kernel
private theorem c5014_nof4z : NoF4zChkSq 5014 := by decide +kernel
theorem C'_5014 : C' 5014 :=
  ⟨c5014_sqf, c5014_range, c5014_ell, leafNSq_of_sq c5014_nsq, leafHAr_of_sq c5014_har,
   c5014_r, c5014_e', c5014_f1, leafS2_of_sq c5014_s2, leafS3_of_sq c5014_s3,
   c5014_iso, leafR8_of_sq c5014_nof2 c5014_nof3 c5014_nof4z⟩
theorem not_tile'_5014 (D : CongruentDissection 5014) : False :=
  not_tile_of_conditions' 5014 C'_5014 D

private theorem c5015_sqf   : LeafSqf 5015   := by decide +kernel
private theorem c5015_range : LeafRange 5015  := by decide +kernel
private theorem c5015_ell   : LeafEll 5015    := by decide +kernel
private theorem c5015_nsq   : NSqChkSq 5015   := by decide +kernel
private theorem c5015_har   : HArithChkSq 5015 := by decide +kernel
private theorem c5015_r     : LeafR 5015      := by decide +kernel
private theorem c5015_e'    : LeafE' 5015     := by decide +kernel
private theorem c5015_f1    : LeafF1 5015     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c5015_s2    : S2ChkSq 5015    := by decide +kernel
private theorem c5015_s3    : S3ChkSq 5015    := by decide +kernel
private theorem c5015_iso   : LeafIso 5015    := by decide +kernel
private theorem c5015_nof2  : NoF2ChkSq 5015  := by decide +kernel
private theorem c5015_nof3  : NoF3ChkSq 5015  := by decide +kernel
private theorem c5015_nof4z : NoF4zChkSq 5015 := by decide +kernel
theorem C'_5015 : C' 5015 :=
  ⟨c5015_sqf, c5015_range, c5015_ell, leafNSq_of_sq c5015_nsq, leafHAr_of_sq c5015_har,
   c5015_r, c5015_e', c5015_f1, leafS2_of_sq c5015_s2, leafS3_of_sq c5015_s3,
   c5015_iso, leafR8_of_sq c5015_nof2 c5015_nof3 c5015_nof4z⟩
theorem not_tile'_5015 (D : CongruentDissection 5015) : False :=
  not_tile_of_conditions' 5015 C'_5015 D

private theorem c5023_sqf   : LeafSqf 5023   := by decide +kernel
private theorem c5023_range : LeafRange 5023  := by decide +kernel
private theorem c5023_ell   : LeafEll 5023    := by decide +kernel
private theorem c5023_nsq   : NSqChkSq 5023   := by decide +kernel
private theorem c5023_har   : HArithChkSq 5023 := by decide +kernel
private theorem c5023_r     : LeafR 5023      := by decide +kernel
private theorem c5023_e'    : LeafE' 5023     := by decide +kernel
private theorem c5023_f1    : LeafF1 5023     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c5023_s2    : S2ChkSq 5023    := by decide +kernel
private theorem c5023_s3    : S3ChkSq 5023    := by decide +kernel
private theorem c5023_iso   : LeafIso 5023    := by decide +kernel
private theorem c5023_nof2  : NoF2ChkSq 5023  := by decide +kernel
private theorem c5023_nof3  : NoF3ChkSq 5023  := by decide +kernel
private theorem c5023_nof4z : NoF4zChkSq 5023 := by decide +kernel
theorem C'_5023 : C' 5023 :=
  ⟨c5023_sqf, c5023_range, c5023_ell, leafNSq_of_sq c5023_nsq, leafHAr_of_sq c5023_har,
   c5023_r, c5023_e', c5023_f1, leafS2_of_sq c5023_s2, leafS3_of_sq c5023_s3,
   c5023_iso, leafR8_of_sq c5023_nof2 c5023_nof3 c5023_nof4z⟩
theorem not_tile'_5023 (D : CongruentDissection 5023) : False :=
  not_tile_of_conditions' 5023 C'_5023 D

end Erdos634.Draft.AllN2

/- AllN2Check130: N = 3002, 3007, 3010, 3011, 3013
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3002_sqf   : LeafSqf 3002   := by decide +kernel
private theorem c3002_range : LeafRange 3002  := by decide +kernel
private theorem c3002_ell   : LeafEll 3002    := by decide +kernel
private theorem c3002_nsq   : NSqChkSq 3002   := by decide +kernel
private theorem c3002_har   : HArithChkSq 3002 := by decide +kernel
private theorem c3002_r     : LeafR 3002      := by decide +kernel
private theorem c3002_e'    : LeafE' 3002     := by decide +kernel
private theorem c3002_f1    : LeafF1 3002     := Or.inl (by decide)
private theorem c3002_s2    : S2ChkSq 3002    := by decide +kernel
private theorem c3002_s3    : S3ChkSq 3002    := by decide +kernel
private theorem c3002_iso   : LeafIso 3002    := by decide +kernel
private theorem c3002_nof2  : NoF2ChkSq 3002  := by decide +kernel
private theorem c3002_nof3  : NoF3ChkSq 3002  := by decide +kernel
private theorem c3002_nof4z : NoF4zChkSq 3002 := by decide +kernel
theorem C'_3002 : C' 3002 :=
  ⟨c3002_sqf, c3002_range, c3002_ell, leafNSq_of_sq c3002_nsq, leafHAr_of_sq c3002_har,
   c3002_r, c3002_e', c3002_f1, leafS2_of_sq c3002_s2, leafS3_of_sq c3002_s3,
   c3002_iso, leafR8_of_sq c3002_nof2 c3002_nof3 c3002_nof4z⟩
theorem not_tile'_3002 (D : CongruentDissection 3002) : False :=
  not_tile_of_conditions' 3002 C'_3002 D

private theorem c3007_sqf   : LeafSqf 3007   := by decide +kernel
private theorem c3007_range : LeafRange 3007  := by decide +kernel
private theorem c3007_ell   : LeafEll 3007    := by decide +kernel
private theorem c3007_nsq   : NSqChkSq 3007   := by decide +kernel
private theorem c3007_har   : HArithChkSq 3007 := by decide +kernel
private theorem c3007_r     : LeafR 3007      := by decide +kernel
private theorem c3007_e'    : LeafE' 3007     := by decide +kernel
private theorem c3007_f1    : LeafF1 3007     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3007_s2    : S2ChkSq 3007    := by decide +kernel
private theorem c3007_s3    : S3ChkSq 3007    := by decide +kernel
private theorem c3007_iso   : LeafIso 3007    := by decide +kernel
private theorem c3007_nof2  : NoF2ChkSq 3007  := by decide +kernel
private theorem c3007_nof3  : NoF3ChkSq 3007  := by decide +kernel
private theorem c3007_nof4z : NoF4zChkSq 3007 := by decide +kernel
theorem C'_3007 : C' 3007 :=
  ⟨c3007_sqf, c3007_range, c3007_ell, leafNSq_of_sq c3007_nsq, leafHAr_of_sq c3007_har,
   c3007_r, c3007_e', c3007_f1, leafS2_of_sq c3007_s2, leafS3_of_sq c3007_s3,
   c3007_iso, leafR8_of_sq c3007_nof2 c3007_nof3 c3007_nof4z⟩
theorem not_tile'_3007 (D : CongruentDissection 3007) : False :=
  not_tile_of_conditions' 3007 C'_3007 D

private theorem c3010_sqf   : LeafSqf 3010   := by decide +kernel
private theorem c3010_range : LeafRange 3010  := by decide +kernel
private theorem c3010_ell   : LeafEll 3010    := by decide +kernel
private theorem c3010_nsq   : NSqChkSq 3010   := by decide +kernel
private theorem c3010_har   : HArithChkSq 3010 := by decide +kernel
private theorem c3010_r     : LeafR 3010      := by decide +kernel
private theorem c3010_e'    : LeafE' 3010     := by decide +kernel
private theorem c3010_f1    : LeafF1 3010     := Or.inl (by decide)
private theorem c3010_s2    : S2ChkSq 3010    := by decide +kernel
private theorem c3010_s3    : S3ChkSq 3010    := by decide +kernel
private theorem c3010_iso   : LeafIso 3010    := by decide +kernel
private theorem c3010_nof2  : NoF2ChkSq 3010  := by decide +kernel
private theorem c3010_nof3  : NoF3ChkSq 3010  := by decide +kernel
private theorem c3010_nof4z : NoF4zChkSq 3010 := by decide +kernel
theorem C'_3010 : C' 3010 :=
  ⟨c3010_sqf, c3010_range, c3010_ell, leafNSq_of_sq c3010_nsq, leafHAr_of_sq c3010_har,
   c3010_r, c3010_e', c3010_f1, leafS2_of_sq c3010_s2, leafS3_of_sq c3010_s3,
   c3010_iso, leafR8_of_sq c3010_nof2 c3010_nof3 c3010_nof4z⟩
theorem not_tile'_3010 (D : CongruentDissection 3010) : False :=
  not_tile_of_conditions' 3010 C'_3010 D

private theorem c3011_sqf   : LeafSqf 3011   := by decide +kernel
private theorem c3011_range : LeafRange 3011  := by decide +kernel
private theorem c3011_ell   : LeafEll 3011    := by decide +kernel
private theorem c3011_nsq   : NSqChkSq 3011   := by decide +kernel
private theorem c3011_har   : HArithChkSq 3011 := by decide +kernel
private theorem c3011_r     : LeafR 3011      := by decide +kernel
private theorem c3011_e'    : LeafE' 3011     := by decide +kernel
private theorem c3011_f1    : LeafF1 3011     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3011_s2    : S2ChkSq 3011    := by decide +kernel
private theorem c3011_s3    : S3ChkSq 3011    := by decide +kernel
private theorem c3011_iso   : LeafIso 3011    := by decide +kernel
private theorem c3011_nof2  : NoF2ChkSq 3011  := by decide +kernel
private theorem c3011_nof3  : NoF3ChkSq 3011  := by decide +kernel
private theorem c3011_nof4z : NoF4zChkSq 3011 := by decide +kernel
theorem C'_3011 : C' 3011 :=
  ⟨c3011_sqf, c3011_range, c3011_ell, leafNSq_of_sq c3011_nsq, leafHAr_of_sq c3011_har,
   c3011_r, c3011_e', c3011_f1, leafS2_of_sq c3011_s2, leafS3_of_sq c3011_s3,
   c3011_iso, leafR8_of_sq c3011_nof2 c3011_nof3 c3011_nof4z⟩
theorem not_tile'_3011 (D : CongruentDissection 3011) : False :=
  not_tile_of_conditions' 3011 C'_3011 D

private theorem c3013_sqf   : LeafSqf 3013   := by decide +kernel
private theorem c3013_range : LeafRange 3013  := by decide +kernel
private theorem c3013_ell   : LeafEll 3013    := by decide +kernel
private theorem c3013_nsq   : NSqChkSq 3013   := by decide +kernel
private theorem c3013_har   : HArithChkSq 3013 := by decide +kernel
private theorem c3013_r     : LeafR 3013      := by decide +kernel
private theorem c3013_e'    : LeafE' 3013     := by decide +kernel
private theorem c3013_f1    : LeafF1 3013     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3013_s2    : S2ChkSq 3013    := by decide +kernel
private theorem c3013_s3    : S3ChkSq 3013    := by decide +kernel
private theorem c3013_iso   : LeafIso 3013    := by decide +kernel
private theorem c3013_nof2  : NoF2ChkSq 3013  := by decide +kernel
private theorem c3013_nof3  : NoF3ChkSq 3013  := by decide +kernel
private theorem c3013_nof4z : NoF4zChkSq 3013 := by decide +kernel
theorem C'_3013 : C' 3013 :=
  ⟨c3013_sqf, c3013_range, c3013_ell, leafNSq_of_sq c3013_nsq, leafHAr_of_sq c3013_har,
   c3013_r, c3013_e', c3013_f1, leafS2_of_sq c3013_s2, leafS3_of_sq c3013_s3,
   c3013_iso, leafR8_of_sq c3013_nof2 c3013_nof3 c3013_nof4z⟩
theorem not_tile'_3013 (D : CongruentDissection 3013) : False :=
  not_tile_of_conditions' 3013 C'_3013 D

end Erdos634.Draft.AllN2

/- AllN2Check288: N = 5001, 5003, 5005, 5006, 5007
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c5001_sqf   : LeafSqf 5001   := by decide +kernel
private theorem c5001_range : LeafRange 5001  := by decide +kernel
private theorem c5001_ell   : LeafEll 5001    := by decide +kernel
private theorem c5001_nsq   : NSqChkSq 5001   := by decide +kernel
private theorem c5001_har   : HArithChkSq 5001 := by decide +kernel
private theorem c5001_r     : LeafR 5001      := by decide +kernel
private theorem c5001_e'    : LeafE' 5001     := by decide +kernel
private theorem c5001_f1    : LeafF1 5001     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c5001_s2    : S2ChkSq 5001    := by decide +kernel
private theorem c5001_s3    : S3ChkSq 5001    := by decide +kernel
private theorem c5001_iso   : LeafIso 5001    := by decide +kernel
private theorem c5001_nof2  : NoF2ChkSq 5001  := by decide +kernel
private theorem c5001_nof3  : NoF3ChkSq 5001  := by decide +kernel
private theorem c5001_nof4z : NoF4zChkSq 5001 := by decide +kernel
theorem C'_5001 : C' 5001 :=
  ⟨c5001_sqf, c5001_range, c5001_ell, leafNSq_of_sq c5001_nsq, leafHAr_of_sq c5001_har,
   c5001_r, c5001_e', c5001_f1, leafS2_of_sq c5001_s2, leafS3_of_sq c5001_s3,
   c5001_iso, leafR8_of_sq c5001_nof2 c5001_nof3 c5001_nof4z⟩
theorem not_tile'_5001 (D : CongruentDissection 5001) : False :=
  not_tile_of_conditions' 5001 C'_5001 D

private theorem c5003_sqf   : LeafSqf 5003   := by decide +kernel
private theorem c5003_range : LeafRange 5003  := by decide +kernel
private theorem c5003_ell   : LeafEll 5003    := by decide +kernel
private theorem c5003_nsq   : NSqChkSq 5003   := by decide +kernel
private theorem c5003_har   : HArithChkSq 5003 := by decide +kernel
private theorem c5003_r     : LeafR 5003      := by decide +kernel
private theorem c5003_e'    : LeafE' 5003     := by decide +kernel
private theorem c5003_f1    : LeafF1 5003     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c5003_s2    : S2ChkSq 5003    := by decide +kernel
private theorem c5003_s3    : S3ChkSq 5003    := by decide +kernel
private theorem c5003_iso   : LeafIso 5003    := by decide +kernel
private theorem c5003_nof2  : NoF2ChkSq 5003  := by decide +kernel
private theorem c5003_nof3  : NoF3ChkSq 5003  := by decide +kernel
private theorem c5003_nof4z : NoF4zChkSq 5003 := by decide +kernel
theorem C'_5003 : C' 5003 :=
  ⟨c5003_sqf, c5003_range, c5003_ell, leafNSq_of_sq c5003_nsq, leafHAr_of_sq c5003_har,
   c5003_r, c5003_e', c5003_f1, leafS2_of_sq c5003_s2, leafS3_of_sq c5003_s3,
   c5003_iso, leafR8_of_sq c5003_nof2 c5003_nof3 c5003_nof4z⟩
theorem not_tile'_5003 (D : CongruentDissection 5003) : False :=
  not_tile_of_conditions' 5003 C'_5003 D

private theorem c5005_sqf   : LeafSqf 5005   := by decide +kernel
private theorem c5005_range : LeafRange 5005  := by decide +kernel
private theorem c5005_ell   : LeafEll 5005    := by decide +kernel
private theorem c5005_nsq   : NSqChkSq 5005   := by decide +kernel
private theorem c5005_har   : HArithChkSq 5005 := by decide +kernel
private theorem c5005_r     : LeafR 5005      := by decide +kernel
private theorem c5005_e'    : LeafE' 5005     := by decide +kernel
private theorem c5005_f1    : LeafF1 5005     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c5005_s2    : S2ChkSq 5005    := by decide +kernel
private theorem c5005_s3    : S3ChkSq 5005    := by decide +kernel
private theorem c5005_iso   : LeafIso 5005    := by decide +kernel
private theorem c5005_nof2  : NoF2ChkSq 5005  := by decide +kernel
private theorem c5005_nof3  : NoF3ChkSq 5005  := by decide +kernel
private theorem c5005_nof4z : NoF4zChkSq 5005 := by decide +kernel
theorem C'_5005 : C' 5005 :=
  ⟨c5005_sqf, c5005_range, c5005_ell, leafNSq_of_sq c5005_nsq, leafHAr_of_sq c5005_har,
   c5005_r, c5005_e', c5005_f1, leafS2_of_sq c5005_s2, leafS3_of_sq c5005_s3,
   c5005_iso, leafR8_of_sq c5005_nof2 c5005_nof3 c5005_nof4z⟩
theorem not_tile'_5005 (D : CongruentDissection 5005) : False :=
  not_tile_of_conditions' 5005 C'_5005 D

private theorem c5006_sqf   : LeafSqf 5006   := by decide +kernel
private theorem c5006_range : LeafRange 5006  := by decide +kernel
private theorem c5006_ell   : LeafEll 5006    := by decide +kernel
private theorem c5006_nsq   : NSqChkSq 5006   := by decide +kernel
private theorem c5006_har   : HArithChkSq 5006 := by decide +kernel
private theorem c5006_r     : LeafR 5006      := by decide +kernel
private theorem c5006_e'    : LeafE' 5006     := by decide +kernel
private theorem c5006_f1    : LeafF1 5006     := Or.inl (by decide)
private theorem c5006_s2    : S2ChkSq 5006    := by decide +kernel
private theorem c5006_s3    : S3ChkSq 5006    := by decide +kernel
private theorem c5006_iso   : LeafIso 5006    := by decide +kernel
private theorem c5006_nof2  : NoF2ChkSq 5006  := by decide +kernel
private theorem c5006_nof3  : NoF3ChkSq 5006  := by decide +kernel
private theorem c5006_nof4z : NoF4zChkSq 5006 := by decide +kernel
theorem C'_5006 : C' 5006 :=
  ⟨c5006_sqf, c5006_range, c5006_ell, leafNSq_of_sq c5006_nsq, leafHAr_of_sq c5006_har,
   c5006_r, c5006_e', c5006_f1, leafS2_of_sq c5006_s2, leafS3_of_sq c5006_s3,
   c5006_iso, leafR8_of_sq c5006_nof2 c5006_nof3 c5006_nof4z⟩
theorem not_tile'_5006 (D : CongruentDissection 5006) : False :=
  not_tile_of_conditions' 5006 C'_5006 D

private theorem c5007_sqf   : LeafSqf 5007   := by decide +kernel
private theorem c5007_range : LeafRange 5007  := by decide +kernel
private theorem c5007_ell   : LeafEll 5007    := by decide +kernel
private theorem c5007_nsq   : NSqChkSq 5007   := by decide +kernel
private theorem c5007_har   : HArithChkSq 5007 := by decide +kernel
private theorem c5007_r     : LeafR 5007      := by decide +kernel
private theorem c5007_e'    : LeafE' 5007     := by decide +kernel
private theorem c5007_f1    : LeafF1 5007     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c5007_s2    : S2ChkSq 5007    := by decide +kernel
private theorem c5007_s3    : S3ChkSq 5007    := by decide +kernel
private theorem c5007_iso   : LeafIso 5007    := by decide +kernel
private theorem c5007_nof2  : NoF2ChkSq 5007  := by decide +kernel
private theorem c5007_nof3  : NoF3ChkSq 5007  := by decide +kernel
private theorem c5007_nof4z : NoF4zChkSq 5007 := by decide +kernel
theorem C'_5007 : C' 5007 :=
  ⟨c5007_sqf, c5007_range, c5007_ell, leafNSq_of_sq c5007_nsq, leafHAr_of_sq c5007_har,
   c5007_r, c5007_e', c5007_f1, leafS2_of_sq c5007_s2, leafS3_of_sq c5007_s3,
   c5007_iso, leafR8_of_sq c5007_nof2 c5007_nof3 c5007_nof4z⟩
theorem not_tile'_5007 (D : CongruentDissection 5007) : False :=
  not_tile_of_conditions' 5007 C'_5007 D

end Erdos634.Draft.AllN2

/- AllN2Check23: N = 1001, 1011, 1015, 1023, 1041
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1001_sqf   : LeafSqf 1001   := by decide +kernel
private theorem c1001_range : LeafRange 1001  := by decide +kernel
private theorem c1001_ell   : LeafEll 1001    := by decide +kernel
private theorem c1001_nsq   : NSqChkSq 1001   := by decide +kernel
private theorem c1001_har   : HArithChkSq 1001 := by decide +kernel
private theorem c1001_r     : LeafR 1001      := by decide +kernel
private theorem c1001_e'    : LeafE' 1001     := by decide +kernel
private theorem c1001_f1    : LeafF1 1001     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1001_s2    : S2ChkSq 1001    := by decide +kernel
private theorem c1001_s3    : S3ChkSq 1001    := by decide +kernel
private theorem c1001_iso   : LeafIso 1001    := by decide +kernel
private theorem c1001_nof2  : NoF2ChkSq 1001  := by decide +kernel
private theorem c1001_nof3  : NoF3ChkSq 1001  := by decide +kernel
private theorem c1001_nof4z : NoF4zChkSq 1001 := by decide +kernel
theorem C'_1001 : C' 1001 :=
  ⟨c1001_sqf, c1001_range, c1001_ell, leafNSq_of_sq c1001_nsq, leafHAr_of_sq c1001_har,
   c1001_r, c1001_e', c1001_f1, leafS2_of_sq c1001_s2, leafS3_of_sq c1001_s3,
   c1001_iso, leafR8_of_sq c1001_nof2 c1001_nof3 c1001_nof4z⟩
theorem not_tile'_1001 (D : CongruentDissection 1001) : False :=
  not_tile_of_conditions' 1001 C'_1001 D

private theorem c1011_sqf   : LeafSqf 1011   := by decide +kernel
private theorem c1011_range : LeafRange 1011  := by decide +kernel
private theorem c1011_ell   : LeafEll 1011    := by decide +kernel
private theorem c1011_nsq   : NSqChkSq 1011   := by decide +kernel
private theorem c1011_har   : HArithChkSq 1011 := by decide +kernel
private theorem c1011_r     : LeafR 1011      := by decide +kernel
private theorem c1011_e'    : LeafE' 1011     := by decide +kernel
private theorem c1011_f1    : LeafF1 1011     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1011_s2    : S2ChkSq 1011    := by decide +kernel
private theorem c1011_s3    : S3ChkSq 1011    := by decide +kernel
private theorem c1011_iso   : LeafIso 1011    := by decide +kernel
private theorem c1011_nof2  : NoF2ChkSq 1011  := by decide +kernel
private theorem c1011_nof3  : NoF3ChkSq 1011  := by decide +kernel
private theorem c1011_nof4z : NoF4zChkSq 1011 := by decide +kernel
theorem C'_1011 : C' 1011 :=
  ⟨c1011_sqf, c1011_range, c1011_ell, leafNSq_of_sq c1011_nsq, leafHAr_of_sq c1011_har,
   c1011_r, c1011_e', c1011_f1, leafS2_of_sq c1011_s2, leafS3_of_sq c1011_s3,
   c1011_iso, leafR8_of_sq c1011_nof2 c1011_nof3 c1011_nof4z⟩
theorem not_tile'_1011 (D : CongruentDissection 1011) : False :=
  not_tile_of_conditions' 1011 C'_1011 D

private theorem c1015_sqf   : LeafSqf 1015   := by decide +kernel
private theorem c1015_range : LeafRange 1015  := by decide +kernel
private theorem c1015_ell   : LeafEll 1015    := by decide +kernel
private theorem c1015_nsq   : NSqChkSq 1015   := by decide +kernel
private theorem c1015_har   : HArithChkSq 1015 := by decide +kernel
private theorem c1015_r     : LeafR 1015      := by decide +kernel
private theorem c1015_e'    : LeafE' 1015     := by decide +kernel
private theorem c1015_f1    : LeafF1 1015     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1015_s2    : S2ChkSq 1015    := by decide +kernel
private theorem c1015_s3    : S3ChkSq 1015    := by decide +kernel
private theorem c1015_iso   : LeafIso 1015    := by decide +kernel
private theorem c1015_nof2  : NoF2ChkSq 1015  := by decide +kernel
private theorem c1015_nof3  : NoF3ChkSq 1015  := by decide +kernel
private theorem c1015_nof4z : NoF4zChkSq 1015 := by decide +kernel
theorem C'_1015 : C' 1015 :=
  ⟨c1015_sqf, c1015_range, c1015_ell, leafNSq_of_sq c1015_nsq, leafHAr_of_sq c1015_har,
   c1015_r, c1015_e', c1015_f1, leafS2_of_sq c1015_s2, leafS3_of_sq c1015_s3,
   c1015_iso, leafR8_of_sq c1015_nof2 c1015_nof3 c1015_nof4z⟩
theorem not_tile'_1015 (D : CongruentDissection 1015) : False :=
  not_tile_of_conditions' 1015 C'_1015 D

private theorem c1023_sqf   : LeafSqf 1023   := by decide +kernel
private theorem c1023_range : LeafRange 1023  := by decide +kernel
private theorem c1023_ell   : LeafEll 1023    := by decide +kernel
private theorem c1023_nsq   : NSqChkSq 1023   := by decide +kernel
private theorem c1023_har   : HArithChkSq 1023 := by decide +kernel
private theorem c1023_r     : LeafR 1023      := by decide +kernel
private theorem c1023_e'    : LeafE' 1023     := by decide +kernel
private theorem c1023_f1    : LeafF1 1023     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1023_s2    : S2ChkSq 1023    := by decide +kernel
private theorem c1023_s3    : S3ChkSq 1023    := by decide +kernel
private theorem c1023_iso   : LeafIso 1023    := by decide +kernel
private theorem c1023_nof2  : NoF2ChkSq 1023  := by decide +kernel
private theorem c1023_nof3  : NoF3ChkSq 1023  := by decide +kernel
private theorem c1023_nof4z : NoF4zChkSq 1023 := by decide +kernel
theorem C'_1023 : C' 1023 :=
  ⟨c1023_sqf, c1023_range, c1023_ell, leafNSq_of_sq c1023_nsq, leafHAr_of_sq c1023_har,
   c1023_r, c1023_e', c1023_f1, leafS2_of_sq c1023_s2, leafS3_of_sq c1023_s3,
   c1023_iso, leafR8_of_sq c1023_nof2 c1023_nof3 c1023_nof4z⟩
theorem not_tile'_1023 (D : CongruentDissection 1023) : False :=
  not_tile_of_conditions' 1023 C'_1023 D

private theorem c1041_sqf   : LeafSqf 1041   := by decide +kernel
private theorem c1041_range : LeafRange 1041  := by decide +kernel
private theorem c1041_ell   : LeafEll 1041    := by decide +kernel
private theorem c1041_nsq   : NSqChkSq 1041   := by decide +kernel
private theorem c1041_har   : HArithChkSq 1041 := by decide +kernel
private theorem c1041_r     : LeafR 1041      := by decide +kernel
private theorem c1041_e'    : LeafE' 1041     := by decide +kernel
private theorem c1041_f1    : LeafF1 1041     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1041_s2    : S2ChkSq 1041    := by decide +kernel
private theorem c1041_s3    : S3ChkSq 1041    := by decide +kernel
private theorem c1041_iso   : LeafIso 1041    := by decide +kernel
private theorem c1041_nof2  : NoF2ChkSq 1041  := by decide +kernel
private theorem c1041_nof3  : NoF3ChkSq 1041  := by decide +kernel
private theorem c1041_nof4z : NoF4zChkSq 1041 := by decide +kernel
theorem C'_1041 : C' 1041 :=
  ⟨c1041_sqf, c1041_range, c1041_ell, leafNSq_of_sq c1041_nsq, leafHAr_of_sq c1041_har,
   c1041_r, c1041_e', c1041_f1, leafS2_of_sq c1041_s2, leafS3_of_sq c1041_s3,
   c1041_iso, leafR8_of_sq c1041_nof2 c1041_nof3 c1041_nof4z⟩
theorem not_tile'_1041 (D : CongruentDissection 1041) : False :=
  not_tile_of_conditions' 1041 C'_1041 D

end Erdos634.Draft.AllN2

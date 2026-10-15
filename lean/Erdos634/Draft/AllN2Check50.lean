/- AllN2Check50: N = 1967, 1969, 1977, 1981, 1983
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c1967_sqf   : LeafSqf 1967   := by decide +kernel
private theorem c1967_range : LeafRange 1967  := by decide +kernel
private theorem c1967_ell   : LeafEll 1967    := by decide +kernel
private theorem c1967_nsq   : NSqChkSq 1967   := by decide +kernel
private theorem c1967_har   : HArithChkSq 1967 := by decide +kernel
private theorem c1967_r     : LeafR 1967      := by decide +kernel
private theorem c1967_e'    : LeafE' 1967     := by decide +kernel
private theorem c1967_f1    : LeafF1 1967     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1967_s2    : S2ChkSq 1967    := by decide +kernel
private theorem c1967_s3    : S3ChkSq 1967    := by decide +kernel
private theorem c1967_iso   : LeafIso 1967    := by decide +kernel
private theorem c1967_nof2  : NoF2ChkSq 1967  := by decide +kernel
private theorem c1967_nof3  : NoF3ChkSq 1967  := by decide +kernel
private theorem c1967_nof4z : NoF4zChkSq 1967 := by decide +kernel
theorem C'_1967 : C' 1967 :=
  ⟨c1967_sqf, c1967_range, c1967_ell, leafNSq_of_sq c1967_nsq, leafHAr_of_sq c1967_har,
   c1967_r, c1967_e', c1967_f1, leafS2_of_sq c1967_s2, leafS3_of_sq c1967_s3,
   c1967_iso, leafR8_of_sq c1967_nof2 c1967_nof3 c1967_nof4z⟩
theorem not_tile'_1967 (D : CongruentDissection 1967) : False :=
  not_tile_of_conditions' 1967 C'_1967 D

private theorem c1969_sqf   : LeafSqf 1969   := by decide +kernel
private theorem c1969_range : LeafRange 1969  := by decide +kernel
private theorem c1969_ell   : LeafEll 1969    := by decide +kernel
private theorem c1969_nsq   : NSqChkSq 1969   := by decide +kernel
private theorem c1969_har   : HArithChkSq 1969 := by decide +kernel
private theorem c1969_r     : LeafR 1969      := by decide +kernel
private theorem c1969_e'    : LeafE' 1969     := by decide +kernel
private theorem c1969_f1    : LeafF1 1969     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1969_s2    : S2ChkSq 1969    := by decide +kernel
private theorem c1969_s3    : S3ChkSq 1969    := by decide +kernel
private theorem c1969_iso   : LeafIso 1969    := by decide +kernel
private theorem c1969_nof2  : NoF2ChkSq 1969  := by decide +kernel
private theorem c1969_nof3  : NoF3ChkSq 1969  := by decide +kernel
private theorem c1969_nof4z : NoF4zChkSq 1969 := by decide +kernel
theorem C'_1969 : C' 1969 :=
  ⟨c1969_sqf, c1969_range, c1969_ell, leafNSq_of_sq c1969_nsq, leafHAr_of_sq c1969_har,
   c1969_r, c1969_e', c1969_f1, leafS2_of_sq c1969_s2, leafS3_of_sq c1969_s3,
   c1969_iso, leafR8_of_sq c1969_nof2 c1969_nof3 c1969_nof4z⟩
theorem not_tile'_1969 (D : CongruentDissection 1969) : False :=
  not_tile_of_conditions' 1969 C'_1969 D

private theorem c1977_sqf   : LeafSqf 1977   := by decide +kernel
private theorem c1977_range : LeafRange 1977  := by decide +kernel
private theorem c1977_ell   : LeafEll 1977    := by decide +kernel
private theorem c1977_nsq   : NSqChkSq 1977   := by decide +kernel
private theorem c1977_har   : HArithChkSq 1977 := by decide +kernel
private theorem c1977_r     : LeafR 1977      := by decide +kernel
private theorem c1977_e'    : LeafE' 1977     := by decide +kernel
private theorem c1977_f1    : LeafF1 1977     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1977_s2    : S2ChkSq 1977    := by decide +kernel
private theorem c1977_s3    : S3ChkSq 1977    := by decide +kernel
private theorem c1977_iso   : LeafIso 1977    := by decide +kernel
private theorem c1977_nof2  : NoF2ChkSq 1977  := by decide +kernel
private theorem c1977_nof3  : NoF3ChkSq 1977  := by decide +kernel
private theorem c1977_nof4z : NoF4zChkSq 1977 := by decide +kernel
theorem C'_1977 : C' 1977 :=
  ⟨c1977_sqf, c1977_range, c1977_ell, leafNSq_of_sq c1977_nsq, leafHAr_of_sq c1977_har,
   c1977_r, c1977_e', c1977_f1, leafS2_of_sq c1977_s2, leafS3_of_sq c1977_s3,
   c1977_iso, leafR8_of_sq c1977_nof2 c1977_nof3 c1977_nof4z⟩
theorem not_tile'_1977 (D : CongruentDissection 1977) : False :=
  not_tile_of_conditions' 1977 C'_1977 D

private theorem c1981_sqf   : LeafSqf 1981   := by decide +kernel
private theorem c1981_range : LeafRange 1981  := by decide +kernel
private theorem c1981_ell   : LeafEll 1981    := by decide +kernel
private theorem c1981_nsq   : NSqChkSq 1981   := by decide +kernel
private theorem c1981_har   : HArithChkSq 1981 := by decide +kernel
private theorem c1981_r     : LeafR 1981      := by decide +kernel
private theorem c1981_e'    : LeafE' 1981     := by decide +kernel
private theorem c1981_f1    : LeafF1 1981     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1981_s2    : S2ChkSq 1981    := by decide +kernel
private theorem c1981_s3    : S3ChkSq 1981    := by decide +kernel
private theorem c1981_iso   : LeafIso 1981    := by decide +kernel
private theorem c1981_nof2  : NoF2ChkSq 1981  := by decide +kernel
private theorem c1981_nof3  : NoF3ChkSq 1981  := by decide +kernel
private theorem c1981_nof4z : NoF4zChkSq 1981 := by decide +kernel
theorem C'_1981 : C' 1981 :=
  ⟨c1981_sqf, c1981_range, c1981_ell, leafNSq_of_sq c1981_nsq, leafHAr_of_sq c1981_har,
   c1981_r, c1981_e', c1981_f1, leafS2_of_sq c1981_s2, leafS3_of_sq c1981_s3,
   c1981_iso, leafR8_of_sq c1981_nof2 c1981_nof3 c1981_nof4z⟩
theorem not_tile'_1981 (D : CongruentDissection 1981) : False :=
  not_tile_of_conditions' 1981 C'_1981 D

private theorem c1983_sqf   : LeafSqf 1983   := by decide +kernel
private theorem c1983_range : LeafRange 1983  := by decide +kernel
private theorem c1983_ell   : LeafEll 1983    := by decide +kernel
private theorem c1983_nsq   : NSqChkSq 1983   := by decide +kernel
private theorem c1983_har   : HArithChkSq 1983 := by decide +kernel
private theorem c1983_r     : LeafR 1983      := by decide +kernel
private theorem c1983_e'    : LeafE' 1983     := by decide +kernel
private theorem c1983_f1    : LeafF1 1983     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c1983_s2    : S2ChkSq 1983    := by decide +kernel
private theorem c1983_s3    : S3ChkSq 1983    := by decide +kernel
private theorem c1983_iso   : LeafIso 1983    := by decide +kernel
private theorem c1983_nof2  : NoF2ChkSq 1983  := by decide +kernel
private theorem c1983_nof3  : NoF3ChkSq 1983  := by decide +kernel
private theorem c1983_nof4z : NoF4zChkSq 1983 := by decide +kernel
theorem C'_1983 : C' 1983 :=
  ⟨c1983_sqf, c1983_range, c1983_ell, leafNSq_of_sq c1983_nsq, leafHAr_of_sq c1983_har,
   c1983_r, c1983_e', c1983_f1, leafS2_of_sq c1983_s2, leafS3_of_sq c1983_s3,
   c1983_iso, leafR8_of_sq c1983_nof2 c1983_nof3 c1983_nof4z⟩
theorem not_tile'_1983 (D : CongruentDissection 1983) : False :=
  not_tile_of_conditions' 1983 C'_1983 D

end Erdos634.Draft.AllN2

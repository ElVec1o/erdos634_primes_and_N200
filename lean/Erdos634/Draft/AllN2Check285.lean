/- AllN2Check285: N = 4971, 4974, 4978, 4979, 4982
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4971_sqf   : LeafSqf 4971   := by decide +kernel
private theorem c4971_range : LeafRange 4971  := by decide +kernel
private theorem c4971_ell   : LeafEll 4971    := by decide +kernel
private theorem c4971_nsq   : NSqChkSq 4971   := by decide +kernel
private theorem c4971_har   : HArithChkSq 4971 := by decide +kernel
private theorem c4971_r     : LeafR 4971      := by decide +kernel
private theorem c4971_e'    : LeafE' 4971     := by decide +kernel
private theorem c4971_f1    : LeafF1 4971     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4971_s2    : S2ChkSq 4971    := by decide +kernel
private theorem c4971_s3    : S3ChkSq 4971    := by decide +kernel
private theorem c4971_iso   : LeafIso 4971    := by decide +kernel
private theorem c4971_nof2  : NoF2ChkSq 4971  := by decide +kernel
private theorem c4971_nof3  : NoF3ChkSq 4971  := by decide +kernel
private theorem c4971_nof4z : NoF4zChkSq 4971 := by decide +kernel
theorem C'_4971 : C' 4971 :=
  ⟨c4971_sqf, c4971_range, c4971_ell, leafNSq_of_sq c4971_nsq, leafHAr_of_sq c4971_har,
   c4971_r, c4971_e', c4971_f1, leafS2_of_sq c4971_s2, leafS3_of_sq c4971_s3,
   c4971_iso, leafR8_of_sq c4971_nof2 c4971_nof3 c4971_nof4z⟩
theorem not_tile'_4971 (D : CongruentDissection 4971) : False :=
  not_tile_of_conditions' 4971 C'_4971 D

private theorem c4974_sqf   : LeafSqf 4974   := by decide +kernel
private theorem c4974_range : LeafRange 4974  := by decide +kernel
private theorem c4974_ell   : LeafEll 4974    := by decide +kernel
private theorem c4974_nsq   : NSqChkSq 4974   := by decide +kernel
private theorem c4974_har   : HArithChkSq 4974 := by decide +kernel
private theorem c4974_r     : LeafR 4974      := by decide +kernel
private theorem c4974_e'    : LeafE' 4974     := by decide +kernel
private theorem c4974_f1    : LeafF1 4974     := Or.inl (by decide)
private theorem c4974_s2    : S2ChkSq 4974    := by decide +kernel
private theorem c4974_s3    : S3ChkSq 4974    := by decide +kernel
private theorem c4974_iso   : LeafIso 4974    := by decide +kernel
private theorem c4974_nof2  : NoF2ChkSq 4974  := by decide +kernel
private theorem c4974_nof3  : NoF3ChkSq 4974  := by decide +kernel
private theorem c4974_nof4z : NoF4zChkSq 4974 := by decide +kernel
theorem C'_4974 : C' 4974 :=
  ⟨c4974_sqf, c4974_range, c4974_ell, leafNSq_of_sq c4974_nsq, leafHAr_of_sq c4974_har,
   c4974_r, c4974_e', c4974_f1, leafS2_of_sq c4974_s2, leafS3_of_sq c4974_s3,
   c4974_iso, leafR8_of_sq c4974_nof2 c4974_nof3 c4974_nof4z⟩
theorem not_tile'_4974 (D : CongruentDissection 4974) : False :=
  not_tile_of_conditions' 4974 C'_4974 D

private theorem c4978_sqf   : LeafSqf 4978   := by decide +kernel
private theorem c4978_range : LeafRange 4978  := by decide +kernel
private theorem c4978_ell   : LeafEll 4978    := by decide +kernel
private theorem c4978_nsq   : NSqChkSq 4978   := by decide +kernel
private theorem c4978_har   : HArithChkSq 4978 := by decide +kernel
private theorem c4978_r     : LeafR 4978      := by decide +kernel
private theorem c4978_e'    : LeafE' 4978     := by decide +kernel
private theorem c4978_f1    : LeafF1 4978     := Or.inl (by decide)
private theorem c4978_s2    : S2ChkSq 4978    := by decide +kernel
private theorem c4978_s3    : S3ChkSq 4978    := by decide +kernel
private theorem c4978_iso   : LeafIso 4978    := by decide +kernel
private theorem c4978_nof2  : NoF2ChkSq 4978  := by decide +kernel
private theorem c4978_nof3  : NoF3ChkSq 4978  := by decide +kernel
private theorem c4978_nof4z : NoF4zChkSq 4978 := by decide +kernel
theorem C'_4978 : C' 4978 :=
  ⟨c4978_sqf, c4978_range, c4978_ell, leafNSq_of_sq c4978_nsq, leafHAr_of_sq c4978_har,
   c4978_r, c4978_e', c4978_f1, leafS2_of_sq c4978_s2, leafS3_of_sq c4978_s3,
   c4978_iso, leafR8_of_sq c4978_nof2 c4978_nof3 c4978_nof4z⟩
theorem not_tile'_4978 (D : CongruentDissection 4978) : False :=
  not_tile_of_conditions' 4978 C'_4978 D

private theorem c4979_sqf   : LeafSqf 4979   := by decide +kernel
private theorem c4979_range : LeafRange 4979  := by decide +kernel
private theorem c4979_ell   : LeafEll 4979    := by decide +kernel
private theorem c4979_nsq   : NSqChkSq 4979   := by decide +kernel
private theorem c4979_har   : HArithChkSq 4979 := by decide +kernel
private theorem c4979_r     : LeafR 4979      := by decide +kernel
private theorem c4979_e'    : LeafE' 4979     := by decide +kernel
private theorem c4979_f1    : LeafF1 4979     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4979_s2    : S2ChkSq 4979    := by decide +kernel
private theorem c4979_s3    : S3ChkSq 4979    := by decide +kernel
private theorem c4979_iso   : LeafIso 4979    := by decide +kernel
private theorem c4979_nof2  : NoF2ChkSq 4979  := by decide +kernel
private theorem c4979_nof3  : NoF3ChkSq 4979  := by decide +kernel
private theorem c4979_nof4z : NoF4zChkSq 4979 := by decide +kernel
theorem C'_4979 : C' 4979 :=
  ⟨c4979_sqf, c4979_range, c4979_ell, leafNSq_of_sq c4979_nsq, leafHAr_of_sq c4979_har,
   c4979_r, c4979_e', c4979_f1, leafS2_of_sq c4979_s2, leafS3_of_sq c4979_s3,
   c4979_iso, leafR8_of_sq c4979_nof2 c4979_nof3 c4979_nof4z⟩
theorem not_tile'_4979 (D : CongruentDissection 4979) : False :=
  not_tile_of_conditions' 4979 C'_4979 D

private theorem c4982_sqf   : LeafSqf 4982   := by decide +kernel
private theorem c4982_range : LeafRange 4982  := by decide +kernel
private theorem c4982_ell   : LeafEll 4982    := by decide +kernel
private theorem c4982_nsq   : NSqChkSq 4982   := by decide +kernel
private theorem c4982_har   : HArithChkSq 4982 := by decide +kernel
private theorem c4982_r     : LeafR 4982      := by decide +kernel
private theorem c4982_e'    : LeafE' 4982     := by decide +kernel
private theorem c4982_f1    : LeafF1 4982     := Or.inl (by decide)
private theorem c4982_s2    : S2ChkSq 4982    := by decide +kernel
private theorem c4982_s3    : S3ChkSq 4982    := by decide +kernel
private theorem c4982_iso   : LeafIso 4982    := by decide +kernel
private theorem c4982_nof2  : NoF2ChkSq 4982  := by decide +kernel
private theorem c4982_nof3  : NoF3ChkSq 4982  := by decide +kernel
private theorem c4982_nof4z : NoF4zChkSq 4982 := by decide +kernel
theorem C'_4982 : C' 4982 :=
  ⟨c4982_sqf, c4982_range, c4982_ell, leafNSq_of_sq c4982_nsq, leafHAr_of_sq c4982_har,
   c4982_r, c4982_e', c4982_f1, leafS2_of_sq c4982_s2, leafS3_of_sq c4982_s3,
   c4982_iso, leafR8_of_sq c4982_nof2 c4982_nof3 c4982_nof4z⟩
theorem not_tile'_4982 (D : CongruentDissection 4982) : False :=
  not_tile_of_conditions' 4982 C'_4982 D

end Erdos634.Draft.AllN2

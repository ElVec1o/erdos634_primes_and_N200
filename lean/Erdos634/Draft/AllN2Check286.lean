/- AllN2Check286: N = 4987, 4989, 4990, 4991, 4994
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4987_sqf   : LeafSqf 4987   := by decide +kernel
private theorem c4987_range : LeafRange 4987  := by decide +kernel
private theorem c4987_ell   : LeafEll 4987    := by decide +kernel
private theorem c4987_nsq   : NSqChkSq 4987   := by decide +kernel
private theorem c4987_har   : HArithChkSq 4987 := by decide +kernel
private theorem c4987_r     : LeafR 4987      := by decide +kernel
private theorem c4987_e'    : LeafE' 4987     := by decide +kernel
private theorem c4987_f1    : LeafF1 4987     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4987_s2    : S2ChkSq 4987    := by decide +kernel
private theorem c4987_s3    : S3ChkSq 4987    := by decide +kernel
private theorem c4987_iso   : LeafIso 4987    := by decide +kernel
private theorem c4987_nof2  : NoF2ChkSq 4987  := by decide +kernel
private theorem c4987_nof3  : NoF3ChkSq 4987  := by decide +kernel
private theorem c4987_nof4z : NoF4zChkSq 4987 := by decide +kernel
theorem C'_4987 : C' 4987 :=
  ⟨c4987_sqf, c4987_range, c4987_ell, leafNSq_of_sq c4987_nsq, leafHAr_of_sq c4987_har,
   c4987_r, c4987_e', c4987_f1, leafS2_of_sq c4987_s2, leafS3_of_sq c4987_s3,
   c4987_iso, leafR8_of_sq c4987_nof2 c4987_nof3 c4987_nof4z⟩
theorem not_tile'_4987 (D : CongruentDissection 4987) : False :=
  not_tile_of_conditions' 4987 C'_4987 D

private theorem c4989_sqf   : LeafSqf 4989   := by decide +kernel
private theorem c4989_range : LeafRange 4989  := by decide +kernel
private theorem c4989_ell   : LeafEll 4989    := by decide +kernel
private theorem c4989_nsq   : NSqChkSq 4989   := by decide +kernel
private theorem c4989_har   : HArithChkSq 4989 := by decide +kernel
private theorem c4989_r     : LeafR 4989      := by decide +kernel
private theorem c4989_e'    : LeafE' 4989     := by decide +kernel
private theorem c4989_f1    : LeafF1 4989     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4989_s2    : S2ChkSq 4989    := by decide +kernel
private theorem c4989_s3    : S3ChkSq 4989    := by decide +kernel
private theorem c4989_iso   : LeafIso 4989    := by decide +kernel
private theorem c4989_nof2  : NoF2ChkSq 4989  := by decide +kernel
private theorem c4989_nof3  : NoF3ChkSq 4989  := by decide +kernel
private theorem c4989_nof4z : NoF4zChkSq 4989 := by decide +kernel
theorem C'_4989 : C' 4989 :=
  ⟨c4989_sqf, c4989_range, c4989_ell, leafNSq_of_sq c4989_nsq, leafHAr_of_sq c4989_har,
   c4989_r, c4989_e', c4989_f1, leafS2_of_sq c4989_s2, leafS3_of_sq c4989_s3,
   c4989_iso, leafR8_of_sq c4989_nof2 c4989_nof3 c4989_nof4z⟩
theorem not_tile'_4989 (D : CongruentDissection 4989) : False :=
  not_tile_of_conditions' 4989 C'_4989 D

private theorem c4990_sqf   : LeafSqf 4990   := by decide +kernel
private theorem c4990_range : LeafRange 4990  := by decide +kernel
private theorem c4990_ell   : LeafEll 4990    := by decide +kernel
private theorem c4990_nsq   : NSqChkSq 4990   := by decide +kernel
private theorem c4990_har   : HArithChkSq 4990 := by decide +kernel
private theorem c4990_r     : LeafR 4990      := by decide +kernel
private theorem c4990_e'    : LeafE' 4990     := by decide +kernel
private theorem c4990_f1    : LeafF1 4990     := Or.inl (by decide)
private theorem c4990_s2    : S2ChkSq 4990    := by decide +kernel
private theorem c4990_s3    : S3ChkSq 4990    := by decide +kernel
private theorem c4990_iso   : LeafIso 4990    := by decide +kernel
private theorem c4990_nof2  : NoF2ChkSq 4990  := by decide +kernel
private theorem c4990_nof3  : NoF3ChkSq 4990  := by decide +kernel
private theorem c4990_nof4z : NoF4zChkSq 4990 := by decide +kernel
theorem C'_4990 : C' 4990 :=
  ⟨c4990_sqf, c4990_range, c4990_ell, leafNSq_of_sq c4990_nsq, leafHAr_of_sq c4990_har,
   c4990_r, c4990_e', c4990_f1, leafS2_of_sq c4990_s2, leafS3_of_sq c4990_s3,
   c4990_iso, leafR8_of_sq c4990_nof2 c4990_nof3 c4990_nof4z⟩
theorem not_tile'_4990 (D : CongruentDissection 4990) : False :=
  not_tile_of_conditions' 4990 C'_4990 D

private theorem c4991_sqf   : LeafSqf 4991   := by decide +kernel
private theorem c4991_range : LeafRange 4991  := by decide +kernel
private theorem c4991_ell   : LeafEll 4991    := by decide +kernel
private theorem c4991_nsq   : NSqChkSq 4991   := by decide +kernel
private theorem c4991_har   : HArithChkSq 4991 := by decide +kernel
private theorem c4991_r     : LeafR 4991      := by decide +kernel
private theorem c4991_e'    : LeafE' 4991     := by decide +kernel
private theorem c4991_f1    : LeafF1 4991     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4991_s2    : S2ChkSq 4991    := by decide +kernel
private theorem c4991_s3    : S3ChkSq 4991    := by decide +kernel
private theorem c4991_iso   : LeafIso 4991    := by decide +kernel
private theorem c4991_nof2  : NoF2ChkSq 4991  := by decide +kernel
private theorem c4991_nof3  : NoF3ChkSq 4991  := by decide +kernel
private theorem c4991_nof4z : NoF4zChkSq 4991 := by decide +kernel
theorem C'_4991 : C' 4991 :=
  ⟨c4991_sqf, c4991_range, c4991_ell, leafNSq_of_sq c4991_nsq, leafHAr_of_sq c4991_har,
   c4991_r, c4991_e', c4991_f1, leafS2_of_sq c4991_s2, leafS3_of_sq c4991_s3,
   c4991_iso, leafR8_of_sq c4991_nof2 c4991_nof3 c4991_nof4z⟩
theorem not_tile'_4991 (D : CongruentDissection 4991) : False :=
  not_tile_of_conditions' 4991 C'_4991 D

private theorem c4994_sqf   : LeafSqf 4994   := by decide +kernel
private theorem c4994_range : LeafRange 4994  := by decide +kernel
private theorem c4994_ell   : LeafEll 4994    := by decide +kernel
private theorem c4994_nsq   : NSqChkSq 4994   := by decide +kernel
private theorem c4994_har   : HArithChkSq 4994 := by decide +kernel
private theorem c4994_r     : LeafR 4994      := by decide +kernel
private theorem c4994_e'    : LeafE' 4994     := by decide +kernel
private theorem c4994_f1    : LeafF1 4994     := Or.inl (by decide)
private theorem c4994_s2    : S2ChkSq 4994    := by decide +kernel
private theorem c4994_s3    : S3ChkSq 4994    := by decide +kernel
private theorem c4994_iso   : LeafIso 4994    := by decide +kernel
private theorem c4994_nof2  : NoF2ChkSq 4994  := by decide +kernel
private theorem c4994_nof3  : NoF3ChkSq 4994  := by decide +kernel
private theorem c4994_nof4z : NoF4zChkSq 4994 := by decide +kernel
theorem C'_4994 : C' 4994 :=
  ⟨c4994_sqf, c4994_range, c4994_ell, leafNSq_of_sq c4994_nsq, leafHAr_of_sq c4994_har,
   c4994_r, c4994_e', c4994_f1, leafS2_of_sq c4994_s2, leafS3_of_sq c4994_s3,
   c4994_iso, leafR8_of_sq c4994_nof2 c4994_nof3 c4994_nof4z⟩
theorem not_tile'_4994 (D : CongruentDissection 4994) : False :=
  not_tile_of_conditions' 4994 C'_4994 D

end Erdos634.Draft.AllN2

/- AllN2Check128: N = 2974, 2981, 2983, 2987, 2990
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2974_sqf   : LeafSqf 2974   := by decide +kernel
private theorem c2974_range : LeafRange 2974  := by decide +kernel
private theorem c2974_ell   : LeafEll 2974    := by decide +kernel
private theorem c2974_nsq   : NSqChkSq 2974   := by decide +kernel
private theorem c2974_har   : HArithChkSq 2974 := by decide +kernel
private theorem c2974_r     : LeafR 2974      := by decide +kernel
private theorem c2974_e'    : LeafE' 2974     := by decide +kernel
private theorem c2974_f1    : LeafF1 2974     := Or.inl (by decide)
private theorem c2974_s2    : S2ChkSq 2974    := by decide +kernel
private theorem c2974_s3    : S3ChkSq 2974    := by decide +kernel
private theorem c2974_iso   : LeafIso 2974    := by decide +kernel
private theorem c2974_nof2  : NoF2ChkSq 2974  := by decide +kernel
private theorem c2974_nof3  : NoF3ChkSq 2974  := by decide +kernel
private theorem c2974_nof4z : NoF4zChkSq 2974 := by decide +kernel
theorem C'_2974 : C' 2974 :=
  ⟨c2974_sqf, c2974_range, c2974_ell, leafNSq_of_sq c2974_nsq, leafHAr_of_sq c2974_har,
   c2974_r, c2974_e', c2974_f1, leafS2_of_sq c2974_s2, leafS3_of_sq c2974_s3,
   c2974_iso, leafR8_of_sq c2974_nof2 c2974_nof3 c2974_nof4z⟩
theorem not_tile'_2974 (D : CongruentDissection 2974) : False :=
  not_tile_of_conditions' 2974 C'_2974 D

private theorem c2981_sqf   : LeafSqf 2981   := by decide +kernel
private theorem c2981_range : LeafRange 2981  := by decide +kernel
private theorem c2981_ell   : LeafEll 2981    := by decide +kernel
private theorem c2981_nsq   : NSqChkSq 2981   := by decide +kernel
private theorem c2981_har   : HArithChkSq 2981 := by decide +kernel
private theorem c2981_r     : LeafR 2981      := by decide +kernel
private theorem c2981_e'    : LeafE' 2981     := by decide +kernel
private theorem c2981_f1    : LeafF1 2981     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2981_s2    : S2ChkSq 2981    := by decide +kernel
private theorem c2981_s3    : S3ChkSq 2981    := by decide +kernel
private theorem c2981_iso   : LeafIso 2981    := by decide +kernel
private theorem c2981_nof2  : NoF2ChkSq 2981  := by decide +kernel
private theorem c2981_nof3  : NoF3ChkSq 2981  := by decide +kernel
private theorem c2981_nof4z : NoF4zChkSq 2981 := by decide +kernel
theorem C'_2981 : C' 2981 :=
  ⟨c2981_sqf, c2981_range, c2981_ell, leafNSq_of_sq c2981_nsq, leafHAr_of_sq c2981_har,
   c2981_r, c2981_e', c2981_f1, leafS2_of_sq c2981_s2, leafS3_of_sq c2981_s3,
   c2981_iso, leafR8_of_sq c2981_nof2 c2981_nof3 c2981_nof4z⟩
theorem not_tile'_2981 (D : CongruentDissection 2981) : False :=
  not_tile_of_conditions' 2981 C'_2981 D

private theorem c2983_sqf   : LeafSqf 2983   := by decide +kernel
private theorem c2983_range : LeafRange 2983  := by decide +kernel
private theorem c2983_ell   : LeafEll 2983    := by decide +kernel
private theorem c2983_nsq   : NSqChkSq 2983   := by decide +kernel
private theorem c2983_har   : HArithChkSq 2983 := by decide +kernel
private theorem c2983_r     : LeafR 2983      := by decide +kernel
private theorem c2983_e'    : LeafE' 2983     := by decide +kernel
private theorem c2983_f1    : LeafF1 2983     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2983_s2    : S2ChkSq 2983    := by decide +kernel
private theorem c2983_s3    : S3ChkSq 2983    := by decide +kernel
private theorem c2983_iso   : LeafIso 2983    := by decide +kernel
private theorem c2983_nof2  : NoF2ChkSq 2983  := by decide +kernel
private theorem c2983_nof3  : NoF3ChkSq 2983  := by decide +kernel
private theorem c2983_nof4z : NoF4zChkSq 2983 := by decide +kernel
theorem C'_2983 : C' 2983 :=
  ⟨c2983_sqf, c2983_range, c2983_ell, leafNSq_of_sq c2983_nsq, leafHAr_of_sq c2983_har,
   c2983_r, c2983_e', c2983_f1, leafS2_of_sq c2983_s2, leafS3_of_sq c2983_s3,
   c2983_iso, leafR8_of_sq c2983_nof2 c2983_nof3 c2983_nof4z⟩
theorem not_tile'_2983 (D : CongruentDissection 2983) : False :=
  not_tile_of_conditions' 2983 C'_2983 D

private theorem c2987_sqf   : LeafSqf 2987   := by decide +kernel
private theorem c2987_range : LeafRange 2987  := by decide +kernel
private theorem c2987_ell   : LeafEll 2987    := by decide +kernel
private theorem c2987_nsq   : NSqChkSq 2987   := by decide +kernel
private theorem c2987_har   : HArithChkSq 2987 := by decide +kernel
private theorem c2987_r     : LeafR 2987      := by decide +kernel
private theorem c2987_e'    : LeafE' 2987     := by decide +kernel
private theorem c2987_f1    : LeafF1 2987     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2987_s2    : S2ChkSq 2987    := by decide +kernel
private theorem c2987_s3    : S3ChkSq 2987    := by decide +kernel
private theorem c2987_iso   : LeafIso 2987    := by decide +kernel
private theorem c2987_nof2  : NoF2ChkSq 2987  := by decide +kernel
private theorem c2987_nof3  : NoF3ChkSq 2987  := by decide +kernel
private theorem c2987_nof4z : NoF4zChkSq 2987 := by decide +kernel
theorem C'_2987 : C' 2987 :=
  ⟨c2987_sqf, c2987_range, c2987_ell, leafNSq_of_sq c2987_nsq, leafHAr_of_sq c2987_har,
   c2987_r, c2987_e', c2987_f1, leafS2_of_sq c2987_s2, leafS3_of_sq c2987_s3,
   c2987_iso, leafR8_of_sq c2987_nof2 c2987_nof3 c2987_nof4z⟩
theorem not_tile'_2987 (D : CongruentDissection 2987) : False :=
  not_tile_of_conditions' 2987 C'_2987 D

private theorem c2990_sqf   : LeafSqf 2990   := by decide +kernel
private theorem c2990_range : LeafRange 2990  := by decide +kernel
private theorem c2990_ell   : LeafEll 2990    := by decide +kernel
private theorem c2990_nsq   : NSqChkSq 2990   := by decide +kernel
private theorem c2990_har   : HArithChkSq 2990 := by decide +kernel
private theorem c2990_r     : LeafR 2990      := by decide +kernel
private theorem c2990_e'    : LeafE' 2990     := by decide +kernel
private theorem c2990_f1    : LeafF1 2990     := Or.inl (by decide)
private theorem c2990_s2    : S2ChkSq 2990    := by decide +kernel
private theorem c2990_s3    : S3ChkSq 2990    := by decide +kernel
private theorem c2990_iso   : LeafIso 2990    := by decide +kernel
private theorem c2990_nof2  : NoF2ChkSq 2990  := by decide +kernel
private theorem c2990_nof3  : NoF3ChkSq 2990  := by decide +kernel
private theorem c2990_nof4z : NoF4zChkSq 2990 := by decide +kernel
theorem C'_2990 : C' 2990 :=
  ⟨c2990_sqf, c2990_range, c2990_ell, leafNSq_of_sq c2990_nsq, leafHAr_of_sq c2990_har,
   c2990_r, c2990_e', c2990_f1, leafS2_of_sq c2990_s2, leafS3_of_sq c2990_s3,
   c2990_iso, leafR8_of_sq c2990_nof2 c2990_nof3 c2990_nof4z⟩
theorem not_tile'_2990 (D : CongruentDissection 2990) : False :=
  not_tile_of_conditions' 2990 C'_2990 D

end Erdos634.Draft.AllN2

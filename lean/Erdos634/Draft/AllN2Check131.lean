/- AllN2Check131: N = 3014, 3017, 3018, 3019, 3021
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3014_sqf   : LeafSqf 3014   := by decide +kernel
private theorem c3014_range : LeafRange 3014  := by decide +kernel
private theorem c3014_ell   : LeafEll 3014    := by decide +kernel
private theorem c3014_nsq   : NSqChkSq 3014   := by decide +kernel
private theorem c3014_har   : HArithChkSq 3014 := by decide +kernel
private theorem c3014_r     : LeafR 3014      := by decide +kernel
private theorem c3014_e'    : LeafE' 3014     := by decide +kernel
private theorem c3014_f1    : LeafF1 3014     := Or.inl (by decide)
private theorem c3014_s2    : S2ChkSq 3014    := by decide +kernel
private theorem c3014_s3    : S3ChkSq 3014    := by decide +kernel
private theorem c3014_iso   : LeafIso 3014    := by decide +kernel
private theorem c3014_nof2  : NoF2ChkSq 3014  := by decide +kernel
private theorem c3014_nof3  : NoF3ChkSq 3014  := by decide +kernel
private theorem c3014_nof4z : NoF4zChkSq 3014 := by decide +kernel
theorem C'_3014 : C' 3014 :=
  ⟨c3014_sqf, c3014_range, c3014_ell, leafNSq_of_sq c3014_nsq, leafHAr_of_sq c3014_har,
   c3014_r, c3014_e', c3014_f1, leafS2_of_sq c3014_s2, leafS3_of_sq c3014_s3,
   c3014_iso, leafR8_of_sq c3014_nof2 c3014_nof3 c3014_nof4z⟩
theorem not_tile'_3014 (D : CongruentDissection 3014) : False :=
  not_tile_of_conditions' 3014 C'_3014 D

private theorem c3017_sqf   : LeafSqf 3017   := by decide +kernel
private theorem c3017_range : LeafRange 3017  := by decide +kernel
private theorem c3017_ell   : LeafEll 3017    := by decide +kernel
private theorem c3017_nsq   : NSqChkSq 3017   := by decide +kernel
private theorem c3017_har   : HArithChkSq 3017 := by decide +kernel
private theorem c3017_r     : LeafR 3017      := by decide +kernel
private theorem c3017_e'    : LeafE' 3017     := by decide +kernel
private theorem c3017_f1    : LeafF1 3017     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3017_s2    : S2ChkSq 3017    := by decide +kernel
private theorem c3017_s3    : S3ChkSq 3017    := by decide +kernel
private theorem c3017_iso   : LeafIso 3017    := by decide +kernel
private theorem c3017_nof2  : NoF2ChkSq 3017  := by decide +kernel
private theorem c3017_nof3  : NoF3ChkSq 3017  := by decide +kernel
private theorem c3017_nof4z : NoF4zChkSq 3017 := by decide +kernel
theorem C'_3017 : C' 3017 :=
  ⟨c3017_sqf, c3017_range, c3017_ell, leafNSq_of_sq c3017_nsq, leafHAr_of_sq c3017_har,
   c3017_r, c3017_e', c3017_f1, leafS2_of_sq c3017_s2, leafS3_of_sq c3017_s3,
   c3017_iso, leafR8_of_sq c3017_nof2 c3017_nof3 c3017_nof4z⟩
theorem not_tile'_3017 (D : CongruentDissection 3017) : False :=
  not_tile_of_conditions' 3017 C'_3017 D

private theorem c3018_sqf   : LeafSqf 3018   := by decide +kernel
private theorem c3018_range : LeafRange 3018  := by decide +kernel
private theorem c3018_ell   : LeafEll 3018    := by decide +kernel
private theorem c3018_nsq   : NSqChkSq 3018   := by decide +kernel
private theorem c3018_har   : HArithChkSq 3018 := by decide +kernel
private theorem c3018_r     : LeafR 3018      := by decide +kernel
private theorem c3018_e'    : LeafE' 3018     := by decide +kernel
private theorem c3018_f1    : LeafF1 3018     := Or.inl (by decide)
private theorem c3018_s2    : S2ChkSq 3018    := by decide +kernel
private theorem c3018_s3    : S3ChkSq 3018    := by decide +kernel
private theorem c3018_iso   : LeafIso 3018    := by decide +kernel
private theorem c3018_nof2  : NoF2ChkSq 3018  := by decide +kernel
private theorem c3018_nof3  : NoF3ChkSq 3018  := by decide +kernel
private theorem c3018_nof4z : NoF4zChkSq 3018 := by decide +kernel
theorem C'_3018 : C' 3018 :=
  ⟨c3018_sqf, c3018_range, c3018_ell, leafNSq_of_sq c3018_nsq, leafHAr_of_sq c3018_har,
   c3018_r, c3018_e', c3018_f1, leafS2_of_sq c3018_s2, leafS3_of_sq c3018_s3,
   c3018_iso, leafR8_of_sq c3018_nof2 c3018_nof3 c3018_nof4z⟩
theorem not_tile'_3018 (D : CongruentDissection 3018) : False :=
  not_tile_of_conditions' 3018 C'_3018 D

private theorem c3019_sqf   : LeafSqf 3019   := by decide +kernel
private theorem c3019_range : LeafRange 3019  := by decide +kernel
private theorem c3019_ell   : LeafEll 3019    := by decide +kernel
private theorem c3019_nsq   : NSqChkSq 3019   := by decide +kernel
private theorem c3019_har   : HArithChkSq 3019 := by decide +kernel
private theorem c3019_r     : LeafR 3019      := by decide +kernel
private theorem c3019_e'    : LeafE' 3019     := by decide +kernel
private theorem c3019_f1    : LeafF1 3019     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3019_s2    : S2ChkSq 3019    := by decide +kernel
private theorem c3019_s3    : S3ChkSq 3019    := by decide +kernel
private theorem c3019_iso   : LeafIso 3019    := by decide +kernel
private theorem c3019_nof2  : NoF2ChkSq 3019  := by decide +kernel
private theorem c3019_nof3  : NoF3ChkSq 3019  := by decide +kernel
private theorem c3019_nof4z : NoF4zChkSq 3019 := by decide +kernel
theorem C'_3019 : C' 3019 :=
  ⟨c3019_sqf, c3019_range, c3019_ell, leafNSq_of_sq c3019_nsq, leafHAr_of_sq c3019_har,
   c3019_r, c3019_e', c3019_f1, leafS2_of_sq c3019_s2, leafS3_of_sq c3019_s3,
   c3019_iso, leafR8_of_sq c3019_nof2 c3019_nof3 c3019_nof4z⟩
theorem not_tile'_3019 (D : CongruentDissection 3019) : False :=
  not_tile_of_conditions' 3019 C'_3019 D

private theorem c3021_sqf   : LeafSqf 3021   := by decide +kernel
private theorem c3021_range : LeafRange 3021  := by decide +kernel
private theorem c3021_ell   : LeafEll 3021    := by decide +kernel
private theorem c3021_nsq   : NSqChkSq 3021   := by decide +kernel
private theorem c3021_har   : HArithChkSq 3021 := by decide +kernel
private theorem c3021_r     : LeafR 3021      := by decide +kernel
private theorem c3021_e'    : LeafE' 3021     := by decide +kernel
private theorem c3021_f1    : LeafF1 3021     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3021_s2    : S2ChkSq 3021    := by decide +kernel
private theorem c3021_s3    : S3ChkSq 3021    := by decide +kernel
private theorem c3021_iso   : LeafIso 3021    := by decide +kernel
private theorem c3021_nof2  : NoF2ChkSq 3021  := by decide +kernel
private theorem c3021_nof3  : NoF3ChkSq 3021  := by decide +kernel
private theorem c3021_nof4z : NoF4zChkSq 3021 := by decide +kernel
theorem C'_3021 : C' 3021 :=
  ⟨c3021_sqf, c3021_range, c3021_ell, leafNSq_of_sq c3021_nsq, leafHAr_of_sq c3021_har,
   c3021_r, c3021_e', c3021_f1, leafS2_of_sq c3021_s2, leafS3_of_sq c3021_s3,
   c3021_iso, leafR8_of_sq c3021_nof2 c3021_nof3 c3021_nof4z⟩
theorem not_tile'_3021 (D : CongruentDissection 3021) : False :=
  not_tile_of_conditions' 3021 C'_3021 D

end Erdos634.Draft.AllN2

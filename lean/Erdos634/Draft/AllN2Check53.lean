/- AllN2Check53: N = 2014, 2015, 2019, 2021, 2022
   Squarefree exclusions via C' with F1 proved through F1ChkSq. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry
private theorem c2014_sqf   : LeafSqf 2014   := by decide +kernel
private theorem c2014_range : LeafRange 2014  := by decide +kernel
private theorem c2014_ell   : LeafEll 2014    := by decide +kernel
private theorem c2014_nsq   : NSqChkSq 2014   := by decide +kernel
private theorem c2014_har   : HArithChkSq 2014 := by decide +kernel
private theorem c2014_r     : LeafR 2014      := by decide +kernel
private theorem c2014_e'    : LeafE' 2014     := by decide +kernel
private theorem c2014_f1    : LeafF1 2014     := Or.inl (by decide)
private theorem c2014_s2    : S2ChkSq 2014    := by decide +kernel
private theorem c2014_s3    : S3ChkSq 2014    := by decide +kernel
private theorem c2014_iso   : LeafIso 2014    := by decide +kernel
private theorem c2014_nof2  : NoF2ChkSq 2014  := by decide +kernel
private theorem c2014_nof3  : NoF3ChkSq 2014  := by decide +kernel
private theorem c2014_nof4z : NoF4zChkSq 2014 := by decide +kernel
theorem C'_2014 : C' 2014 :=
  ⟨c2014_sqf, c2014_range, c2014_ell, leafNSq_of_sq c2014_nsq, leafHAr_of_sq c2014_har,
   c2014_r, c2014_e', c2014_f1, leafS2_of_sq c2014_s2, leafS3_of_sq c2014_s3,
   c2014_iso, leafR8_of_sq c2014_nof2 c2014_nof3 c2014_nof4z⟩
theorem not_tile'_2014 (D : CongruentDissection 2014) : False :=
  not_tile_of_conditions' 2014 C'_2014 D

private theorem c2015_sqf   : LeafSqf 2015   := by decide +kernel
private theorem c2015_range : LeafRange 2015  := by decide +kernel
private theorem c2015_ell   : LeafEll 2015    := by decide +kernel
private theorem c2015_nsq   : NSqChkSq 2015   := by decide +kernel
private theorem c2015_har   : HArithChkSq 2015 := by decide +kernel
private theorem c2015_r     : LeafR 2015      := by decide +kernel
private theorem c2015_e'    : LeafE' 2015     := by decide +kernel
private theorem c2015_f1    : LeafF1 2015     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2015_s2    : S2ChkSq 2015    := by decide +kernel
private theorem c2015_s3    : S3ChkSq 2015    := by decide +kernel
private theorem c2015_iso   : LeafIso 2015    := by decide +kernel
private theorem c2015_nof2  : NoF2ChkSq 2015  := by decide +kernel
private theorem c2015_nof3  : NoF3ChkSq 2015  := by decide +kernel
private theorem c2015_nof4z : NoF4zChkSq 2015 := by decide +kernel
theorem C'_2015 : C' 2015 :=
  ⟨c2015_sqf, c2015_range, c2015_ell, leafNSq_of_sq c2015_nsq, leafHAr_of_sq c2015_har,
   c2015_r, c2015_e', c2015_f1, leafS2_of_sq c2015_s2, leafS3_of_sq c2015_s3,
   c2015_iso, leafR8_of_sq c2015_nof2 c2015_nof3 c2015_nof4z⟩
theorem not_tile'_2015 (D : CongruentDissection 2015) : False :=
  not_tile_of_conditions' 2015 C'_2015 D

private theorem c2019_sqf   : LeafSqf 2019   := by decide +kernel
private theorem c2019_range : LeafRange 2019  := by decide +kernel
private theorem c2019_ell   : LeafEll 2019    := by decide +kernel
private theorem c2019_nsq   : NSqChkSq 2019   := by decide +kernel
private theorem c2019_har   : HArithChkSq 2019 := by decide +kernel
private theorem c2019_r     : LeafR 2019      := by decide +kernel
private theorem c2019_e'    : LeafE' 2019     := by decide +kernel
private theorem c2019_f1    : LeafF1 2019     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2019_s2    : S2ChkSq 2019    := by decide +kernel
private theorem c2019_s3    : S3ChkSq 2019    := by decide +kernel
private theorem c2019_iso   : LeafIso 2019    := by decide +kernel
private theorem c2019_nof2  : NoF2ChkSq 2019  := by decide +kernel
private theorem c2019_nof3  : NoF3ChkSq 2019  := by decide +kernel
private theorem c2019_nof4z : NoF4zChkSq 2019 := by decide +kernel
theorem C'_2019 : C' 2019 :=
  ⟨c2019_sqf, c2019_range, c2019_ell, leafNSq_of_sq c2019_nsq, leafHAr_of_sq c2019_har,
   c2019_r, c2019_e', c2019_f1, leafS2_of_sq c2019_s2, leafS3_of_sq c2019_s3,
   c2019_iso, leafR8_of_sq c2019_nof2 c2019_nof3 c2019_nof4z⟩
theorem not_tile'_2019 (D : CongruentDissection 2019) : False :=
  not_tile_of_conditions' 2019 C'_2019 D

private theorem c2021_sqf   : LeafSqf 2021   := by decide +kernel
private theorem c2021_range : LeafRange 2021  := by decide +kernel
private theorem c2021_ell   : LeafEll 2021    := by decide +kernel
private theorem c2021_nsq   : NSqChkSq 2021   := by decide +kernel
private theorem c2021_har   : HArithChkSq 2021 := by decide +kernel
private theorem c2021_r     : LeafR 2021      := by decide +kernel
private theorem c2021_e'    : LeafE' 2021     := by decide +kernel
private theorem c2021_f1    : LeafF1 2021     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2021_s2    : S2ChkSq 2021    := by decide +kernel
private theorem c2021_s3    : S3ChkSq 2021    := by decide +kernel
private theorem c2021_iso   : LeafIso 2021    := by decide +kernel
private theorem c2021_nof2  : NoF2ChkSq 2021  := by decide +kernel
private theorem c2021_nof3  : NoF3ChkSq 2021  := by decide +kernel
private theorem c2021_nof4z : NoF4zChkSq 2021 := by decide +kernel
theorem C'_2021 : C' 2021 :=
  ⟨c2021_sqf, c2021_range, c2021_ell, leafNSq_of_sq c2021_nsq, leafHAr_of_sq c2021_har,
   c2021_r, c2021_e', c2021_f1, leafS2_of_sq c2021_s2, leafS3_of_sq c2021_s3,
   c2021_iso, leafR8_of_sq c2021_nof2 c2021_nof3 c2021_nof4z⟩
theorem not_tile'_2021 (D : CongruentDissection 2021) : False :=
  not_tile_of_conditions' 2021 C'_2021 D

private theorem c2022_sqf   : LeafSqf 2022   := by decide +kernel
private theorem c2022_range : LeafRange 2022  := by decide +kernel
private theorem c2022_ell   : LeafEll 2022    := by decide +kernel
private theorem c2022_nsq   : NSqChkSq 2022   := by decide +kernel
private theorem c2022_har   : HArithChkSq 2022 := by decide +kernel
private theorem c2022_r     : LeafR 2022      := by decide +kernel
private theorem c2022_e'    : LeafE' 2022     := by decide +kernel
private theorem c2022_f1    : LeafF1 2022     := Or.inl (by decide)
private theorem c2022_s2    : S2ChkSq 2022    := by decide +kernel
private theorem c2022_s3    : S3ChkSq 2022    := by decide +kernel
private theorem c2022_iso   : LeafIso 2022    := by decide +kernel
private theorem c2022_nof2  : NoF2ChkSq 2022  := by decide +kernel
private theorem c2022_nof3  : NoF3ChkSq 2022  := by decide +kernel
private theorem c2022_nof4z : NoF4zChkSq 2022 := by decide +kernel
theorem C'_2022 : C' 2022 :=
  ⟨c2022_sqf, c2022_range, c2022_ell, leafNSq_of_sq c2022_nsq, leafHAr_of_sq c2022_har,
   c2022_r, c2022_e', c2022_f1, leafS2_of_sq c2022_s2, leafS3_of_sq c2022_s3,
   c2022_iso, leafR8_of_sq c2022_nof2 c2022_nof3 c2022_nof4z⟩
theorem not_tile'_2022 (D : CongruentDissection 2022) : False :=
  not_tile_of_conditions' 2022 C'_2022 D

end Erdos634.Draft.AllN2

/- AllN2Check162: N = 3403, 3406, 3407, 3409, 3410
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3403_sqf   : LeafSqf 3403   := by decide +kernel
private theorem c3403_range : LeafRange 3403  := by decide +kernel
private theorem c3403_ell   : LeafEll 3403    := by decide +kernel
private theorem c3403_nsq   : NSqChkSq 3403   := by decide +kernel
private theorem c3403_har   : HArithChkSq 3403 := by decide +kernel
private theorem c3403_r     : LeafR 3403      := by decide +kernel
private theorem c3403_e'    : LeafE' 3403     := by decide +kernel
private theorem c3403_f1    : LeafF1 3403     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3403_s2    : S2ChkSq 3403    := by decide +kernel
private theorem c3403_s3    : S3ChkSq 3403    := by decide +kernel
private theorem c3403_iso   : LeafIso 3403    := by decide +kernel
private theorem c3403_nof2  : NoF2ChkSq 3403  := by decide +kernel
private theorem c3403_nof3  : NoF3ChkSq 3403  := by decide +kernel
private theorem c3403_nof4z : NoF4zChkSq 3403 := by decide +kernel
theorem C'_3403 : C' 3403 :=
  ⟨c3403_sqf, c3403_range, c3403_ell, leafNSq_of_sq c3403_nsq, leafHAr_of_sq c3403_har,
   c3403_r, c3403_e', c3403_f1, leafS2_of_sq c3403_s2, leafS3_of_sq c3403_s3,
   c3403_iso, leafR8_of_sq c3403_nof2 c3403_nof3 c3403_nof4z⟩
theorem not_tile'_3403 (D : CongruentDissection 3403) : False :=
  not_tile_of_conditions' 3403 C'_3403 D

private theorem c3406_sqf   : LeafSqf 3406   := by decide +kernel
private theorem c3406_range : LeafRange 3406  := by decide +kernel
private theorem c3406_ell   : LeafEll 3406    := by decide +kernel
private theorem c3406_nsq   : NSqChkSq 3406   := by decide +kernel
private theorem c3406_har   : HArithChkSq 3406 := by decide +kernel
private theorem c3406_r     : LeafR 3406      := by decide +kernel
private theorem c3406_e'    : LeafE' 3406     := by decide +kernel
private theorem c3406_f1    : LeafF1 3406     := Or.inl (by decide)
private theorem c3406_s2    : S2ChkSq 3406    := by decide +kernel
private theorem c3406_s3    : S3ChkSq 3406    := by decide +kernel
private theorem c3406_iso   : LeafIso 3406    := by decide +kernel
private theorem c3406_nof2  : NoF2ChkSq 3406  := by decide +kernel
private theorem c3406_nof3  : NoF3ChkSq 3406  := by decide +kernel
private theorem c3406_nof4z : NoF4zChkSq 3406 := by decide +kernel
theorem C'_3406 : C' 3406 :=
  ⟨c3406_sqf, c3406_range, c3406_ell, leafNSq_of_sq c3406_nsq, leafHAr_of_sq c3406_har,
   c3406_r, c3406_e', c3406_f1, leafS2_of_sq c3406_s2, leafS3_of_sq c3406_s3,
   c3406_iso, leafR8_of_sq c3406_nof2 c3406_nof3 c3406_nof4z⟩
theorem not_tile'_3406 (D : CongruentDissection 3406) : False :=
  not_tile_of_conditions' 3406 C'_3406 D

private theorem c3407_sqf   : LeafSqf 3407   := by decide +kernel
private theorem c3407_range : LeafRange 3407  := by decide +kernel
private theorem c3407_ell   : LeafEll 3407    := by decide +kernel
private theorem c3407_nsq   : NSqChkSq 3407   := by decide +kernel
private theorem c3407_har   : HArithChkSq 3407 := by decide +kernel
private theorem c3407_r     : LeafR 3407      := by decide +kernel
private theorem c3407_e'    : LeafE' 3407     := by decide +kernel
private theorem c3407_f1    : LeafF1 3407     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3407_s2    : S2ChkSq 3407    := by decide +kernel
private theorem c3407_s3    : S3ChkSq 3407    := by decide +kernel
private theorem c3407_iso   : LeafIso 3407    := by decide +kernel
private theorem c3407_nof2  : NoF2ChkSq 3407  := by decide +kernel
private theorem c3407_nof3  : NoF3ChkSq 3407  := by decide +kernel
private theorem c3407_nof4z : NoF4zChkSq 3407 := by decide +kernel
theorem C'_3407 : C' 3407 :=
  ⟨c3407_sqf, c3407_range, c3407_ell, leafNSq_of_sq c3407_nsq, leafHAr_of_sq c3407_har,
   c3407_r, c3407_e', c3407_f1, leafS2_of_sq c3407_s2, leafS3_of_sq c3407_s3,
   c3407_iso, leafR8_of_sq c3407_nof2 c3407_nof3 c3407_nof4z⟩
theorem not_tile'_3407 (D : CongruentDissection 3407) : False :=
  not_tile_of_conditions' 3407 C'_3407 D

private theorem c3409_sqf   : LeafSqf 3409   := by decide +kernel
private theorem c3409_range : LeafRange 3409  := by decide +kernel
private theorem c3409_ell   : LeafEll 3409    := by decide +kernel
private theorem c3409_nsq   : NSqChkSq 3409   := by decide +kernel
private theorem c3409_har   : HArithChkSq 3409 := by decide +kernel
private theorem c3409_r     : LeafR 3409      := by decide +kernel
private theorem c3409_e'    : LeafE' 3409     := by decide +kernel
private theorem c3409_f1    : LeafF1 3409     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3409_s2    : S2ChkSq 3409    := by decide +kernel
private theorem c3409_s3    : S3ChkSq 3409    := by decide +kernel
private theorem c3409_iso   : LeafIso 3409    := by decide +kernel
private theorem c3409_nof2  : NoF2ChkSq 3409  := by decide +kernel
private theorem c3409_nof3  : NoF3ChkSq 3409  := by decide +kernel
private theorem c3409_nof4z : NoF4zChkSq 3409 := by decide +kernel
theorem C'_3409 : C' 3409 :=
  ⟨c3409_sqf, c3409_range, c3409_ell, leafNSq_of_sq c3409_nsq, leafHAr_of_sq c3409_har,
   c3409_r, c3409_e', c3409_f1, leafS2_of_sq c3409_s2, leafS3_of_sq c3409_s3,
   c3409_iso, leafR8_of_sq c3409_nof2 c3409_nof3 c3409_nof4z⟩
theorem not_tile'_3409 (D : CongruentDissection 3409) : False :=
  not_tile_of_conditions' 3409 C'_3409 D

private theorem c3410_sqf   : LeafSqf 3410   := by decide +kernel
private theorem c3410_range : LeafRange 3410  := by decide +kernel
private theorem c3410_ell   : LeafEll 3410    := by decide +kernel
private theorem c3410_nsq   : NSqChkSq 3410   := by decide +kernel
private theorem c3410_har   : HArithChkSq 3410 := by decide +kernel
private theorem c3410_r     : LeafR 3410      := by decide +kernel
private theorem c3410_e'    : LeafE' 3410     := by decide +kernel
private theorem c3410_f1    : LeafF1 3410     := Or.inl (by decide)
private theorem c3410_s2    : S2ChkSq 3410    := by decide +kernel
private theorem c3410_s3    : S3ChkSq 3410    := by decide +kernel
private theorem c3410_iso   : LeafIso 3410    := by decide +kernel
private theorem c3410_nof2  : NoF2ChkSq 3410  := by decide +kernel
private theorem c3410_nof3  : NoF3ChkSq 3410  := by decide +kernel
private theorem c3410_nof4z : NoF4zChkSq 3410 := by decide +kernel
theorem C'_3410 : C' 3410 :=
  ⟨c3410_sqf, c3410_range, c3410_ell, leafNSq_of_sq c3410_nsq, leafHAr_of_sq c3410_har,
   c3410_r, c3410_e', c3410_f1, leafS2_of_sq c3410_s2, leafS3_of_sq c3410_s3,
   c3410_iso, leafR8_of_sq c3410_nof2 c3410_nof3 c3410_nof4z⟩
theorem not_tile'_3410 (D : CongruentDissection 3410) : False :=
  not_tile_of_conditions' 3410 C'_3410 D

end Erdos634.Draft.AllN2

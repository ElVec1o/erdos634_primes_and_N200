/- AllN2Check84: N = 2419, 2422, 2423, 2427, 2429
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c2419_sqf   : LeafSqf 2419   := by decide +kernel
private theorem c2419_range : LeafRange 2419  := by decide +kernel
private theorem c2419_ell   : LeafEll 2419    := by decide +kernel
private theorem c2419_nsq   : NSqChkSq 2419   := by decide +kernel
private theorem c2419_har   : HArithChkSq 2419 := by decide +kernel
private theorem c2419_r     : LeafR 2419      := by decide +kernel
private theorem c2419_e'    : LeafE' 2419     := by decide +kernel
private theorem c2419_f1    : LeafF1 2419     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2419_s2    : S2ChkSq 2419    := by decide +kernel
private theorem c2419_s3    : S3ChkSq 2419    := by decide +kernel
private theorem c2419_iso   : LeafIso 2419    := by decide +kernel
private theorem c2419_nof2  : NoF2ChkSq 2419  := by decide +kernel
private theorem c2419_nof3  : NoF3ChkSq 2419  := by decide +kernel
private theorem c2419_nof4z : NoF4zChkSq 2419 := by decide +kernel
theorem C'_2419 : C' 2419 :=
  ⟨c2419_sqf, c2419_range, c2419_ell, leafNSq_of_sq c2419_nsq, leafHAr_of_sq c2419_har,
   c2419_r, c2419_e', c2419_f1, leafS2_of_sq c2419_s2, leafS3_of_sq c2419_s3,
   c2419_iso, leafR8_of_sq c2419_nof2 c2419_nof3 c2419_nof4z⟩
theorem not_tile'_2419 (D : CongruentDissection 2419) : False :=
  not_tile_of_conditions' 2419 C'_2419 D

private theorem c2422_sqf   : LeafSqf 2422   := by decide +kernel
private theorem c2422_range : LeafRange 2422  := by decide +kernel
private theorem c2422_ell   : LeafEll 2422    := by decide +kernel
private theorem c2422_nsq   : NSqChkSq 2422   := by decide +kernel
private theorem c2422_har   : HArithChkSq 2422 := by decide +kernel
private theorem c2422_r     : LeafR 2422      := by decide +kernel
private theorem c2422_e'    : LeafE' 2422     := by decide +kernel
private theorem c2422_f1    : LeafF1 2422     := Or.inl (by decide)
private theorem c2422_s2    : S2ChkSq 2422    := by decide +kernel
private theorem c2422_s3    : S3ChkSq 2422    := by decide +kernel
private theorem c2422_iso   : LeafIso 2422    := by decide +kernel
private theorem c2422_nof2  : NoF2ChkSq 2422  := by decide +kernel
private theorem c2422_nof3  : NoF3ChkSq 2422  := by decide +kernel
private theorem c2422_nof4z : NoF4zChkSq 2422 := by decide +kernel
theorem C'_2422 : C' 2422 :=
  ⟨c2422_sqf, c2422_range, c2422_ell, leafNSq_of_sq c2422_nsq, leafHAr_of_sq c2422_har,
   c2422_r, c2422_e', c2422_f1, leafS2_of_sq c2422_s2, leafS3_of_sq c2422_s3,
   c2422_iso, leafR8_of_sq c2422_nof2 c2422_nof3 c2422_nof4z⟩
theorem not_tile'_2422 (D : CongruentDissection 2422) : False :=
  not_tile_of_conditions' 2422 C'_2422 D

private theorem c2423_sqf   : LeafSqf 2423   := by decide +kernel
private theorem c2423_range : LeafRange 2423  := by decide +kernel
private theorem c2423_ell   : LeafEll 2423    := by decide +kernel
private theorem c2423_nsq   : NSqChkSq 2423   := by decide +kernel
private theorem c2423_har   : HArithChkSq 2423 := by decide +kernel
private theorem c2423_r     : LeafR 2423      := by decide +kernel
private theorem c2423_e'    : LeafE' 2423     := by decide +kernel
private theorem c2423_f1    : LeafF1 2423     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2423_s2    : S2ChkSq 2423    := by decide +kernel
private theorem c2423_s3    : S3ChkSq 2423    := by decide +kernel
private theorem c2423_iso   : LeafIso 2423    := by decide +kernel
private theorem c2423_nof2  : NoF2ChkSq 2423  := by decide +kernel
private theorem c2423_nof3  : NoF3ChkSq 2423  := by decide +kernel
private theorem c2423_nof4z : NoF4zChkSq 2423 := by decide +kernel
theorem C'_2423 : C' 2423 :=
  ⟨c2423_sqf, c2423_range, c2423_ell, leafNSq_of_sq c2423_nsq, leafHAr_of_sq c2423_har,
   c2423_r, c2423_e', c2423_f1, leafS2_of_sq c2423_s2, leafS3_of_sq c2423_s3,
   c2423_iso, leafR8_of_sq c2423_nof2 c2423_nof3 c2423_nof4z⟩
theorem not_tile'_2423 (D : CongruentDissection 2423) : False :=
  not_tile_of_conditions' 2423 C'_2423 D

private theorem c2427_sqf   : LeafSqf 2427   := by decide +kernel
private theorem c2427_range : LeafRange 2427  := by decide +kernel
private theorem c2427_ell   : LeafEll 2427    := by decide +kernel
private theorem c2427_nsq   : NSqChkSq 2427   := by decide +kernel
private theorem c2427_har   : HArithChkSq 2427 := by decide +kernel
private theorem c2427_r     : LeafR 2427      := by decide +kernel
private theorem c2427_e'    : LeafE' 2427     := by decide +kernel
private theorem c2427_f1    : LeafF1 2427     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2427_s2    : S2ChkSq 2427    := by decide +kernel
private theorem c2427_s3    : S3ChkSq 2427    := by decide +kernel
private theorem c2427_iso   : LeafIso 2427    := by decide +kernel
private theorem c2427_nof2  : NoF2ChkSq 2427  := by decide +kernel
private theorem c2427_nof3  : NoF3ChkSq 2427  := by decide +kernel
private theorem c2427_nof4z : NoF4zChkSq 2427 := by decide +kernel
theorem C'_2427 : C' 2427 :=
  ⟨c2427_sqf, c2427_range, c2427_ell, leafNSq_of_sq c2427_nsq, leafHAr_of_sq c2427_har,
   c2427_r, c2427_e', c2427_f1, leafS2_of_sq c2427_s2, leafS3_of_sq c2427_s3,
   c2427_iso, leafR8_of_sq c2427_nof2 c2427_nof3 c2427_nof4z⟩
theorem not_tile'_2427 (D : CongruentDissection 2427) : False :=
  not_tile_of_conditions' 2427 C'_2427 D

private theorem c2429_sqf   : LeafSqf 2429   := by decide +kernel
private theorem c2429_range : LeafRange 2429  := by decide +kernel
private theorem c2429_ell   : LeafEll 2429    := by decide +kernel
private theorem c2429_nsq   : NSqChkSq 2429   := by decide +kernel
private theorem c2429_har   : HArithChkSq 2429 := by decide +kernel
private theorem c2429_r     : LeafR 2429      := by decide +kernel
private theorem c2429_e'    : LeafE' 2429     := by decide +kernel
private theorem c2429_f1    : LeafF1 2429     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c2429_s2    : S2ChkSq 2429    := by decide +kernel
private theorem c2429_s3    : S3ChkSq 2429    := by decide +kernel
private theorem c2429_iso   : LeafIso 2429    := by decide +kernel
private theorem c2429_nof2  : NoF2ChkSq 2429  := by decide +kernel
private theorem c2429_nof3  : NoF3ChkSq 2429  := by decide +kernel
private theorem c2429_nof4z : NoF4zChkSq 2429 := by decide +kernel
theorem C'_2429 : C' 2429 :=
  ⟨c2429_sqf, c2429_range, c2429_ell, leafNSq_of_sq c2429_nsq, leafHAr_of_sq c2429_har,
   c2429_r, c2429_e', c2429_f1, leafS2_of_sq c2429_s2, leafS3_of_sq c2429_s3,
   c2429_iso, leafR8_of_sq c2429_nof2 c2429_nof3 c2429_nof4z⟩
theorem not_tile'_2429 (D : CongruentDissection 2429) : False :=
  not_tile_of_conditions' 2429 C'_2429 D

end Erdos634.Draft.AllN2

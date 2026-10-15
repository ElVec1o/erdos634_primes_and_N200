/- AllN2Check250: N = 4541, 4542, 4543, 4547, 4555
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4541_sqf   : LeafSqf 4541   := by decide +kernel
private theorem c4541_range : LeafRange 4541  := by decide +kernel
private theorem c4541_ell   : LeafEll 4541    := by decide +kernel
private theorem c4541_nsq   : NSqChkSq 4541   := by decide +kernel
private theorem c4541_har   : HArithChkSq 4541 := by decide +kernel
private theorem c4541_r     : LeafR 4541      := by decide +kernel
private theorem c4541_e'    : LeafE' 4541     := by decide +kernel
private theorem c4541_f1    : LeafF1 4541     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4541_s2    : S2ChkSq 4541    := by decide +kernel
private theorem c4541_s3    : S3ChkSq 4541    := by decide +kernel
private theorem c4541_iso   : LeafIso 4541    := by decide +kernel
private theorem c4541_nof2  : NoF2ChkSq 4541  := by decide +kernel
private theorem c4541_nof3  : NoF3ChkSq 4541  := by decide +kernel
private theorem c4541_nof4z : NoF4zChkSq 4541 := by decide +kernel
theorem C'_4541 : C' 4541 :=
  ⟨c4541_sqf, c4541_range, c4541_ell, leafNSq_of_sq c4541_nsq, leafHAr_of_sq c4541_har,
   c4541_r, c4541_e', c4541_f1, leafS2_of_sq c4541_s2, leafS3_of_sq c4541_s3,
   c4541_iso, leafR8_of_sq c4541_nof2 c4541_nof3 c4541_nof4z⟩
theorem not_tile'_4541 (D : CongruentDissection 4541) : False :=
  not_tile_of_conditions' 4541 C'_4541 D

private theorem c4542_sqf   : LeafSqf 4542   := by decide +kernel
private theorem c4542_range : LeafRange 4542  := by decide +kernel
private theorem c4542_ell   : LeafEll 4542    := by decide +kernel
private theorem c4542_nsq   : NSqChkSq 4542   := by decide +kernel
private theorem c4542_har   : HArithChkSq 4542 := by decide +kernel
private theorem c4542_r     : LeafR 4542      := by decide +kernel
private theorem c4542_e'    : LeafE' 4542     := by decide +kernel
private theorem c4542_f1    : LeafF1 4542     := Or.inl (by decide)
private theorem c4542_s2    : S2ChkSq 4542    := by decide +kernel
private theorem c4542_s3    : S3ChkSq 4542    := by decide +kernel
private theorem c4542_iso   : LeafIso 4542    := by decide +kernel
private theorem c4542_nof2  : NoF2ChkSq 4542  := by decide +kernel
private theorem c4542_nof3  : NoF3ChkSq 4542  := by decide +kernel
private theorem c4542_nof4z : NoF4zChkSq 4542 := by decide +kernel
theorem C'_4542 : C' 4542 :=
  ⟨c4542_sqf, c4542_range, c4542_ell, leafNSq_of_sq c4542_nsq, leafHAr_of_sq c4542_har,
   c4542_r, c4542_e', c4542_f1, leafS2_of_sq c4542_s2, leafS3_of_sq c4542_s3,
   c4542_iso, leafR8_of_sq c4542_nof2 c4542_nof3 c4542_nof4z⟩
theorem not_tile'_4542 (D : CongruentDissection 4542) : False :=
  not_tile_of_conditions' 4542 C'_4542 D

private theorem c4543_sqf   : LeafSqf 4543   := by decide +kernel
private theorem c4543_range : LeafRange 4543  := by decide +kernel
private theorem c4543_ell   : LeafEll 4543    := by decide +kernel
private theorem c4543_nsq   : NSqChkSq 4543   := by decide +kernel
private theorem c4543_har   : HArithChkSq 4543 := by decide +kernel
private theorem c4543_r     : LeafR 4543      := by decide +kernel
private theorem c4543_e'    : LeafE' 4543     := by decide +kernel
private theorem c4543_f1    : LeafF1 4543     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4543_s2    : S2ChkSq 4543    := by decide +kernel
private theorem c4543_s3    : S3ChkSq 4543    := by decide +kernel
private theorem c4543_iso   : LeafIso 4543    := by decide +kernel
private theorem c4543_nof2  : NoF2ChkSq 4543  := by decide +kernel
private theorem c4543_nof3  : NoF3ChkSq 4543  := by decide +kernel
private theorem c4543_nof4z : NoF4zChkSq 4543 := by decide +kernel
theorem C'_4543 : C' 4543 :=
  ⟨c4543_sqf, c4543_range, c4543_ell, leafNSq_of_sq c4543_nsq, leafHAr_of_sq c4543_har,
   c4543_r, c4543_e', c4543_f1, leafS2_of_sq c4543_s2, leafS3_of_sq c4543_s3,
   c4543_iso, leafR8_of_sq c4543_nof2 c4543_nof3 c4543_nof4z⟩
theorem not_tile'_4543 (D : CongruentDissection 4543) : False :=
  not_tile_of_conditions' 4543 C'_4543 D

private theorem c4547_sqf   : LeafSqf 4547   := by decide +kernel
private theorem c4547_range : LeafRange 4547  := by decide +kernel
private theorem c4547_ell   : LeafEll 4547    := by decide +kernel
private theorem c4547_nsq   : NSqChkSq 4547   := by decide +kernel
private theorem c4547_har   : HArithChkSq 4547 := by decide +kernel
private theorem c4547_r     : LeafR 4547      := by decide +kernel
private theorem c4547_e'    : LeafE' 4547     := by decide +kernel
private theorem c4547_f1    : LeafF1 4547     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4547_s2    : S2ChkSq 4547    := by decide +kernel
private theorem c4547_s3    : S3ChkSq 4547    := by decide +kernel
private theorem c4547_iso   : LeafIso 4547    := by decide +kernel
private theorem c4547_nof2  : NoF2ChkSq 4547  := by decide +kernel
private theorem c4547_nof3  : NoF3ChkSq 4547  := by decide +kernel
private theorem c4547_nof4z : NoF4zChkSq 4547 := by decide +kernel
theorem C'_4547 : C' 4547 :=
  ⟨c4547_sqf, c4547_range, c4547_ell, leafNSq_of_sq c4547_nsq, leafHAr_of_sq c4547_har,
   c4547_r, c4547_e', c4547_f1, leafS2_of_sq c4547_s2, leafS3_of_sq c4547_s3,
   c4547_iso, leafR8_of_sq c4547_nof2 c4547_nof3 c4547_nof4z⟩
theorem not_tile'_4547 (D : CongruentDissection 4547) : False :=
  not_tile_of_conditions' 4547 C'_4547 D

private theorem c4555_sqf   : LeafSqf 4555   := by decide +kernel
private theorem c4555_range : LeafRange 4555  := by decide +kernel
private theorem c4555_ell   : LeafEll 4555    := by decide +kernel
private theorem c4555_nsq   : NSqChkSq 4555   := by decide +kernel
private theorem c4555_har   : HArithChkSq 4555 := by decide +kernel
private theorem c4555_r     : LeafR 4555      := by decide +kernel
private theorem c4555_e'    : LeafE' 4555     := by decide +kernel
private theorem c4555_f1    : LeafF1 4555     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4555_s2    : S2ChkSq 4555    := by decide +kernel
private theorem c4555_s3    : S3ChkSq 4555    := by decide +kernel
private theorem c4555_iso   : LeafIso 4555    := by decide +kernel
private theorem c4555_nof2  : NoF2ChkSq 4555  := by decide +kernel
private theorem c4555_nof3  : NoF3ChkSq 4555  := by decide +kernel
private theorem c4555_nof4z : NoF4zChkSq 4555 := by decide +kernel
theorem C'_4555 : C' 4555 :=
  ⟨c4555_sqf, c4555_range, c4555_ell, leafNSq_of_sq c4555_nsq, leafHAr_of_sq c4555_har,
   c4555_r, c4555_e', c4555_f1, leafS2_of_sq c4555_s2, leafS3_of_sq c4555_s3,
   c4555_iso, leafR8_of_sq c4555_nof2 c4555_nof3 c4555_nof4z⟩
theorem not_tile'_4555 (D : CongruentDissection 4555) : False :=
  not_tile_of_conditions' 4555 C'_4555 D

end Erdos634.Draft.AllN2

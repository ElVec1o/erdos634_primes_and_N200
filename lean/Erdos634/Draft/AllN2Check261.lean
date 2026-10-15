/- AllN2Check261: N = 4681, 4686, 4687, 4690, 4691
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4681_sqf   : LeafSqf 4681   := by decide +kernel
private theorem c4681_range : LeafRange 4681  := by decide +kernel
private theorem c4681_ell   : LeafEll 4681    := by decide +kernel
private theorem c4681_nsq   : NSqChkSq 4681   := by decide +kernel
private theorem c4681_har   : HArithChkSq 4681 := by decide +kernel
private theorem c4681_r     : LeafR 4681      := by decide +kernel
private theorem c4681_e'    : LeafE' 4681     := by decide +kernel
private theorem c4681_f1    : LeafF1 4681     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4681_s2    : S2ChkSq 4681    := by decide +kernel
private theorem c4681_s3    : S3ChkSq 4681    := by decide +kernel
private theorem c4681_iso   : LeafIso 4681    := by decide +kernel
private theorem c4681_nof2  : NoF2ChkSq 4681  := by decide +kernel
private theorem c4681_nof3  : NoF3ChkSq 4681  := by decide +kernel
private theorem c4681_nof4z : NoF4zChkSq 4681 := by decide +kernel
theorem C'_4681 : C' 4681 :=
  ⟨c4681_sqf, c4681_range, c4681_ell, leafNSq_of_sq c4681_nsq, leafHAr_of_sq c4681_har,
   c4681_r, c4681_e', c4681_f1, leafS2_of_sq c4681_s2, leafS3_of_sq c4681_s3,
   c4681_iso, leafR8_of_sq c4681_nof2 c4681_nof3 c4681_nof4z⟩
theorem not_tile'_4681 (D : CongruentDissection 4681) : False :=
  not_tile_of_conditions' 4681 C'_4681 D

private theorem c4686_sqf   : LeafSqf 4686   := by decide +kernel
private theorem c4686_range : LeafRange 4686  := by decide +kernel
private theorem c4686_ell   : LeafEll 4686    := by decide +kernel
private theorem c4686_nsq   : NSqChkSq 4686   := by decide +kernel
private theorem c4686_har   : HArithChkSq 4686 := by decide +kernel
private theorem c4686_r     : LeafR 4686      := by decide +kernel
private theorem c4686_e'    : LeafE' 4686     := by decide +kernel
private theorem c4686_f1    : LeafF1 4686     := Or.inl (by decide)
private theorem c4686_s2    : S2ChkSq 4686    := by decide +kernel
private theorem c4686_s3    : S3ChkSq 4686    := by decide +kernel
private theorem c4686_iso   : LeafIso 4686    := by decide +kernel
private theorem c4686_nof2  : NoF2ChkSq 4686  := by decide +kernel
private theorem c4686_nof3  : NoF3ChkSq 4686  := by decide +kernel
private theorem c4686_nof4z : NoF4zChkSq 4686 := by decide +kernel
theorem C'_4686 : C' 4686 :=
  ⟨c4686_sqf, c4686_range, c4686_ell, leafNSq_of_sq c4686_nsq, leafHAr_of_sq c4686_har,
   c4686_r, c4686_e', c4686_f1, leafS2_of_sq c4686_s2, leafS3_of_sq c4686_s3,
   c4686_iso, leafR8_of_sq c4686_nof2 c4686_nof3 c4686_nof4z⟩
theorem not_tile'_4686 (D : CongruentDissection 4686) : False :=
  not_tile_of_conditions' 4686 C'_4686 D

private theorem c4687_sqf   : LeafSqf 4687   := by decide +kernel
private theorem c4687_range : LeafRange 4687  := by decide +kernel
private theorem c4687_ell   : LeafEll 4687    := by decide +kernel
private theorem c4687_nsq   : NSqChkSq 4687   := by decide +kernel
private theorem c4687_har   : HArithChkSq 4687 := by decide +kernel
private theorem c4687_r     : LeafR 4687      := by decide +kernel
private theorem c4687_e'    : LeafE' 4687     := by decide +kernel
private theorem c4687_f1    : LeafF1 4687     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4687_s2    : S2ChkSq 4687    := by decide +kernel
private theorem c4687_s3    : S3ChkSq 4687    := by decide +kernel
private theorem c4687_iso   : LeafIso 4687    := by decide +kernel
private theorem c4687_nof2  : NoF2ChkSq 4687  := by decide +kernel
private theorem c4687_nof3  : NoF3ChkSq 4687  := by decide +kernel
private theorem c4687_nof4z : NoF4zChkSq 4687 := by decide +kernel
theorem C'_4687 : C' 4687 :=
  ⟨c4687_sqf, c4687_range, c4687_ell, leafNSq_of_sq c4687_nsq, leafHAr_of_sq c4687_har,
   c4687_r, c4687_e', c4687_f1, leafS2_of_sq c4687_s2, leafS3_of_sq c4687_s3,
   c4687_iso, leafR8_of_sq c4687_nof2 c4687_nof3 c4687_nof4z⟩
theorem not_tile'_4687 (D : CongruentDissection 4687) : False :=
  not_tile_of_conditions' 4687 C'_4687 D

private theorem c4690_sqf   : LeafSqf 4690   := by decide +kernel
private theorem c4690_range : LeafRange 4690  := by decide +kernel
private theorem c4690_ell   : LeafEll 4690    := by decide +kernel
private theorem c4690_nsq   : NSqChkSq 4690   := by decide +kernel
private theorem c4690_har   : HArithChkSq 4690 := by decide +kernel
private theorem c4690_r     : LeafR 4690      := by decide +kernel
private theorem c4690_e'    : LeafE' 4690     := by decide +kernel
private theorem c4690_f1    : LeafF1 4690     := Or.inl (by decide)
private theorem c4690_s2    : S2ChkSq 4690    := by decide +kernel
private theorem c4690_s3    : S3ChkSq 4690    := by decide +kernel
private theorem c4690_iso   : LeafIso 4690    := by decide +kernel
private theorem c4690_nof2  : NoF2ChkSq 4690  := by decide +kernel
private theorem c4690_nof3  : NoF3ChkSq 4690  := by decide +kernel
private theorem c4690_nof4z : NoF4zChkSq 4690 := by decide +kernel
theorem C'_4690 : C' 4690 :=
  ⟨c4690_sqf, c4690_range, c4690_ell, leafNSq_of_sq c4690_nsq, leafHAr_of_sq c4690_har,
   c4690_r, c4690_e', c4690_f1, leafS2_of_sq c4690_s2, leafS3_of_sq c4690_s3,
   c4690_iso, leafR8_of_sq c4690_nof2 c4690_nof3 c4690_nof4z⟩
theorem not_tile'_4690 (D : CongruentDissection 4690) : False :=
  not_tile_of_conditions' 4690 C'_4690 D

private theorem c4691_sqf   : LeafSqf 4691   := by decide +kernel
private theorem c4691_range : LeafRange 4691  := by decide +kernel
private theorem c4691_ell   : LeafEll 4691    := by decide +kernel
private theorem c4691_nsq   : NSqChkSq 4691   := by decide +kernel
private theorem c4691_har   : HArithChkSq 4691 := by decide +kernel
private theorem c4691_r     : LeafR 4691      := by decide +kernel
private theorem c4691_e'    : LeafE' 4691     := by decide +kernel
private theorem c4691_f1    : LeafF1 4691     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4691_s2    : S2ChkSq 4691    := by decide +kernel
private theorem c4691_s3    : S3ChkSq 4691    := by decide +kernel
private theorem c4691_iso   : LeafIso 4691    := by decide +kernel
private theorem c4691_nof2  : NoF2ChkSq 4691  := by decide +kernel
private theorem c4691_nof3  : NoF3ChkSq 4691  := by decide +kernel
private theorem c4691_nof4z : NoF4zChkSq 4691 := by decide +kernel
theorem C'_4691 : C' 4691 :=
  ⟨c4691_sqf, c4691_range, c4691_ell, leafNSq_of_sq c4691_nsq, leafHAr_of_sq c4691_har,
   c4691_r, c4691_e', c4691_f1, leafS2_of_sq c4691_s2, leafS3_of_sq c4691_s3,
   c4691_iso, leafR8_of_sq c4691_nof2 c4691_nof3 c4691_nof4z⟩
theorem not_tile'_4691 (D : CongruentDissection 4691) : False :=
  not_tile_of_conditions' 4691 C'_4691 D

end Erdos634.Draft.AllN2

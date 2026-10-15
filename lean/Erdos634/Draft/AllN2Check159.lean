/- AllN2Check159: N = 3369, 3371, 3374, 3377, 3378
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c3369_sqf   : LeafSqf 3369   := by decide +kernel
private theorem c3369_range : LeafRange 3369  := by decide +kernel
private theorem c3369_ell   : LeafEll 3369    := by decide +kernel
private theorem c3369_nsq   : NSqChkSq 3369   := by decide +kernel
private theorem c3369_har   : HArithChkSq 3369 := by decide +kernel
private theorem c3369_r     : LeafR 3369      := by decide +kernel
private theorem c3369_e'    : LeafE' 3369     := by decide +kernel
private theorem c3369_f1    : LeafF1 3369     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3369_s2    : S2ChkSq 3369    := by decide +kernel
private theorem c3369_s3    : S3ChkSq 3369    := by decide +kernel
private theorem c3369_iso   : LeafIso 3369    := by decide +kernel
private theorem c3369_nof2  : NoF2ChkSq 3369  := by decide +kernel
private theorem c3369_nof3  : NoF3ChkSq 3369  := by decide +kernel
private theorem c3369_nof4z : NoF4zChkSq 3369 := by decide +kernel
theorem C'_3369 : C' 3369 :=
  ⟨c3369_sqf, c3369_range, c3369_ell, leafNSq_of_sq c3369_nsq, leafHAr_of_sq c3369_har,
   c3369_r, c3369_e', c3369_f1, leafS2_of_sq c3369_s2, leafS3_of_sq c3369_s3,
   c3369_iso, leafR8_of_sq c3369_nof2 c3369_nof3 c3369_nof4z⟩
theorem not_tile'_3369 (D : CongruentDissection 3369) : False :=
  not_tile_of_conditions' 3369 C'_3369 D

private theorem c3371_sqf   : LeafSqf 3371   := by decide +kernel
private theorem c3371_range : LeafRange 3371  := by decide +kernel
private theorem c3371_ell   : LeafEll 3371    := by decide +kernel
private theorem c3371_nsq   : NSqChkSq 3371   := by decide +kernel
private theorem c3371_har   : HArithChkSq 3371 := by decide +kernel
private theorem c3371_r     : LeafR 3371      := by decide +kernel
private theorem c3371_e'    : LeafE' 3371     := by decide +kernel
private theorem c3371_f1    : LeafF1 3371     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3371_s2    : S2ChkSq 3371    := by decide +kernel
private theorem c3371_s3    : S3ChkSq 3371    := by decide +kernel
private theorem c3371_iso   : LeafIso 3371    := by decide +kernel
private theorem c3371_nof2  : NoF2ChkSq 3371  := by decide +kernel
private theorem c3371_nof3  : NoF3ChkSq 3371  := by decide +kernel
private theorem c3371_nof4z : NoF4zChkSq 3371 := by decide +kernel
theorem C'_3371 : C' 3371 :=
  ⟨c3371_sqf, c3371_range, c3371_ell, leafNSq_of_sq c3371_nsq, leafHAr_of_sq c3371_har,
   c3371_r, c3371_e', c3371_f1, leafS2_of_sq c3371_s2, leafS3_of_sq c3371_s3,
   c3371_iso, leafR8_of_sq c3371_nof2 c3371_nof3 c3371_nof4z⟩
theorem not_tile'_3371 (D : CongruentDissection 3371) : False :=
  not_tile_of_conditions' 3371 C'_3371 D

private theorem c3374_sqf   : LeafSqf 3374   := by decide +kernel
private theorem c3374_range : LeafRange 3374  := by decide +kernel
private theorem c3374_ell   : LeafEll 3374    := by decide +kernel
private theorem c3374_nsq   : NSqChkSq 3374   := by decide +kernel
private theorem c3374_har   : HArithChkSq 3374 := by decide +kernel
private theorem c3374_r     : LeafR 3374      := by decide +kernel
private theorem c3374_e'    : LeafE' 3374     := by decide +kernel
private theorem c3374_f1    : LeafF1 3374     := Or.inl (by decide)
private theorem c3374_s2    : S2ChkSq 3374    := by decide +kernel
private theorem c3374_s3    : S3ChkSq 3374    := by decide +kernel
private theorem c3374_iso   : LeafIso 3374    := by decide +kernel
private theorem c3374_nof2  : NoF2ChkSq 3374  := by decide +kernel
private theorem c3374_nof3  : NoF3ChkSq 3374  := by decide +kernel
private theorem c3374_nof4z : NoF4zChkSq 3374 := by decide +kernel
theorem C'_3374 : C' 3374 :=
  ⟨c3374_sqf, c3374_range, c3374_ell, leafNSq_of_sq c3374_nsq, leafHAr_of_sq c3374_har,
   c3374_r, c3374_e', c3374_f1, leafS2_of_sq c3374_s2, leafS3_of_sq c3374_s3,
   c3374_iso, leafR8_of_sq c3374_nof2 c3374_nof3 c3374_nof4z⟩
theorem not_tile'_3374 (D : CongruentDissection 3374) : False :=
  not_tile_of_conditions' 3374 C'_3374 D

private theorem c3377_sqf   : LeafSqf 3377   := by decide +kernel
private theorem c3377_range : LeafRange 3377  := by decide +kernel
private theorem c3377_ell   : LeafEll 3377    := by decide +kernel
private theorem c3377_nsq   : NSqChkSq 3377   := by decide +kernel
private theorem c3377_har   : HArithChkSq 3377 := by decide +kernel
private theorem c3377_r     : LeafR 3377      := by decide +kernel
private theorem c3377_e'    : LeafE' 3377     := by decide +kernel
private theorem c3377_f1    : LeafF1 3377     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c3377_s2    : S2ChkSq 3377    := by decide +kernel
private theorem c3377_s3    : S3ChkSq 3377    := by decide +kernel
private theorem c3377_iso   : LeafIso 3377    := by decide +kernel
private theorem c3377_nof2  : NoF2ChkSq 3377  := by decide +kernel
private theorem c3377_nof3  : NoF3ChkSq 3377  := by decide +kernel
private theorem c3377_nof4z : NoF4zChkSq 3377 := by decide +kernel
theorem C'_3377 : C' 3377 :=
  ⟨c3377_sqf, c3377_range, c3377_ell, leafNSq_of_sq c3377_nsq, leafHAr_of_sq c3377_har,
   c3377_r, c3377_e', c3377_f1, leafS2_of_sq c3377_s2, leafS3_of_sq c3377_s3,
   c3377_iso, leafR8_of_sq c3377_nof2 c3377_nof3 c3377_nof4z⟩
theorem not_tile'_3377 (D : CongruentDissection 3377) : False :=
  not_tile_of_conditions' 3377 C'_3377 D

private theorem c3378_sqf   : LeafSqf 3378   := by decide +kernel
private theorem c3378_range : LeafRange 3378  := by decide +kernel
private theorem c3378_ell   : LeafEll 3378    := by decide +kernel
private theorem c3378_nsq   : NSqChkSq 3378   := by decide +kernel
private theorem c3378_har   : HArithChkSq 3378 := by decide +kernel
private theorem c3378_r     : LeafR 3378      := by decide +kernel
private theorem c3378_e'    : LeafE' 3378     := by decide +kernel
private theorem c3378_f1    : LeafF1 3378     := Or.inl (by decide)
private theorem c3378_s2    : S2ChkSq 3378    := by decide +kernel
private theorem c3378_s3    : S3ChkSq 3378    := by decide +kernel
private theorem c3378_iso   : LeafIso 3378    := by decide +kernel
private theorem c3378_nof2  : NoF2ChkSq 3378  := by decide +kernel
private theorem c3378_nof3  : NoF3ChkSq 3378  := by decide +kernel
private theorem c3378_nof4z : NoF4zChkSq 3378 := by decide +kernel
theorem C'_3378 : C' 3378 :=
  ⟨c3378_sqf, c3378_range, c3378_ell, leafNSq_of_sq c3378_nsq, leafHAr_of_sq c3378_har,
   c3378_r, c3378_e', c3378_f1, leafS2_of_sq c3378_s2, leafS3_of_sq c3378_s3,
   c3378_iso, leafR8_of_sq c3378_nof2 c3378_nof3 c3378_nof4z⟩
theorem not_tile'_3378 (D : CongruentDissection 3378) : False :=
  not_tile_of_conditions' 3378 C'_3378 D

end Erdos634.Draft.AllN2

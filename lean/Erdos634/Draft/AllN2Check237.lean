/- AllN2Check237: N = 4379, 4382, 4387, 4390, 4391
   Squarefree exclusions via C' with sqrt-bounded checks. -/
import Erdos634.Draft.AllN2Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN2
open Erdos634.Draft.AllNExclusion Erdos634.Geometry

private theorem c4379_sqf   : LeafSqf 4379   := by decide +kernel
private theorem c4379_range : LeafRange 4379  := by decide +kernel
private theorem c4379_ell   : LeafEll 4379    := by decide +kernel
private theorem c4379_nsq   : NSqChkSq 4379   := by decide +kernel
private theorem c4379_har   : HArithChkSq 4379 := by decide +kernel
private theorem c4379_r     : LeafR 4379      := by decide +kernel
private theorem c4379_e'    : LeafE' 4379     := by decide +kernel
private theorem c4379_f1    : LeafF1 4379     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4379_s2    : S2ChkSq 4379    := by decide +kernel
private theorem c4379_s3    : S3ChkSq 4379    := by decide +kernel
private theorem c4379_iso   : LeafIso 4379    := by decide +kernel
private theorem c4379_nof2  : NoF2ChkSq 4379  := by decide +kernel
private theorem c4379_nof3  : NoF3ChkSq 4379  := by decide +kernel
private theorem c4379_nof4z : NoF4zChkSq 4379 := by decide +kernel
theorem C'_4379 : C' 4379 :=
  ⟨c4379_sqf, c4379_range, c4379_ell, leafNSq_of_sq c4379_nsq, leafHAr_of_sq c4379_har,
   c4379_r, c4379_e', c4379_f1, leafS2_of_sq c4379_s2, leafS3_of_sq c4379_s3,
   c4379_iso, leafR8_of_sq c4379_nof2 c4379_nof3 c4379_nof4z⟩
theorem not_tile'_4379 (D : CongruentDissection 4379) : False :=
  not_tile_of_conditions' 4379 C'_4379 D

private theorem c4382_sqf   : LeafSqf 4382   := by decide +kernel
private theorem c4382_range : LeafRange 4382  := by decide +kernel
private theorem c4382_ell   : LeafEll 4382    := by decide +kernel
private theorem c4382_nsq   : NSqChkSq 4382   := by decide +kernel
private theorem c4382_har   : HArithChkSq 4382 := by decide +kernel
private theorem c4382_r     : LeafR 4382      := by decide +kernel
private theorem c4382_e'    : LeafE' 4382     := by decide +kernel
private theorem c4382_f1    : LeafF1 4382     := Or.inl (by decide)
private theorem c4382_s2    : S2ChkSq 4382    := by decide +kernel
private theorem c4382_s3    : S3ChkSq 4382    := by decide +kernel
private theorem c4382_iso   : LeafIso 4382    := by decide +kernel
private theorem c4382_nof2  : NoF2ChkSq 4382  := by decide +kernel
private theorem c4382_nof3  : NoF3ChkSq 4382  := by decide +kernel
private theorem c4382_nof4z : NoF4zChkSq 4382 := by decide +kernel
theorem C'_4382 : C' 4382 :=
  ⟨c4382_sqf, c4382_range, c4382_ell, leafNSq_of_sq c4382_nsq, leafHAr_of_sq c4382_har,
   c4382_r, c4382_e', c4382_f1, leafS2_of_sq c4382_s2, leafS3_of_sq c4382_s3,
   c4382_iso, leafR8_of_sq c4382_nof2 c4382_nof3 c4382_nof4z⟩
theorem not_tile'_4382 (D : CongruentDissection 4382) : False :=
  not_tile_of_conditions' 4382 C'_4382 D

private theorem c4387_sqf   : LeafSqf 4387   := by decide +kernel
private theorem c4387_range : LeafRange 4387  := by decide +kernel
private theorem c4387_ell   : LeafEll 4387    := by decide +kernel
private theorem c4387_nsq   : NSqChkSq 4387   := by decide +kernel
private theorem c4387_har   : HArithChkSq 4387 := by decide +kernel
private theorem c4387_r     : LeafR 4387      := by decide +kernel
private theorem c4387_e'    : LeafE' 4387     := by decide +kernel
private theorem c4387_f1    : LeafF1 4387     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4387_s2    : S2ChkSq 4387    := by decide +kernel
private theorem c4387_s3    : S3ChkSq 4387    := by decide +kernel
private theorem c4387_iso   : LeafIso 4387    := by decide +kernel
private theorem c4387_nof2  : NoF2ChkSq 4387  := by decide +kernel
private theorem c4387_nof3  : NoF3ChkSq 4387  := by decide +kernel
private theorem c4387_nof4z : NoF4zChkSq 4387 := by decide +kernel
theorem C'_4387 : C' 4387 :=
  ⟨c4387_sqf, c4387_range, c4387_ell, leafNSq_of_sq c4387_nsq, leafHAr_of_sq c4387_har,
   c4387_r, c4387_e', c4387_f1, leafS2_of_sq c4387_s2, leafS3_of_sq c4387_s3,
   c4387_iso, leafR8_of_sq c4387_nof2 c4387_nof3 c4387_nof4z⟩
theorem not_tile'_4387 (D : CongruentDissection 4387) : False :=
  not_tile_of_conditions' 4387 C'_4387 D

private theorem c4390_sqf   : LeafSqf 4390   := by decide +kernel
private theorem c4390_range : LeafRange 4390  := by decide +kernel
private theorem c4390_ell   : LeafEll 4390    := by decide +kernel
private theorem c4390_nsq   : NSqChkSq 4390   := by decide +kernel
private theorem c4390_har   : HArithChkSq 4390 := by decide +kernel
private theorem c4390_r     : LeafR 4390      := by decide +kernel
private theorem c4390_e'    : LeafE' 4390     := by decide +kernel
private theorem c4390_f1    : LeafF1 4390     := Or.inl (by decide)
private theorem c4390_s2    : S2ChkSq 4390    := by decide +kernel
private theorem c4390_s3    : S3ChkSq 4390    := by decide +kernel
private theorem c4390_iso   : LeafIso 4390    := by decide +kernel
private theorem c4390_nof2  : NoF2ChkSq 4390  := by decide +kernel
private theorem c4390_nof3  : NoF3ChkSq 4390  := by decide +kernel
private theorem c4390_nof4z : NoF4zChkSq 4390 := by decide +kernel
theorem C'_4390 : C' 4390 :=
  ⟨c4390_sqf, c4390_range, c4390_ell, leafNSq_of_sq c4390_nsq, leafHAr_of_sq c4390_har,
   c4390_r, c4390_e', c4390_f1, leafS2_of_sq c4390_s2, leafS3_of_sq c4390_s3,
   c4390_iso, leafR8_of_sq c4390_nof2 c4390_nof3 c4390_nof4z⟩
theorem not_tile'_4390 (D : CongruentDissection 4390) : False :=
  not_tile_of_conditions' 4390 C'_4390 D

private theorem c4391_sqf   : LeafSqf 4391   := by decide +kernel
private theorem c4391_range : LeafRange 4391  := by decide +kernel
private theorem c4391_ell   : LeafEll 4391    := by decide +kernel
private theorem c4391_nsq   : NSqChkSq 4391   := by decide +kernel
private theorem c4391_har   : HArithChkSq 4391 := by decide +kernel
private theorem c4391_r     : LeafR 4391      := by decide +kernel
private theorem c4391_e'    : LeafE' 4391     := by decide +kernel
private theorem c4391_f1    : LeafF1 4391     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c4391_s2    : S2ChkSq 4391    := by decide +kernel
private theorem c4391_s3    : S3ChkSq 4391    := by decide +kernel
private theorem c4391_iso   : LeafIso 4391    := by decide +kernel
private theorem c4391_nof2  : NoF2ChkSq 4391  := by decide +kernel
private theorem c4391_nof3  : NoF3ChkSq 4391  := by decide +kernel
private theorem c4391_nof4z : NoF4zChkSq 4391 := by decide +kernel
theorem C'_4391 : C' 4391 :=
  ⟨c4391_sqf, c4391_range, c4391_ell, leafNSq_of_sq c4391_nsq, leafHAr_of_sq c4391_har,
   c4391_r, c4391_e', c4391_f1, leafS2_of_sq c4391_s2, leafS3_of_sq c4391_s3,
   c4391_iso, leafR8_of_sq c4391_nof2 c4391_nof3 c4391_nof4z⟩
theorem not_tile'_4391 (D : CongruentDissection 4391) : False :=
  not_tile_of_conditions' 4391 C'_4391 D

end Erdos634.Draft.AllN2

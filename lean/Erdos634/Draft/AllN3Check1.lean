/- AllN3Check1: N = 255, 285, 435, 438, 483, 555.
   Squarefree values excluded by `AllN3.C3` and not by `R8ZF.C''` (through the discriminant table of the `π/3` pairs,
   or, for 438 and 805, the base-`α` divisibility).  Kernel checks, leaf by leaf, with square-root-bounded loops.
   Composite-N work.  No sorry, no native_decide. -/
import Erdos634.Draft.AllN3Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN3
open Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2 Erdos634.Draft.R8ZF Erdos634.Geometry
open Erdos634.Draft.TileCountFamilies (TileCount)

private theorem c255_sqf   : LeafSqf 255   := by decide +kernel
private theorem c255_range : LeafRange 255  := by decide +kernel
private theorem c255_ell   : LeafEll 255    := by decide +kernel
private theorem c255_nsq   : NSqChkSq 255   := by decide +kernel
private theorem c255_har   : HArithChkSq 255 := by decide +kernel
private theorem c255_r     : LeafR 255      := by decide +kernel
private theorem c255_e     : LeafEsq 255    := by decide +kernel
private theorem c255_f1    : LeafF1 255     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c255_s2    : S2ChkSq 255    := by decide +kernel
private theorem c255_s3    : S3ChkDSq 255   := by decide +kernel
private theorem c255_iso   : LeafIso 255    := by decide +kernel
private theorem c255_nof2  : NoF2ChkSq 255  := by decide +kernel
private theorem c255_nof3  : NoF3zChkSq 255 := by decide +kernel
private theorem c255_nof4z : NoF4zChkSq 255 := by decide +kernel
theorem C3_255 : C3 255 :=
  ⟨c255_sqf, c255_range, c255_ell, leafNSq_of_sq c255_nsq, leafHAr_of_sq c255_har,
   c255_r, c255_e, c255_f1, leafS2_of_sq c255_s2, s3ChkD_of_sq c255_s3, c255_iso,
   leafR8z_of_sq c255_nof2 c255_nof3 c255_nof4z⟩
theorem not_tileCount_255 : ¬ TileCount 255 := not_tileCount_of_c3 C3_255

private theorem c285_sqf   : LeafSqf 285   := by decide +kernel
private theorem c285_range : LeafRange 285  := by decide +kernel
private theorem c285_ell   : LeafEll 285    := by decide +kernel
private theorem c285_nsq   : NSqChkSq 285   := by decide +kernel
private theorem c285_har   : HArithChkSq 285 := by decide +kernel
private theorem c285_r     : LeafR 285      := by decide +kernel
private theorem c285_e     : LeafEsq 285    := by decide +kernel
private theorem c285_f1    : LeafF1 285     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c285_s2    : S2ChkSq 285    := by decide +kernel
private theorem c285_s3    : S3ChkDSq 285   := by decide +kernel
private theorem c285_iso   : LeafIso 285    := by decide +kernel
private theorem c285_nof2  : NoF2ChkSq 285  := by decide +kernel
private theorem c285_nof3  : NoF3zChkSq 285 := by decide +kernel
private theorem c285_nof4z : NoF4zChkSq 285 := by decide +kernel
theorem C3_285 : C3 285 :=
  ⟨c285_sqf, c285_range, c285_ell, leafNSq_of_sq c285_nsq, leafHAr_of_sq c285_har,
   c285_r, c285_e, c285_f1, leafS2_of_sq c285_s2, s3ChkD_of_sq c285_s3, c285_iso,
   leafR8z_of_sq c285_nof2 c285_nof3 c285_nof4z⟩
theorem not_tileCount_285 : ¬ TileCount 285 := not_tileCount_of_c3 C3_285

private theorem c435_sqf   : LeafSqf 435   := by decide +kernel
private theorem c435_range : LeafRange 435  := by decide +kernel
private theorem c435_ell   : LeafEll 435    := by decide +kernel
private theorem c435_nsq   : NSqChkSq 435   := by decide +kernel
private theorem c435_har   : HArithChkSq 435 := by decide +kernel
private theorem c435_r     : LeafR 435      := by decide +kernel
private theorem c435_e     : LeafEsq 435    := by decide +kernel
private theorem c435_f1    : LeafF1 435     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c435_s2    : S2ChkSq 435    := by decide +kernel
private theorem c435_s3    : S3ChkDSq 435   := by decide +kernel
private theorem c435_iso   : LeafIso 435    := by decide +kernel
private theorem c435_nof2  : NoF2ChkSq 435  := by decide +kernel
private theorem c435_nof3  : NoF3zChkSq 435 := by decide +kernel
private theorem c435_nof4z : NoF4zChkSq 435 := by decide +kernel
theorem C3_435 : C3 435 :=
  ⟨c435_sqf, c435_range, c435_ell, leafNSq_of_sq c435_nsq, leafHAr_of_sq c435_har,
   c435_r, c435_e, c435_f1, leafS2_of_sq c435_s2, s3ChkD_of_sq c435_s3, c435_iso,
   leafR8z_of_sq c435_nof2 c435_nof3 c435_nof4z⟩
theorem not_tileCount_435 : ¬ TileCount 435 := not_tileCount_of_c3 C3_435

private theorem c438_sqf   : LeafSqf 438   := by decide +kernel
private theorem c438_range : LeafRange 438  := by decide +kernel
private theorem c438_ell   : LeafEll 438    := by decide +kernel
private theorem c438_nsq   : NSqChkSq 438   := by decide +kernel
private theorem c438_har   : HArithChkSq 438 := by decide +kernel
private theorem c438_r     : LeafR 438      := by decide +kernel
private theorem c438_e     : LeafEsq 438    := by decide +kernel
private theorem c438_f1    : LeafF1 438     := Or.inl (by decide)
private theorem c438_s2    : S2ChkSq 438    := by decide +kernel
private theorem c438_s3    : S3ChkDSq 438   := by decide +kernel
private theorem c438_iso   : LeafIso 438    := by decide +kernel
private theorem c438_nof2  : NoF2ChkSq 438  := by decide +kernel
private theorem c438_nof3  : NoF3zChkSq 438 := by decide +kernel
private theorem c438_nof4z : NoF4zChkSq 438 := by decide +kernel
theorem C3_438 : C3 438 :=
  ⟨c438_sqf, c438_range, c438_ell, leafNSq_of_sq c438_nsq, leafHAr_of_sq c438_har,
   c438_r, c438_e, c438_f1, leafS2_of_sq c438_s2, s3ChkD_of_sq c438_s3, c438_iso,
   leafR8z_of_sq c438_nof2 c438_nof3 c438_nof4z⟩
theorem not_tileCount_438 : ¬ TileCount 438 := not_tileCount_of_c3 C3_438

private theorem c483_sqf   : LeafSqf 483   := by decide +kernel
private theorem c483_range : LeafRange 483  := by decide +kernel
private theorem c483_ell   : LeafEll 483    := by decide +kernel
private theorem c483_nsq   : NSqChkSq 483   := by decide +kernel
private theorem c483_har   : HArithChkSq 483 := by decide +kernel
private theorem c483_r     : LeafR 483      := by decide +kernel
private theorem c483_e     : LeafEsq 483    := by decide +kernel
private theorem c483_f1    : LeafF1 483     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c483_s2    : S2ChkSq 483    := by decide +kernel
private theorem c483_s3    : S3ChkDSq 483   := by decide +kernel
private theorem c483_iso   : LeafIso 483    := by decide +kernel
private theorem c483_nof2  : NoF2ChkSq 483  := by decide +kernel
private theorem c483_nof3  : NoF3zChkSq 483 := by decide +kernel
private theorem c483_nof4z : NoF4zChkSq 483 := by decide +kernel
theorem C3_483 : C3 483 :=
  ⟨c483_sqf, c483_range, c483_ell, leafNSq_of_sq c483_nsq, leafHAr_of_sq c483_har,
   c483_r, c483_e, c483_f1, leafS2_of_sq c483_s2, s3ChkD_of_sq c483_s3, c483_iso,
   leafR8z_of_sq c483_nof2 c483_nof3 c483_nof4z⟩
theorem not_tileCount_483 : ¬ TileCount 483 := not_tileCount_of_c3 C3_483

private theorem c555_sqf   : LeafSqf 555   := by decide +kernel
private theorem c555_range : LeafRange 555  := by decide +kernel
private theorem c555_ell   : LeafEll 555    := by decide +kernel
private theorem c555_nsq   : NSqChkSq 555   := by decide +kernel
private theorem c555_har   : HArithChkSq 555 := by decide +kernel
private theorem c555_r     : LeafR 555      := by decide +kernel
private theorem c555_e     : LeafEsq 555    := by decide +kernel
private theorem c555_f1    : LeafF1 555     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c555_s2    : S2ChkSq 555    := by decide +kernel
private theorem c555_s3    : S3ChkDSq 555   := by decide +kernel
private theorem c555_iso   : LeafIso 555    := by decide +kernel
private theorem c555_nof2  : NoF2ChkSq 555  := by decide +kernel
private theorem c555_nof3  : NoF3zChkSq 555 := by decide +kernel
private theorem c555_nof4z : NoF4zChkSq 555 := by decide +kernel
theorem C3_555 : C3 555 :=
  ⟨c555_sqf, c555_range, c555_ell, leafNSq_of_sq c555_nsq, leafHAr_of_sq c555_har,
   c555_r, c555_e, c555_f1, leafS2_of_sq c555_s2, s3ChkD_of_sq c555_s3, c555_iso,
   leafR8z_of_sq c555_nof2 c555_nof3 c555_nof4z⟩
theorem not_tileCount_555 : ¬ TileCount 555 := not_tileCount_of_c3 C3_555

/-- the gain is real: `255` fails the old `π/3` table (the irrational pair `(51, 15)`), and `438` fails the old
base-`α` check (the solution `(e, d, m)` of the reduced equation has `d ∤ m`) -/
theorem old_checks_fail : ¬ LeafE' 255 ∧ ¬ S3ChkSq 438 := ⟨by decide +kernel, by decide +kernel⟩

end Erdos634.Draft.AllN3

#print axioms Erdos634.Draft.AllN3.not_tileCount_255

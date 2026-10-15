/- AllN3Check2: N = 609, 615, 645, 651, 705, 795.
   Squarefree values excluded by `AllN3.C3` and not by `R8ZF.C''` (through the discriminant table of the `π/3` pairs,
   or, for 438 and 805, the base-`α` divisibility).  Kernel checks, leaf by leaf, with square-root-bounded loops.
   Composite-N work.  No sorry, no native_decide. -/
import Erdos634.Draft.AllN3Cond
set_option maxRecDepth 8000
namespace Erdos634.Draft.AllN3
open Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2 Erdos634.Draft.R8ZF Erdos634.Geometry
open Erdos634.Draft.TileCountFamilies (TileCount)

private theorem c609_sqf   : LeafSqf 609   := by decide +kernel
private theorem c609_range : LeafRange 609  := by decide +kernel
private theorem c609_ell   : LeafEll 609    := by decide +kernel
private theorem c609_nsq   : NSqChkSq 609   := by decide +kernel
private theorem c609_har   : HArithChkSq 609 := by decide +kernel
private theorem c609_r     : LeafR 609      := by decide +kernel
private theorem c609_e     : LeafEsq 609    := by decide +kernel
private theorem c609_f1    : LeafF1 609     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c609_s2    : S2ChkSq 609    := by decide +kernel
private theorem c609_s3    : S3ChkDSq 609   := by decide +kernel
private theorem c609_iso   : LeafIso 609    := by decide +kernel
private theorem c609_nof2  : NoF2ChkSq 609  := by decide +kernel
private theorem c609_nof3  : NoF3zChkSq 609 := by decide +kernel
private theorem c609_nof4z : NoF4zChkSq 609 := by decide +kernel
theorem C3_609 : C3 609 :=
  ⟨c609_sqf, c609_range, c609_ell, leafNSq_of_sq c609_nsq, leafHAr_of_sq c609_har,
   c609_r, c609_e, c609_f1, leafS2_of_sq c609_s2, s3ChkD_of_sq c609_s3, c609_iso,
   leafR8z_of_sq c609_nof2 c609_nof3 c609_nof4z⟩
theorem not_tileCount_609 : ¬ TileCount 609 := not_tileCount_of_c3 C3_609

private theorem c615_sqf   : LeafSqf 615   := by decide +kernel
private theorem c615_range : LeafRange 615  := by decide +kernel
private theorem c615_ell   : LeafEll 615    := by decide +kernel
private theorem c615_nsq   : NSqChkSq 615   := by decide +kernel
private theorem c615_har   : HArithChkSq 615 := by decide +kernel
private theorem c615_r     : LeafR 615      := by decide +kernel
private theorem c615_e     : LeafEsq 615    := by decide +kernel
private theorem c615_f1    : LeafF1 615     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c615_s2    : S2ChkSq 615    := by decide +kernel
private theorem c615_s3    : S3ChkDSq 615   := by decide +kernel
private theorem c615_iso   : LeafIso 615    := by decide +kernel
private theorem c615_nof2  : NoF2ChkSq 615  := by decide +kernel
private theorem c615_nof3  : NoF3zChkSq 615 := by decide +kernel
private theorem c615_nof4z : NoF4zChkSq 615 := by decide +kernel
theorem C3_615 : C3 615 :=
  ⟨c615_sqf, c615_range, c615_ell, leafNSq_of_sq c615_nsq, leafHAr_of_sq c615_har,
   c615_r, c615_e, c615_f1, leafS2_of_sq c615_s2, s3ChkD_of_sq c615_s3, c615_iso,
   leafR8z_of_sq c615_nof2 c615_nof3 c615_nof4z⟩
theorem not_tileCount_615 : ¬ TileCount 615 := not_tileCount_of_c3 C3_615

private theorem c645_sqf   : LeafSqf 645   := by decide +kernel
private theorem c645_range : LeafRange 645  := by decide +kernel
private theorem c645_ell   : LeafEll 645    := by decide +kernel
private theorem c645_nsq   : NSqChkSq 645   := by decide +kernel
private theorem c645_har   : HArithChkSq 645 := by decide +kernel
private theorem c645_r     : LeafR 645      := by decide +kernel
private theorem c645_e     : LeafEsq 645    := by decide +kernel
private theorem c645_f1    : LeafF1 645     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c645_s2    : S2ChkSq 645    := by decide +kernel
private theorem c645_s3    : S3ChkDSq 645   := by decide +kernel
private theorem c645_iso   : LeafIso 645    := by decide +kernel
private theorem c645_nof2  : NoF2ChkSq 645  := by decide +kernel
private theorem c645_nof3  : NoF3zChkSq 645 := by decide +kernel
private theorem c645_nof4z : NoF4zChkSq 645 := by decide +kernel
theorem C3_645 : C3 645 :=
  ⟨c645_sqf, c645_range, c645_ell, leafNSq_of_sq c645_nsq, leafHAr_of_sq c645_har,
   c645_r, c645_e, c645_f1, leafS2_of_sq c645_s2, s3ChkD_of_sq c645_s3, c645_iso,
   leafR8z_of_sq c645_nof2 c645_nof3 c645_nof4z⟩
theorem not_tileCount_645 : ¬ TileCount 645 := not_tileCount_of_c3 C3_645

private theorem c651_sqf   : LeafSqf 651   := by decide +kernel
private theorem c651_range : LeafRange 651  := by decide +kernel
private theorem c651_ell   : LeafEll 651    := by decide +kernel
private theorem c651_nsq   : NSqChkSq 651   := by decide +kernel
private theorem c651_har   : HArithChkSq 651 := by decide +kernel
private theorem c651_r     : LeafR 651      := by decide +kernel
private theorem c651_e     : LeafEsq 651    := by decide +kernel
private theorem c651_f1    : LeafF1 651     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c651_s2    : S2ChkSq 651    := by decide +kernel
private theorem c651_s3    : S3ChkDSq 651   := by decide +kernel
private theorem c651_iso   : LeafIso 651    := by decide +kernel
private theorem c651_nof2  : NoF2ChkSq 651  := by decide +kernel
private theorem c651_nof3  : NoF3zChkSq 651 := by decide +kernel
private theorem c651_nof4z : NoF4zChkSq 651 := by decide +kernel
theorem C3_651 : C3 651 :=
  ⟨c651_sqf, c651_range, c651_ell, leafNSq_of_sq c651_nsq, leafHAr_of_sq c651_har,
   c651_r, c651_e, c651_f1, leafS2_of_sq c651_s2, s3ChkD_of_sq c651_s3, c651_iso,
   leafR8z_of_sq c651_nof2 c651_nof3 c651_nof4z⟩
theorem not_tileCount_651 : ¬ TileCount 651 := not_tileCount_of_c3 C3_651

private theorem c705_sqf   : LeafSqf 705   := by decide +kernel
private theorem c705_range : LeafRange 705  := by decide +kernel
private theorem c705_ell   : LeafEll 705    := by decide +kernel
private theorem c705_nsq   : NSqChkSq 705   := by decide +kernel
private theorem c705_har   : HArithChkSq 705 := by decide +kernel
private theorem c705_r     : LeafR 705      := by decide +kernel
private theorem c705_e     : LeafEsq 705    := by decide +kernel
private theorem c705_f1    : LeafF1 705     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c705_s2    : S2ChkSq 705    := by decide +kernel
private theorem c705_s3    : S3ChkDSq 705   := by decide +kernel
private theorem c705_iso   : LeafIso 705    := by decide +kernel
private theorem c705_nof2  : NoF2ChkSq 705  := by decide +kernel
private theorem c705_nof3  : NoF3zChkSq 705 := by decide +kernel
private theorem c705_nof4z : NoF4zChkSq 705 := by decide +kernel
theorem C3_705 : C3 705 :=
  ⟨c705_sqf, c705_range, c705_ell, leafNSq_of_sq c705_nsq, leafHAr_of_sq c705_har,
   c705_r, c705_e, c705_f1, leafS2_of_sq c705_s2, s3ChkD_of_sq c705_s3, c705_iso,
   leafR8z_of_sq c705_nof2 c705_nof3 c705_nof4z⟩
theorem not_tileCount_705 : ¬ TileCount 705 := not_tileCount_of_c3 C3_705

private theorem c795_sqf   : LeafSqf 795   := by decide +kernel
private theorem c795_range : LeafRange 795  := by decide +kernel
private theorem c795_ell   : LeafEll 795    := by decide +kernel
private theorem c795_nsq   : NSqChkSq 795   := by decide +kernel
private theorem c795_har   : HArithChkSq 795 := by decide +kernel
private theorem c795_r     : LeafR 795      := by decide +kernel
private theorem c795_e     : LeafEsq 795    := by decide +kernel
private theorem c795_f1    : LeafF1 795     := Or.inr (f1chk_of_sq (by decide +kernel))
private theorem c795_s2    : S2ChkSq 795    := by decide +kernel
private theorem c795_s3    : S3ChkDSq 795   := by decide +kernel
private theorem c795_iso   : LeafIso 795    := by decide +kernel
private theorem c795_nof2  : NoF2ChkSq 795  := by decide +kernel
private theorem c795_nof3  : NoF3zChkSq 795 := by decide +kernel
private theorem c795_nof4z : NoF4zChkSq 795 := by decide +kernel
theorem C3_795 : C3 795 :=
  ⟨c795_sqf, c795_range, c795_ell, leafNSq_of_sq c795_nsq, leafHAr_of_sq c795_har,
   c795_r, c795_e, c795_f1, leafS2_of_sq c795_s2, s3ChkD_of_sq c795_s3, c795_iso,
   leafR8z_of_sq c795_nof2 c795_nof3 c795_nof4z⟩
theorem not_tileCount_795 : ¬ TileCount 795 := not_tileCount_of_c3 C3_795

end Erdos634.Draft.AllN3

#print axioms Erdos634.Draft.AllN3.not_tileCount_609

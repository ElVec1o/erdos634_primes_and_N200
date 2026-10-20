/-
Draft/NSQWinZ24028.lean -- `no_dissection_z24028` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_24028 : NQChkW 24028 := by decide +kernel
theorem zl2_24028 : (EllChk2 24028 ∨ AsqChk 24028) := by decide +kernel
theorem zl3_24028 : NSqChkSq 24028 := by decide +kernel
theorem zl4_24028 : HArithChkSq 24028 := by decide +kernel
theorem zl5_24028 : (24028 % 2 = 1 ∨ (24028 % 2 = 0 ∧ NHSqChkSq 24028)) := by decide +kernel
theorem zl6_24028 : LeafEsqW 24028 := by decide +kernel
theorem zl7_24028 : (24028 % 4 = 2 ∨ F1ChkParW 24028) := by decide +kernel
theorem zl8_24028 : S2ChkSq 24028 := by decide +kernel
theorem zl9_24028 : S3ChkSq 24028 := by decide +kernel
theorem zl10_24028 : IsoH9bChkW 24028 := by decide +kernel
theorem zl11_24028 : (NoF2ChkSq 24028 ∧ NoF3zChkSq 24028 ∧ NoF4zChkSq 24028) := by decide +kernel
theorem zl12_24028 : GammaChkDW 24028 := by decide +kernel
theorem zl13_24028 : S1t2ChkW 24028 := by decide +kernel
theorem zl14_24028 : RWChkT2W 24028 := by decide +kernel
theorem zl15_24028 : S5wChkW 24028 := by decide +kernel

theorem cnzETWD6_24028 : CN'zETWD6 24028 :=
  ⟨zl1_24028, zl2_24028, zl3_24028, zl4_24028, zl5_24028, zl6_24028, zl7_24028, zl8_24028, zl9_24028, zl10_24028, zl11_24028, zl12_24028, zl13_24028, zl14_24028, zl15_24028⟩
theorem no_dissection_z24028 (D : CongruentDissection 24028) : False := not_tile_of_conditionsNSQzETWD6 24028 cnzETWD6_24028 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z24028

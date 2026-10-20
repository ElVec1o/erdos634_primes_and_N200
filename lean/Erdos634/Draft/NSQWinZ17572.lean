/-
Draft/NSQWinZ17572.lean -- `no_dissection_z17572` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_17572 : NQChkW 17572 := by decide +kernel
theorem zl2_17572 : (EllChk2 17572 ∨ AsqChk 17572) := by decide +kernel
theorem zl3_17572 : NSqChkSq 17572 := by decide +kernel
theorem zl4_17572 : HArithChkSq 17572 := by decide +kernel
theorem zl5_17572 : (17572 % 2 = 1 ∨ (17572 % 2 = 0 ∧ NHSqChkSq 17572)) := by decide +kernel
theorem zl6_17572 : LeafEsqW 17572 := by decide +kernel
theorem zl7_17572 : (17572 % 4 = 2 ∨ F1ChkParW 17572) := by decide +kernel
theorem zl8_17572 : S2ChkSq 17572 := by decide +kernel
theorem zl9_17572 : S3ChkSq 17572 := by decide +kernel
theorem zl10_17572 : IsoH9bChkW 17572 := by decide +kernel
theorem zl11_17572 : (NoF2ChkSq 17572 ∧ NoF3zChkSq 17572 ∧ NoF4zChkSq 17572) := by decide +kernel
theorem zl12_17572 : GammaChkDW 17572 := by decide +kernel
theorem zl13_17572 : S1t2ChkW 17572 := by decide +kernel
theorem zl14_17572 : RWChkT2W 17572 := by decide +kernel
theorem zl15_17572 : S5wChkW 17572 := by decide +kernel

theorem cnzETWD6_17572 : CN'zETWD6 17572 :=
  ⟨zl1_17572, zl2_17572, zl3_17572, zl4_17572, zl5_17572, zl6_17572, zl7_17572, zl8_17572, zl9_17572, zl10_17572, zl11_17572, zl12_17572, zl13_17572, zl14_17572, zl15_17572⟩
theorem no_dissection_z17572 (D : CongruentDissection 17572) : False := not_tile_of_conditionsNSQzETWD6 17572 cnzETWD6_17572 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z17572

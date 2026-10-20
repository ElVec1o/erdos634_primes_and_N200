/-
Draft/NSQWinZ41070.lean -- `no_dissection_z41070` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_41070 : NQChkW 41070 := by decide +kernel
theorem zl2_41070 : (EllChk2 41070 ∨ AsqChk 41070) := by decide +kernel
theorem zl3_41070 : NSqChkSq 41070 := by decide +kernel
theorem zl4_41070 : HArithChkSq 41070 := by decide +kernel
theorem zl5_41070 : (41070 % 2 = 1 ∨ (41070 % 2 = 0 ∧ NHSqChkSq 41070)) := by decide +kernel
theorem zl6_41070 : LeafEsqW 41070 := by decide +kernel
theorem zl7_41070 : (41070 % 4 = 2 ∨ F1ChkParW 41070) := by decide +kernel
theorem zl8_41070 : S2ChkSq 41070 := by decide +kernel
theorem zl9_41070 : S3ChkSq 41070 := by decide +kernel
theorem zl10_41070 : IsoH9bChkW 41070 := by decide +kernel
theorem zl11_41070 : (NoF2ChkSq 41070 ∧ NoF3zChkSq 41070 ∧ NoF4zChkSq 41070) := by decide +kernel
theorem zl12_41070 : GammaChkDW 41070 := by decide +kernel
theorem zl13_41070 : S1t2ChkW 41070 := by decide +kernel
theorem zl14_41070 : RWChkT2W 41070 := by decide +kernel
theorem zl15_41070 : S5wChkW 41070 := by decide +kernel

theorem cnzETWD6_41070 : CN'zETWD6 41070 :=
  ⟨zl1_41070, zl2_41070, zl3_41070, zl4_41070, zl5_41070, zl6_41070, zl7_41070, zl8_41070, zl9_41070, zl10_41070, zl11_41070, zl12_41070, zl13_41070, zl14_41070, zl15_41070⟩
theorem no_dissection_z41070 (D : CongruentDissection 41070) : False := not_tile_of_conditionsNSQzETWD6 41070 cnzETWD6_41070 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z41070

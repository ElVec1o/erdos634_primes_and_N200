/-
Draft/NSQWinZ18750.lean -- `no_dissection_z18750` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_18750 : NQChkW 18750 := by decide +kernel
theorem zl2_18750 : (EllChk2 18750 ∨ AsqChk 18750) := by decide +kernel
theorem zl3_18750 : NSqChkSq 18750 := by decide +kernel
theorem zl4_18750 : HArithChkSq 18750 := by decide +kernel
theorem zl5_18750 : (18750 % 2 = 1 ∨ (18750 % 2 = 0 ∧ NHSqChkSq 18750)) := by decide +kernel
theorem zl6_18750 : LeafEsqW 18750 := by decide +kernel
theorem zl7_18750 : (18750 % 4 = 2 ∨ F1ChkParW 18750) := by decide +kernel
theorem zl8_18750 : S2ChkSq 18750 := by decide +kernel
theorem zl9_18750 : S3ChkSq 18750 := by decide +kernel
theorem zl10_18750 : IsoH9bChkW 18750 := by decide +kernel
theorem zl11_18750 : (NoF2ChkSq 18750 ∧ NoF3zChkSq 18750 ∧ NoF4zChkSq 18750) := by decide +kernel
theorem zl12_18750 : GammaChkDW 18750 := by decide +kernel
theorem zl13_18750 : S1t2ChkW 18750 := by decide +kernel
theorem zl14_18750 : RWChkT2W 18750 := by decide +kernel
theorem zl15_18750 : S5wChkW 18750 := by decide +kernel

theorem cnzETWD6_18750 : CN'zETWD6 18750 :=
  ⟨zl1_18750, zl2_18750, zl3_18750, zl4_18750, zl5_18750, zl6_18750, zl7_18750, zl8_18750, zl9_18750, zl10_18750, zl11_18750, zl12_18750, zl13_18750, zl14_18750, zl15_18750⟩
theorem no_dissection_z18750 (D : CongruentDissection 18750) : False := not_tile_of_conditionsNSQzETWD6 18750 cnzETWD6_18750 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z18750

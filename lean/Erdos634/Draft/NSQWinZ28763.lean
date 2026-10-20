/-
Draft/NSQWinZ28763.lean -- `no_dissection_z28763` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_28763 : NQChkW 28763 := by decide +kernel
theorem zl2_28763 : (EllChk2 28763 ∨ AsqChk 28763) := by decide +kernel
theorem zl3_28763 : NSqChkSq 28763 := by decide +kernel
theorem zl4_28763 : HArithChkSq 28763 := by decide +kernel
theorem zl5_28763 : (28763 % 2 = 1 ∨ (28763 % 2 = 0 ∧ NHSqChkSq 28763)) := by decide +kernel
theorem zl6_28763 : LeafEsqW 28763 := by decide +kernel
theorem zl7_28763 : (28763 % 4 = 2 ∨ F1ChkParW 28763) := by decide +kernel
theorem zl8_28763 : S2ChkSq 28763 := by decide +kernel
theorem zl9_28763 : S3ChkSq 28763 := by decide +kernel
theorem zl10_28763 : IsoH9bChkW 28763 := by decide +kernel
theorem zl11_28763 : (NoF2ChkSq 28763 ∧ NoF3zChkSq 28763 ∧ NoF4zChkSq 28763) := by decide +kernel
theorem zl12_28763 : GammaChkDW 28763 := by decide +kernel
theorem zl13_28763 : S1t2ChkW 28763 := by decide +kernel
theorem zl14_28763 : RWChkT2W 28763 := by decide +kernel
theorem zl15_28763 : S5wChkW 28763 := by decide +kernel

theorem cnzETWD6_28763 : CN'zETWD6 28763 :=
  ⟨zl1_28763, zl2_28763, zl3_28763, zl4_28763, zl5_28763, zl6_28763, zl7_28763, zl8_28763, zl9_28763, zl10_28763, zl11_28763, zl12_28763, zl13_28763, zl14_28763, zl15_28763⟩
theorem no_dissection_z28763 (D : CongruentDissection 28763) : False := not_tile_of_conditionsNSQzETWD6 28763 cnzETWD6_28763 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z28763

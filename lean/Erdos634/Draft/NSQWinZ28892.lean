/-
Draft/NSQWinZ28892.lean -- `no_dissection_z28892` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_28892 : NQChkW 28892 := by decide +kernel
theorem zl2_28892 : (EllChk2 28892 ∨ AsqChk 28892) := by decide +kernel
theorem zl3_28892 : NSqChkSq 28892 := by decide +kernel
theorem zl4_28892 : HArithChkSq 28892 := by decide +kernel
theorem zl5_28892 : (28892 % 2 = 1 ∨ (28892 % 2 = 0 ∧ NHSqChkSq 28892)) := by decide +kernel
theorem zl6_28892 : LeafEsqW 28892 := by decide +kernel
theorem zl7_28892 : (28892 % 4 = 2 ∨ F1ChkParW 28892) := by decide +kernel
theorem zl8_28892 : S2ChkSq 28892 := by decide +kernel
theorem zl9_28892 : S3ChkSq 28892 := by decide +kernel
theorem zl10_28892 : IsoH9bChkW 28892 := by decide +kernel
theorem zl11_28892 : (NoF2ChkSq 28892 ∧ NoF3zChkSq 28892 ∧ NoF4zChkSq 28892) := by decide +kernel
theorem zl12_28892 : GammaChkDW 28892 := by decide +kernel
theorem zl13_28892 : S1t2ChkW 28892 := by decide +kernel
theorem zl14_28892 : RWChkT2W 28892 := by decide +kernel
theorem zl15_28892 : S5wChkW 28892 := by decide +kernel

theorem cnzETWD6_28892 : CN'zETWD6 28892 :=
  ⟨zl1_28892, zl2_28892, zl3_28892, zl4_28892, zl5_28892, zl6_28892, zl7_28892, zl8_28892, zl9_28892, zl10_28892, zl11_28892, zl12_28892, zl13_28892, zl14_28892, zl15_28892⟩
theorem no_dissection_z28892 (D : CongruentDissection 28892) : False := not_tile_of_conditionsNSQzETWD6 28892 cnzETWD6_28892 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z28892

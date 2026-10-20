/-
Draft/NSQWinZ12124.lean -- `no_dissection_z12124` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_12124 : NQChkW 12124 := by decide +kernel
theorem zl2_12124 : (EllChk2 12124 ∨ AsqChk 12124) := by decide +kernel
theorem zl3_12124 : NSqChkSq 12124 := by decide +kernel
theorem zl4_12124 : HArithChkSq 12124 := by decide +kernel
theorem zl5_12124 : (12124 % 2 = 1 ∨ (12124 % 2 = 0 ∧ NHSqChkSq 12124)) := by decide +kernel
theorem zl6_12124 : LeafEsqW 12124 := by decide +kernel
theorem zl7_12124 : (12124 % 4 = 2 ∨ F1ChkParW 12124) := by decide +kernel
theorem zl8_12124 : S2ChkSq 12124 := by decide +kernel
theorem zl9_12124 : S3ChkSq 12124 := by decide +kernel
theorem zl10_12124 : IsoH9bChkW 12124 := by decide +kernel
theorem zl11_12124 : (NoF2ChkSq 12124 ∧ NoF3zChkSq 12124 ∧ NoF4zChkSq 12124) := by decide +kernel
theorem zl12_12124 : GammaChkDW 12124 := by decide +kernel
theorem zl13_12124 : S1t2ChkW 12124 := by decide +kernel
theorem zl14_12124 : RWChkT2W 12124 := by decide +kernel
theorem zl15_12124 : S5wChkW 12124 := by decide +kernel

theorem cnzETWD6_12124 : CN'zETWD6 12124 :=
  ⟨zl1_12124, zl2_12124, zl3_12124, zl4_12124, zl5_12124, zl6_12124, zl7_12124, zl8_12124, zl9_12124, zl10_12124, zl11_12124, zl12_12124, zl13_12124, zl14_12124, zl15_12124⟩
theorem no_dissection_z12124 (D : CongruentDissection 12124) : False := not_tile_of_conditionsNSQzETWD6 12124 cnzETWD6_12124 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z12124

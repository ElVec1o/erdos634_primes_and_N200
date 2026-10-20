/-
Draft/NSQWinZ42352.lean -- `no_dissection_z42352` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_42352 : NQChkW 42352 := by decide +kernel
theorem zl2_42352 : (EllChk2 42352 ∨ AsqChk 42352) := by decide +kernel
theorem zl3_42352 : NSqChkSq 42352 := by decide +kernel
theorem zl4_42352 : HArithChkSq 42352 := by decide +kernel
theorem zl5_42352 : (42352 % 2 = 1 ∨ (42352 % 2 = 0 ∧ NHSqChkSq 42352)) := by decide +kernel
theorem zl6_42352 : LeafEsqW 42352 := by decide +kernel
theorem zl7_42352 : (42352 % 4 = 2 ∨ F1ChkParW 42352) := by decide +kernel
theorem zl8_42352 : S2ChkSq 42352 := by decide +kernel
theorem zl9_42352 : S3ChkSq 42352 := by decide +kernel
theorem zl10_42352 : IsoH9bChkW 42352 := by decide +kernel
theorem zl11_42352 : (NoF2ChkSq 42352 ∧ NoF3zChkSq 42352 ∧ NoF4zChkSq 42352) := by decide +kernel
theorem zl12_42352 : GammaChkDW 42352 := by decide +kernel
theorem zl13_42352 : S1t2ChkW 42352 := by decide +kernel
theorem zl14_42352 : RWChkT2W 42352 := by decide +kernel
theorem zl15_42352 : S5wChkW 42352 := by decide +kernel

theorem cnzETWD6_42352 : CN'zETWD6 42352 :=
  ⟨zl1_42352, zl2_42352, zl3_42352, zl4_42352, zl5_42352, zl6_42352, zl7_42352, zl8_42352, zl9_42352, zl10_42352, zl11_42352, zl12_42352, zl13_42352, zl14_42352, zl15_42352⟩
theorem no_dissection_z42352 (D : CongruentDissection 42352) : False := not_tile_of_conditionsNSQzETWD6 42352 cnzETWD6_42352 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z42352

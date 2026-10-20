/-
Draft/NSQWinZ25230.lean -- `no_dissection_z25230` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_25230 : NQChkW 25230 := by decide +kernel
theorem zl2_25230 : (EllChk2 25230 ∨ AsqChk 25230) := by decide +kernel
theorem zl3_25230 : NSqChkSq 25230 := by decide +kernel
theorem zl4_25230 : HArithChkSq 25230 := by decide +kernel
theorem zl5_25230 : (25230 % 2 = 1 ∨ (25230 % 2 = 0 ∧ NHSqChkSq 25230)) := by decide +kernel
theorem zl6_25230 : LeafEsqW 25230 := by decide +kernel
theorem zl7_25230 : (25230 % 4 = 2 ∨ F1ChkParW 25230) := by decide +kernel
theorem zl8_25230 : S2ChkSq 25230 := by decide +kernel
theorem zl9_25230 : S3ChkSq 25230 := by decide +kernel
theorem zl10_25230 : IsoH9bChkW 25230 := by decide +kernel
theorem zl11_25230 : (NoF2ChkSq 25230 ∧ NoF3zChkSq 25230 ∧ NoF4zChkSq 25230) := by decide +kernel
theorem zl12_25230 : GammaChkDW 25230 := by decide +kernel
theorem zl13_25230 : S1t2ChkW 25230 := by decide +kernel
theorem zl14_25230 : RWChkT2W 25230 := by decide +kernel
theorem zl15_25230 : S5wChkW 25230 := by decide +kernel

theorem cnzETWD6_25230 : CN'zETWD6 25230 :=
  ⟨zl1_25230, zl2_25230, zl3_25230, zl4_25230, zl5_25230, zl6_25230, zl7_25230, zl8_25230, zl9_25230, zl10_25230, zl11_25230, zl12_25230, zl13_25230, zl14_25230, zl15_25230⟩
theorem no_dissection_z25230 (D : CongruentDissection 25230) : False := not_tile_of_conditionsNSQzETWD6 25230 cnzETWD6_25230 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z25230

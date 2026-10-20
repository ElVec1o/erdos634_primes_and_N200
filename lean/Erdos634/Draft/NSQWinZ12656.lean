/-
Draft/NSQWinZ12656.lean -- `no_dissection_z12656` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_12656 : NQChkW 12656 := by decide +kernel
theorem zl2_12656 : (EllChk2 12656 ∨ AsqChk 12656) := by decide +kernel
theorem zl3_12656 : NSqChkSq 12656 := by decide +kernel
theorem zl4_12656 : HArithChkSq 12656 := by decide +kernel
theorem zl5_12656 : (12656 % 2 = 1 ∨ (12656 % 2 = 0 ∧ NHSqChkSq 12656)) := by decide +kernel
theorem zl6_12656 : LeafEsqW 12656 := by decide +kernel
theorem zl7_12656 : (12656 % 4 = 2 ∨ F1ChkParW 12656) := by decide +kernel
theorem zl8_12656 : S2ChkSq 12656 := by decide +kernel
theorem zl9_12656 : S3ChkSq 12656 := by decide +kernel
theorem zl10_12656 : IsoH9bChkW 12656 := by decide +kernel
theorem zl11_12656 : (NoF2ChkSq 12656 ∧ NoF3zChkSq 12656 ∧ NoF4zChkSq 12656) := by decide +kernel
theorem zl12_12656 : GammaChkDW 12656 := by decide +kernel
theorem zl13_12656 : S1t2ChkW 12656 := by decide +kernel
theorem zl14_12656 : RWChkT2W 12656 := by decide +kernel
theorem zl15_12656 : S5wChkW 12656 := by decide +kernel

theorem cnzETWD6_12656 : CN'zETWD6 12656 :=
  ⟨zl1_12656, zl2_12656, zl3_12656, zl4_12656, zl5_12656, zl6_12656, zl7_12656, zl8_12656, zl9_12656, zl10_12656, zl11_12656, zl12_12656, zl13_12656, zl14_12656, zl15_12656⟩
theorem no_dissection_z12656 (D : CongruentDissection 12656) : False := not_tile_of_conditionsNSQzETWD6 12656 cnzETWD6_12656 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z12656

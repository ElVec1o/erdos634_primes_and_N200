/-
Draft/NSQWinZ25328.lean -- `no_dissection_z25328` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_25328 : NQChkW 25328 := by decide +kernel
theorem zl2_25328 : (EllChk2 25328 ∨ AsqChk 25328) := by decide +kernel
theorem zl3_25328 : NSqChkSq 25328 := by decide +kernel
theorem zl4_25328 : HArithChkSq 25328 := by decide +kernel
theorem zl5_25328 : (25328 % 2 = 1 ∨ (25328 % 2 = 0 ∧ NHSqChkSq 25328)) := by decide +kernel
theorem zl6_25328 : LeafEsqW 25328 := by decide +kernel
theorem zl7_25328 : (25328 % 4 = 2 ∨ F1ChkParW 25328) := by decide +kernel
theorem zl8_25328 : S2ChkSq 25328 := by decide +kernel
theorem zl9_25328 : S3ChkSq 25328 := by decide +kernel
theorem zl10_25328 : IsoH9bChkW 25328 := by decide +kernel
theorem zl11_25328 : (NoF2ChkSq 25328 ∧ NoF3zChkSq 25328 ∧ NoF4zChkSq 25328) := by decide +kernel
theorem zl12_25328 : GammaChkDW 25328 := by decide +kernel
theorem zl13_25328 : S1t2ChkW 25328 := by decide +kernel
theorem zl14_25328 : RWChkT2W 25328 := by decide +kernel
theorem zl15_25328 : S5wChkW 25328 := by decide +kernel

theorem cnzETWD6_25328 : CN'zETWD6 25328 :=
  ⟨zl1_25328, zl2_25328, zl3_25328, zl4_25328, zl5_25328, zl6_25328, zl7_25328, zl8_25328, zl9_25328, zl10_25328, zl11_25328, zl12_25328, zl13_25328, zl14_25328, zl15_25328⟩
theorem no_dissection_z25328 (D : CongruentDissection 25328) : False := not_tile_of_conditionsNSQzETWD6 25328 cnzETWD6_25328 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z25328

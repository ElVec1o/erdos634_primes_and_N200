/-
Draft/NSQWinZ15870.lean -- `no_dissection_z15870` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_15870 : NQChkW 15870 := by decide +kernel
theorem zl2_15870 : (EllChk2 15870 ∨ AsqChk 15870) := by decide +kernel
theorem zl3_15870 : NSqChkSq 15870 := by decide +kernel
theorem zl4_15870 : HArithChkSq 15870 := by decide +kernel
theorem zl5_15870 : (15870 % 2 = 1 ∨ (15870 % 2 = 0 ∧ NHSqChkSq 15870)) := by decide +kernel
theorem zl6_15870 : LeafEsqW 15870 := by decide +kernel
theorem zl7_15870 : (15870 % 4 = 2 ∨ F1ChkParW 15870) := by decide +kernel
theorem zl8_15870 : S2ChkSq 15870 := by decide +kernel
theorem zl9_15870 : S3ChkSq 15870 := by decide +kernel
theorem zl10_15870 : IsoH9bChkW 15870 := by decide +kernel
theorem zl11_15870 : (NoF2ChkSq 15870 ∧ NoF3zChkSq 15870 ∧ NoF4zChkSq 15870) := by decide +kernel
theorem zl12_15870 : GammaChkDW 15870 := by decide +kernel
theorem zl13_15870 : S1t2ChkW 15870 := by decide +kernel
theorem zl14_15870 : RWChkT2W 15870 := by decide +kernel
theorem zl15_15870 : S5wChkW 15870 := by decide +kernel

theorem cnzETWD6_15870 : CN'zETWD6 15870 :=
  ⟨zl1_15870, zl2_15870, zl3_15870, zl4_15870, zl5_15870, zl6_15870, zl7_15870, zl8_15870, zl9_15870, zl10_15870, zl11_15870, zl12_15870, zl13_15870, zl14_15870, zl15_15870⟩
theorem no_dissection_z15870 (D : CongruentDissection 15870) : False := not_tile_of_conditionsNSQzETWD6 15870 cnzETWD6_15870 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z15870

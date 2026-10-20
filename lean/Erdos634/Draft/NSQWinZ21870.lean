/-
Draft/NSQWinZ21870.lean -- `no_dissection_z21870` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_21870 : NQChkW 21870 := by decide +kernel
theorem zl2_21870 : (EllChk2 21870 ∨ AsqChk 21870) := by decide +kernel
theorem zl3_21870 : NSqChkSq 21870 := by decide +kernel
theorem zl4_21870 : HArithChkSq 21870 := by decide +kernel
theorem zl5_21870 : (21870 % 2 = 1 ∨ (21870 % 2 = 0 ∧ NHSqChkSq 21870)) := by decide +kernel
theorem zl6_21870 : LeafEsqW 21870 := by decide +kernel
theorem zl7_21870 : (21870 % 4 = 2 ∨ F1ChkParW 21870) := by decide +kernel
theorem zl8_21870 : S2ChkSq 21870 := by decide +kernel
theorem zl9_21870 : S3ChkSq 21870 := by decide +kernel
theorem zl10_21870 : IsoH9bChkW 21870 := by decide +kernel
theorem zl11_21870 : (NoF2ChkSq 21870 ∧ NoF3zChkSq 21870 ∧ NoF4zChkSq 21870) := by decide +kernel
theorem zl12_21870 : GammaChkDW 21870 := by decide +kernel
theorem zl13_21870 : S1t2ChkW 21870 := by decide +kernel
theorem zl14_21870 : RWChkT2W 21870 := by decide +kernel
theorem zl15_21870 : S5wChkW 21870 := by decide +kernel

theorem cnzETWD6_21870 : CN'zETWD6 21870 :=
  ⟨zl1_21870, zl2_21870, zl3_21870, zl4_21870, zl5_21870, zl6_21870, zl7_21870, zl8_21870, zl9_21870, zl10_21870, zl11_21870, zl12_21870, zl13_21870, zl14_21870, zl15_21870⟩
theorem no_dissection_z21870 (D : CongruentDissection 21870) : False := not_tile_of_conditionsNSQzETWD6 21870 cnzETWD6_21870 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z21870

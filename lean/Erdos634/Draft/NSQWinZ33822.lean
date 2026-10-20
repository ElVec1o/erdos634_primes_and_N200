/-
Draft/NSQWinZ33822.lean -- `no_dissection_z33822` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_33822 : NQChkW 33822 := by decide +kernel
theorem zl2_33822 : (EllChk2 33822 ∨ AsqChk 33822) := by decide +kernel
theorem zl3_33822 : NSqChkSq 33822 := by decide +kernel
theorem zl4_33822 : HArithChkSq 33822 := by decide +kernel
theorem zl5_33822 : (33822 % 2 = 1 ∨ (33822 % 2 = 0 ∧ NHSqChkSq 33822)) := by decide +kernel
theorem zl6_33822 : LeafEsqW 33822 := by decide +kernel
theorem zl7_33822 : (33822 % 4 = 2 ∨ F1ChkParW 33822) := by decide +kernel
theorem zl8_33822 : S2ChkSq 33822 := by decide +kernel
theorem zl9_33822 : S3ChkSq 33822 := by decide +kernel
theorem zl10_33822 : IsoH9bChkW 33822 := by decide +kernel
theorem zl11_33822 : (NoF2ChkSq 33822 ∧ NoF3zChkSq 33822 ∧ NoF4zChkSq 33822) := by decide +kernel
theorem zl12_33822 : GammaChkDW 33822 := by decide +kernel
theorem zl13_33822 : S1t2ChkW 33822 := by decide +kernel
theorem zl14_33822 : RWChkT2W 33822 := by decide +kernel
theorem zl15_33822 : S5wChkW 33822 := by decide +kernel

theorem cnzETWD6_33822 : CN'zETWD6 33822 :=
  ⟨zl1_33822, zl2_33822, zl3_33822, zl4_33822, zl5_33822, zl6_33822, zl7_33822, zl8_33822, zl9_33822, zl10_33822, zl11_33822, zl12_33822, zl13_33822, zl14_33822, zl15_33822⟩
theorem no_dissection_z33822 (D : CongruentDissection 33822) : False := not_tile_of_conditionsNSQzETWD6 33822 cnzETWD6_33822 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z33822

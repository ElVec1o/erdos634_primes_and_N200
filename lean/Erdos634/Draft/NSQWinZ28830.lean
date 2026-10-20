/-
Draft/NSQWinZ28830.lean -- `no_dissection_z28830` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_28830 : NQChkW 28830 := by decide +kernel
theorem zl2_28830 : (EllChk2 28830 ∨ AsqChk 28830) := by decide +kernel
theorem zl3_28830 : NSqChkSq 28830 := by decide +kernel
theorem zl4_28830 : HArithChkSq 28830 := by decide +kernel
theorem zl5_28830 : (28830 % 2 = 1 ∨ (28830 % 2 = 0 ∧ NHSqChkSq 28830)) := by decide +kernel
theorem zl6_28830 : LeafEsqW 28830 := by decide +kernel
theorem zl7_28830 : (28830 % 4 = 2 ∨ F1ChkParW 28830) := by decide +kernel
theorem zl8_28830 : S2ChkSq 28830 := by decide +kernel
theorem zl9_28830 : S3ChkSq 28830 := by decide +kernel
theorem zl10_28830 : IsoH9bChkW 28830 := by decide +kernel
theorem zl11_28830 : (NoF2ChkSq 28830 ∧ NoF3zChkSq 28830 ∧ NoF4zChkSq 28830) := by decide +kernel
theorem zl12_28830 : GammaChkDW 28830 := by decide +kernel
theorem zl13_28830 : S1t2ChkW 28830 := by decide +kernel
theorem zl14_28830 : RWChkT2W 28830 := by decide +kernel
theorem zl15_28830 : S5wChkW 28830 := by decide +kernel

theorem cnzETWD6_28830 : CN'zETWD6 28830 :=
  ⟨zl1_28830, zl2_28830, zl3_28830, zl4_28830, zl5_28830, zl6_28830, zl7_28830, zl8_28830, zl9_28830, zl10_28830, zl11_28830, zl12_28830, zl13_28830, zl14_28830, zl15_28830⟩
theorem no_dissection_z28830 (D : CongruentDissection 28830) : False := not_tile_of_conditionsNSQzETWD6 28830 cnzETWD6_28830 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z28830

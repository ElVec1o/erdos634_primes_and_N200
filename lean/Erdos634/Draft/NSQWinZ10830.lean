/-
Draft/NSQWinZ10830.lean -- `no_dissection_z10830` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_10830 : NQChkW 10830 := by decide +kernel
theorem zl2_10830 : (EllChk2 10830 ∨ AsqChk 10830) := by decide +kernel
theorem zl3_10830 : NSqChkSq 10830 := by decide +kernel
theorem zl4_10830 : HArithChkSq 10830 := by decide +kernel
theorem zl5_10830 : (10830 % 2 = 1 ∨ (10830 % 2 = 0 ∧ NHSqChkSq 10830)) := by decide +kernel
theorem zl6_10830 : LeafEsqW 10830 := by decide +kernel
theorem zl7_10830 : (10830 % 4 = 2 ∨ F1ChkParW 10830) := by decide +kernel
theorem zl8_10830 : S2ChkSq 10830 := by decide +kernel
theorem zl9_10830 : S3ChkSq 10830 := by decide +kernel
theorem zl10_10830 : IsoH9bChkW 10830 := by decide +kernel
theorem zl11_10830 : (NoF2ChkSq 10830 ∧ NoF3zChkSq 10830 ∧ NoF4zChkSq 10830) := by decide +kernel
theorem zl12_10830 : GammaChkDW 10830 := by decide +kernel
theorem zl13_10830 : S1t2ChkW 10830 := by decide +kernel
theorem zl14_10830 : RWChkT2W 10830 := by decide +kernel
theorem zl15_10830 : S5wChkW 10830 := by decide +kernel

theorem cnzETWD6_10830 : CN'zETWD6 10830 :=
  ⟨zl1_10830, zl2_10830, zl3_10830, zl4_10830, zl5_10830, zl6_10830, zl7_10830, zl8_10830, zl9_10830, zl10_10830, zl11_10830, zl12_10830, zl13_10830, zl14_10830, zl15_10830⟩
theorem no_dissection_z10830 (D : CongruentDissection 10830) : False := not_tile_of_conditionsNSQzETWD6 10830 cnzETWD6_10830 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z10830

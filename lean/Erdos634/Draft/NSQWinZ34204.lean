/-
Draft/NSQWinZ34204.lean -- `no_dissection_z34204` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_34204 : NQChkW 34204 := by decide +kernel
theorem zl2_34204 : (EllChk2 34204 ∨ AsqChk 34204) := by decide +kernel
theorem zl3_34204 : NSqChkSq 34204 := by decide +kernel
theorem zl4_34204 : HArithChkSq 34204 := by decide +kernel
theorem zl5_34204 : (34204 % 2 = 1 ∨ (34204 % 2 = 0 ∧ NHSqChkSq 34204)) := by decide +kernel
theorem zl6_34204 : LeafEsqW 34204 := by decide +kernel
theorem zl7_34204 : (34204 % 4 = 2 ∨ F1ChkParW 34204) := by decide +kernel
theorem zl8_34204 : S2ChkSq 34204 := by decide +kernel
theorem zl9_34204 : S3ChkSq 34204 := by decide +kernel
theorem zl10_34204 : IsoH9bChkW 34204 := by decide +kernel
theorem zl11_34204 : (NoF2ChkSq 34204 ∧ NoF3zChkSq 34204 ∧ NoF4zChkSq 34204) := by decide +kernel
theorem zl12_34204 : GammaChkDW 34204 := by decide +kernel
theorem zl13_34204 : S1t2ChkW 34204 := by decide +kernel
theorem zl14_34204 : RWChkT2W 34204 := by decide +kernel
theorem zl15_34204 : S5wChkW 34204 := by decide +kernel

theorem cnzETWD6_34204 : CN'zETWD6 34204 :=
  ⟨zl1_34204, zl2_34204, zl3_34204, zl4_34204, zl5_34204, zl6_34204, zl7_34204, zl8_34204, zl9_34204, zl10_34204, zl11_34204, zl12_34204, zl13_34204, zl14_34204, zl15_34204⟩
theorem no_dissection_z34204 (D : CongruentDissection 34204) : False := not_tile_of_conditionsNSQzETWD6 34204 cnzETWD6_34204 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z34204

/-
Draft/NSQWinZ26404.lean -- `no_dissection_z26404` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_26404 : NQChkW 26404 := by decide +kernel
theorem zl2_26404 : (EllChk2 26404 ∨ AsqChk 26404) := by decide +kernel
theorem zl3_26404 : NSqChkSq 26404 := by decide +kernel
theorem zl4_26404 : HArithChkSq 26404 := by decide +kernel
theorem zl5_26404 : (26404 % 2 = 1 ∨ (26404 % 2 = 0 ∧ NHSqChkSq 26404)) := by decide +kernel
theorem zl6_26404 : LeafEsqW 26404 := by decide +kernel
theorem zl7_26404 : (26404 % 4 = 2 ∨ F1ChkParW 26404) := by decide +kernel
theorem zl8_26404 : S2ChkSq 26404 := by decide +kernel
theorem zl9_26404 : S3ChkSq 26404 := by decide +kernel
theorem zl10_26404 : IsoH9bChkW 26404 := by decide +kernel
theorem zl11_26404 : (NoF2ChkSq 26404 ∧ NoF3zChkSq 26404 ∧ NoF4zChkSq 26404) := by decide +kernel
theorem zl12_26404 : GammaChkDW 26404 := by decide +kernel
theorem zl13_26404 : S1t2ChkW 26404 := by decide +kernel
theorem zl14_26404 : RWChkT2W 26404 := by decide +kernel
theorem zl15_26404 : S5wChkW 26404 := by decide +kernel

theorem cnzETWD6_26404 : CN'zETWD6 26404 :=
  ⟨zl1_26404, zl2_26404, zl3_26404, zl4_26404, zl5_26404, zl6_26404, zl7_26404, zl8_26404, zl9_26404, zl10_26404, zl11_26404, zl12_26404, zl13_26404, zl14_26404, zl15_26404⟩
theorem no_dissection_z26404 (D : CongruentDissection 26404) : False := not_tile_of_conditionsNSQzETWD6 26404 cnzETWD6_26404 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z26404

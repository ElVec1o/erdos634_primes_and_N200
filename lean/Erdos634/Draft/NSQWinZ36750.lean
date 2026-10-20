/-
Draft/NSQWinZ36750.lean -- `no_dissection_z36750` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_36750 : NQChkW 36750 := by decide +kernel
theorem zl2_36750 : (EllChk2 36750 ∨ AsqChk 36750) := by decide +kernel
theorem zl3_36750 : NSqChkSq 36750 := by decide +kernel
theorem zl4_36750 : HArithChkSq 36750 := by decide +kernel
theorem zl5_36750 : (36750 % 2 = 1 ∨ (36750 % 2 = 0 ∧ NHSqChkSq 36750)) := by decide +kernel
theorem zl6_36750 : LeafEsqW 36750 := by decide +kernel
theorem zl7_36750 : (36750 % 4 = 2 ∨ F1ChkParW 36750) := by decide +kernel
theorem zl8_36750 : S2ChkSq 36750 := by decide +kernel
theorem zl9_36750 : S3ChkSq 36750 := by decide +kernel
theorem zl10_36750 : IsoH9bChkW 36750 := by decide +kernel
theorem zl11_36750 : (NoF2ChkSq 36750 ∧ NoF3zChkSq 36750 ∧ NoF4zChkSq 36750) := by decide +kernel
theorem zl12_36750 : GammaChkDW 36750 := by decide +kernel
theorem zl13_36750 : S1t2ChkW 36750 := by decide +kernel
theorem zl14_36750 : RWChkT2W 36750 := by decide +kernel
theorem zl15_36750 : S5wChkW 36750 := by decide +kernel

theorem cnzETWD6_36750 : CN'zETWD6 36750 :=
  ⟨zl1_36750, zl2_36750, zl3_36750, zl4_36750, zl5_36750, zl6_36750, zl7_36750, zl8_36750, zl9_36750, zl10_36750, zl11_36750, zl12_36750, zl13_36750, zl14_36750, zl15_36750⟩
theorem no_dissection_z36750 (D : CongruentDissection 36750) : False := not_tile_of_conditionsNSQzETWD6 36750 cnzETWD6_36750 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z36750

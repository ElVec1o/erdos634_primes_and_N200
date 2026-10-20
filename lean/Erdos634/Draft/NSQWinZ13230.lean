/-
Draft/NSQWinZ13230.lean -- `no_dissection_z13230` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_13230 : NQChkW 13230 := by decide +kernel
theorem zl2_13230 : (EllChk2 13230 ∨ AsqChk 13230) := by decide +kernel
theorem zl3_13230 : NSqChkSq 13230 := by decide +kernel
theorem zl4_13230 : HArithChkSq 13230 := by decide +kernel
theorem zl5_13230 : (13230 % 2 = 1 ∨ (13230 % 2 = 0 ∧ NHSqChkSq 13230)) := by decide +kernel
theorem zl6_13230 : LeafEsqW 13230 := by decide +kernel
theorem zl7_13230 : (13230 % 4 = 2 ∨ F1ChkParW 13230) := by decide +kernel
theorem zl8_13230 : S2ChkSq 13230 := by decide +kernel
theorem zl9_13230 : S3ChkSq 13230 := by decide +kernel
theorem zl10_13230 : IsoH9bChkW 13230 := by decide +kernel
theorem zl11_13230 : (NoF2ChkSq 13230 ∧ NoF3zChkSq 13230 ∧ NoF4zChkSq 13230) := by decide +kernel
theorem zl12_13230 : GammaChkDW 13230 := by decide +kernel
theorem zl13_13230 : S1t2ChkW 13230 := by decide +kernel
theorem zl14_13230 : RWChkT2W 13230 := by decide +kernel
theorem zl15_13230 : S5wChkW 13230 := by decide +kernel

theorem cnzETWD6_13230 : CN'zETWD6 13230 :=
  ⟨zl1_13230, zl2_13230, zl3_13230, zl4_13230, zl5_13230, zl6_13230, zl7_13230, zl8_13230, zl9_13230, zl10_13230, zl11_13230, zl12_13230, zl13_13230, zl14_13230, zl15_13230⟩
theorem no_dissection_z13230 (D : CongruentDissection 13230) : False := not_tile_of_conditionsNSQzETWD6 13230 cnzETWD6_13230 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z13230

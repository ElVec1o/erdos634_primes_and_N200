/-
Draft/NSQWinZ15966.lean -- `no_dissection_z15966` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_15966 : NQChkW 15966 := by decide +kernel
theorem zl2_15966 : (EllChk2 15966 ∨ AsqChk 15966) := by decide +kernel
theorem zl3_15966 : NSqChkSq 15966 := by decide +kernel
theorem zl4_15966 : HArithChkSq 15966 := by decide +kernel
theorem zl5_15966 : (15966 % 2 = 1 ∨ (15966 % 2 = 0 ∧ NHSqChkSq 15966)) := by decide +kernel
theorem zl6_15966 : LeafEsqW 15966 := by decide +kernel
theorem zl7_15966 : (15966 % 4 = 2 ∨ F1ChkParW 15966) := by decide +kernel
theorem zl8_15966 : S2ChkSq 15966 := by decide +kernel
theorem zl9_15966 : S3ChkSq 15966 := by decide +kernel
theorem zl10_15966 : IsoH9bChkW 15966 := by decide +kernel
theorem zl11_15966 : (NoF2ChkSq 15966 ∧ NoF3zChkSq 15966 ∧ NoF4zChkSq 15966) := by decide +kernel
theorem zl12_15966 : GammaChkDW 15966 := by decide +kernel
theorem zl13_15966 : S1t2ChkW 15966 := by decide +kernel
theorem zl14_15966 : RWChkT2W 15966 := by decide +kernel
theorem zl15_15966 : S5wChkW 15966 := by decide +kernel

theorem cnzETWD6_15966 : CN'zETWD6 15966 :=
  ⟨zl1_15966, zl2_15966, zl3_15966, zl4_15966, zl5_15966, zl6_15966, zl7_15966, zl8_15966, zl9_15966, zl10_15966, zl11_15966, zl12_15966, zl13_15966, zl14_15966, zl15_15966⟩
theorem no_dissection_z15966 (D : CongruentDissection 15966) : False := not_tile_of_conditionsNSQzETWD6 15966 cnzETWD6_15966 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z15966

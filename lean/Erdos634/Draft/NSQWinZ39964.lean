/-
Draft/NSQWinZ39964.lean -- `no_dissection_z39964` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_39964 : NQChkW 39964 := by decide +kernel
theorem zl2_39964 : (EllChk2 39964 ∨ AsqChk 39964) := by decide +kernel
theorem zl3_39964 : NSqChkSq 39964 := by decide +kernel
theorem zl4_39964 : HArithChkSq 39964 := by decide +kernel
theorem zl5_39964 : (39964 % 2 = 1 ∨ (39964 % 2 = 0 ∧ NHSqChkSq 39964)) := by decide +kernel
theorem zl6_39964 : LeafEsqW 39964 := by decide +kernel
theorem zl7_39964 : (39964 % 4 = 2 ∨ F1ChkParW 39964) := by decide +kernel
theorem zl8_39964 : S2ChkSq 39964 := by decide +kernel
theorem zl9_39964 : S3ChkSq 39964 := by decide +kernel
theorem zl10_39964 : IsoH9bChkW 39964 := by decide +kernel
theorem zl11_39964 : (NoF2ChkSq 39964 ∧ NoF3zChkSq 39964 ∧ NoF4zChkSq 39964) := by decide +kernel
theorem zl12_39964 : GammaChkDW 39964 := by decide +kernel
theorem zl13_39964 : S1t2ChkW 39964 := by decide +kernel
theorem zl14_39964 : RWChkT2W 39964 := by decide +kernel
theorem zl15_39964 : S5wChkW 39964 := by decide +kernel

theorem cnzETWD6_39964 : CN'zETWD6 39964 :=
  ⟨zl1_39964, zl2_39964, zl3_39964, zl4_39964, zl5_39964, zl6_39964, zl7_39964, zl8_39964, zl9_39964, zl10_39964, zl11_39964, zl12_39964, zl13_39964, zl14_39964, zl15_39964⟩
theorem no_dissection_z39964 (D : CongruentDissection 39964) : False := not_tile_of_conditionsNSQzETWD6 39964 cnzETWD6_39964 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z39964

/-
Draft/NSQWinZ32670.lean -- `no_dissection_z32670` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_32670 : NQChkW 32670 := by decide +kernel
theorem zl2_32670 : (EllChk2 32670 ∨ AsqChk 32670) := by decide +kernel
theorem zl3_32670 : NSqChkSq 32670 := by decide +kernel
theorem zl4_32670 : HArithChkSq 32670 := by decide +kernel
theorem zl5_32670 : (32670 % 2 = 1 ∨ (32670 % 2 = 0 ∧ NHSqChkSq 32670)) := by decide +kernel
theorem zl6_32670 : LeafEsqW 32670 := by decide +kernel
theorem zl7_32670 : (32670 % 4 = 2 ∨ F1ChkParW 32670) := by decide +kernel
theorem zl8_32670 : S2ChkSq 32670 := by decide +kernel
theorem zl9_32670 : S3ChkSq 32670 := by decide +kernel
theorem zl10_32670 : IsoH9bChkW 32670 := by decide +kernel
theorem zl11_32670 : (NoF2ChkSq 32670 ∧ NoF3zChkSq 32670 ∧ NoF4zChkSq 32670) := by decide +kernel
theorem zl12_32670 : GammaChkDW 32670 := by decide +kernel
theorem zl13_32670 : S1t2ChkW 32670 := by decide +kernel
theorem zl14_32670 : RWChkT2W 32670 := by decide +kernel
theorem zl15_32670 : S5wChkW 32670 := by decide +kernel

theorem cnzETWD6_32670 : CN'zETWD6 32670 :=
  ⟨zl1_32670, zl2_32670, zl3_32670, zl4_32670, zl5_32670, zl6_32670, zl7_32670, zl8_32670, zl9_32670, zl10_32670, zl11_32670, zl12_32670, zl13_32670, zl14_32670, zl15_32670⟩
theorem no_dissection_z32670 (D : CongruentDissection 32670) : False := not_tile_of_conditionsNSQzETWD6 32670 cnzETWD6_32670 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z32670

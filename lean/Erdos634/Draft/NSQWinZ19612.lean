/-
Draft/NSQWinZ19612.lean -- `no_dissection_z19612` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_19612 : NQChkW 19612 := by decide +kernel
theorem zl2_19612 : (EllChk2 19612 ∨ AsqChk 19612) := by decide +kernel
theorem zl3_19612 : NSqChkSq 19612 := by decide +kernel
theorem zl4_19612 : HArithChkSq 19612 := by decide +kernel
theorem zl5_19612 : (19612 % 2 = 1 ∨ (19612 % 2 = 0 ∧ NHSqChkSq 19612)) := by decide +kernel
theorem zl6_19612 : LeafEsqW 19612 := by decide +kernel
theorem zl7_19612 : (19612 % 4 = 2 ∨ F1ChkParW 19612) := by decide +kernel
theorem zl8_19612 : S2ChkSq 19612 := by decide +kernel
theorem zl9_19612 : S3ChkSq 19612 := by decide +kernel
theorem zl10_19612 : IsoH9bChkW 19612 := by decide +kernel
theorem zl11_19612 : (NoF2ChkSq 19612 ∧ NoF3zChkSq 19612 ∧ NoF4zChkSq 19612) := by decide +kernel
theorem zl12_19612 : GammaChkDW 19612 := by decide +kernel
theorem zl13_19612 : S1t2ChkW 19612 := by decide +kernel
theorem zl14_19612 : RWChkT2W 19612 := by decide +kernel
theorem zl15_19612 : S5wChkW 19612 := by decide +kernel

theorem cnzETWD6_19612 : CN'zETWD6 19612 :=
  ⟨zl1_19612, zl2_19612, zl3_19612, zl4_19612, zl5_19612, zl6_19612, zl7_19612, zl8_19612, zl9_19612, zl10_19612, zl11_19612, zl12_19612, zl13_19612, zl14_19612, zl15_19612⟩
theorem no_dissection_z19612 (D : CongruentDissection 19612) : False := not_tile_of_conditionsNSQzETWD6 19612 cnzETWD6_19612 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z19612

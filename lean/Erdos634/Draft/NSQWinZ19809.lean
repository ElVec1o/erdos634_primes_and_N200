/-
Draft/NSQWinZ19809.lean -- `no_dissection_z19809` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_19809 : NQChkW 19809 := by decide +kernel
theorem zl2_19809 : (EllChk2 19809 ∨ AsqChk 19809) := by decide +kernel
theorem zl3_19809 : NSqChkSq 19809 := by decide +kernel
theorem zl4_19809 : HArithChkSq 19809 := by decide +kernel
theorem zl5_19809 : (19809 % 2 = 1 ∨ (19809 % 2 = 0 ∧ NHSqChkSq 19809)) := by decide +kernel
theorem zl6_19809 : LeafEsqW 19809 := by decide +kernel
theorem zl7_19809 : (19809 % 4 = 2 ∨ F1ChkParW 19809) := by decide +kernel
theorem zl8_19809 : S2ChkSq 19809 := by decide +kernel
theorem zl9_19809 : S3ChkSq 19809 := by decide +kernel
theorem zl10_19809 : IsoH9bChkW 19809 := by decide +kernel
theorem zl11_19809 : (NoF2ChkSq 19809 ∧ NoF3zChkSq 19809 ∧ NoF4zChkSq 19809) := by decide +kernel
theorem zl12_19809 : GammaChkDW 19809 := by decide +kernel
theorem zl13_19809 : S1t2ChkW 19809 := by decide +kernel
theorem zl14_19809 : RWChkT2W 19809 := by decide +kernel
theorem zl15_19809 : S5wChkW 19809 := by decide +kernel

theorem cnzETWD6_19809 : CN'zETWD6 19809 :=
  ⟨zl1_19809, zl2_19809, zl3_19809, zl4_19809, zl5_19809, zl6_19809, zl7_19809, zl8_19809, zl9_19809, zl10_19809, zl11_19809, zl12_19809, zl13_19809, zl14_19809, zl15_19809⟩
theorem no_dissection_z19809 (D : CongruentDissection 19809) : False := not_tile_of_conditionsNSQzETWD6 19809 cnzETWD6_19809 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z19809

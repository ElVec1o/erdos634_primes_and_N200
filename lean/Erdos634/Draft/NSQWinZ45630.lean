/-
Draft/NSQWinZ45630.lean -- `no_dissection_z45630` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_45630 : NQChkW 45630 := by decide +kernel
theorem zl2_45630 : (EllChk2 45630 ∨ AsqChk 45630) := by decide +kernel
theorem zl3_45630 : NSqChkSq 45630 := by decide +kernel
theorem zl4_45630 : HArithChkSq 45630 := by decide +kernel
theorem zl5_45630 : (45630 % 2 = 1 ∨ (45630 % 2 = 0 ∧ NHSqChkSq 45630)) := by decide +kernel
theorem zl6_45630 : LeafEsqW 45630 := by decide +kernel
theorem zl7_45630 : (45630 % 4 = 2 ∨ F1ChkParW 45630) := by decide +kernel
theorem zl8_45630 : S2ChkSq 45630 := by decide +kernel
theorem zl9_45630 : S3ChkSq 45630 := by decide +kernel
theorem zl10_45630 : IsoH9bChkW 45630 := by decide +kernel
theorem zl11_45630 : (NoF2ChkSq 45630 ∧ NoF3zChkSq 45630 ∧ NoF4zChkSq 45630) := by decide +kernel
theorem zl12_45630 : GammaChkDW 45630 := by decide +kernel
theorem zl13_45630 : S1t2ChkW 45630 := by decide +kernel
theorem zl14_45630 : RWChkT2W 45630 := by decide +kernel
theorem zl15_45630 : S5wChkW 45630 := by decide +kernel

theorem cnzETWD6_45630 : CN'zETWD6 45630 :=
  ⟨zl1_45630, zl2_45630, zl3_45630, zl4_45630, zl5_45630, zl6_45630, zl7_45630, zl8_45630, zl9_45630, zl10_45630, zl11_45630, zl12_45630, zl13_45630, zl14_45630, zl15_45630⟩
theorem no_dissection_z45630 (D : CongruentDissection 45630) : False := not_tile_of_conditionsNSQzETWD6 45630 cnzETWD6_45630 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z45630

/-
Draft/NSQWinZ24066.lean -- `no_dissection_z24066` via the fully windowed chain `CN'zETWD6` (`NSQWin3`), the 15 leaves decided in SEPARATE kernel
declarations (kernel memory is per declaration, so the peak is the largest leaf, not the sum). Credit: Beeson-Rosu, Paliy, the S+ analysis.
UNAUDITED. No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin3

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain

theorem zl1_24066 : NQChkW 24066 := by decide +kernel
theorem zl2_24066 : (EllChk2 24066 ∨ AsqChk 24066) := by decide +kernel
theorem zl3_24066 : NSqChkSq 24066 := by decide +kernel
theorem zl4_24066 : HArithChkSq 24066 := by decide +kernel
theorem zl5_24066 : (24066 % 2 = 1 ∨ (24066 % 2 = 0 ∧ NHSqChkSq 24066)) := by decide +kernel
theorem zl6_24066 : LeafEsqW 24066 := by decide +kernel
theorem zl7_24066 : (24066 % 4 = 2 ∨ F1ChkParW 24066) := by decide +kernel
theorem zl8_24066 : S2ChkSq 24066 := by decide +kernel
theorem zl9_24066 : S3ChkSq 24066 := by decide +kernel
theorem zl10_24066 : IsoH9bChkW 24066 := by decide +kernel
theorem zl11_24066 : (NoF2ChkSq 24066 ∧ NoF3zChkSq 24066 ∧ NoF4zChkSq 24066) := by decide +kernel
theorem zl12_24066 : GammaChkDW 24066 := by decide +kernel
theorem zl13_24066 : S1t2ChkW 24066 := by decide +kernel
theorem zl14_24066 : RWChkT2W 24066 := by decide +kernel
theorem zl15_24066 : S5wChkW 24066 := by decide +kernel

theorem cnzETWD6_24066 : CN'zETWD6 24066 :=
  ⟨zl1_24066, zl2_24066, zl3_24066, zl4_24066, zl5_24066, zl6_24066, zl7_24066, zl8_24066, zl9_24066, zl10_24066, zl11_24066, zl12_24066, zl13_24066, zl14_24066, zl15_24066⟩
theorem no_dissection_z24066 (D : CongruentDissection 24066) : False := not_tile_of_conditionsNSQzETWD6 24066 cnzETWD6_24066 D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_dissection_z24066

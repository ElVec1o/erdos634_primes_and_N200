/-
Draft/WGapLinkI2108.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 2108.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_2108 : NQChkW 2108 := by decide +kernel
theorem wf2_2108 : (EllChk2 2108 ∨ AsqChk 2108) := by decide +kernel
theorem wf3_2108 : NSqChkSq 2108 := by decide +kernel
theorem wf4_2108 : HArithChkSq 2108 := by decide +kernel
theorem wf5_2108 : (2108 % 2 = 1 ∨ (2108 % 2 = 0 ∧ NHSqChkSq 2108)) := by decide +kernel
theorem wf6a_2108 : Pairs60ChkSq 2108 [] := by decide +kernel
theorem wf6b_2108 : Pairs120ChkSq 2108 [] := by decide +kernel
theorem wf6_2108 : LeafEsqS 2108 := Or.inr ⟨by norm_num, wf6a_2108, wf6b_2108⟩
theorem wf7_2108 : (2108 % 4 = 2 ∨ F1ChkParW 2108) := by decide +kernel
theorem wf8_2108 : S2ChkSq 2108 := by decide +kernel
theorem wf9_2108 : S3newChk 2108 := by decide +kernel
theorem wf10_2108 : IsoH9bChkW 2108 := by decide +kernel
theorem wf11a_2108 : NoF2ChkSq 2108 := by decide +kernel
theorem wf11b_2108 : NoF3zChkSq 2108 := by decide +kernel
theorem wf11c_2108 : NoF4zChkSq 2108 := by decide +kernel
theorem wf12_2108 : GammaChkDW 2108 := by decide +kernel
theorem wf13_2108 : Erdos634.Draft.S1Band.S1UBChkW 2108 := by decide +kernel
theorem wf14_2108 : RWChkW 2108 := by decide +kernel
theorem wf15_2108 : S5wChkW 2108 := by decide +kernel
theorem cnzFixW_2108 : CNzFixW 2108 :=
  ⟨wf1_2108, wf2_2108, wf3_2108, wf4_2108, wf5_2108, wf6_2108, wf7_2108, wf8_2108, wf9_2108, wf10_2108, ⟨wf11a_2108, wf11b_2108, wf11c_2108⟩, wf12_2108, wf13_2108, wf14_2108, wf15_2108⟩
theorem no_tileCount_W_2108 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 2108 := not_tileCount_of_CNzFixW 2108 cnzFixW_2108

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_2108

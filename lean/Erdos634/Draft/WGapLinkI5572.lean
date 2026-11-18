/-
Draft/WGapLinkI5572.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 5572.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_5572 : NQChkW 5572 := by decide +kernel
theorem wf2_5572 : (EllChk2 5572 ∨ AsqChk 5572) := by decide +kernel
theorem wf3_5572 : NSqChkSq 5572 := by decide +kernel
theorem wf4_5572 : HArithChkSq 5572 := by decide +kernel
theorem wf5_5572 : (5572 % 2 = 1 ∨ (5572 % 2 = 0 ∧ NHSqChkSq 5572)) := by decide +kernel
theorem wf6a_5572 : Pairs60ChkSq 5572 [] := by decide +kernel
theorem wf6b_5572 : Pairs120ChkSq 5572 [] := by decide +kernel
theorem wf6_5572 : LeafEsqS 5572 := Or.inr ⟨by norm_num, wf6a_5572, wf6b_5572⟩
theorem wf7_5572 : (5572 % 4 = 2 ∨ F1ChkParW 5572) := by decide +kernel
theorem wf8_5572 : S2ChkSq 5572 := by decide +kernel
theorem wf9_5572 : S3newChk 5572 := by decide +kernel
theorem wf10_5572 : IsoH9bChkW 5572 := by decide +kernel
theorem wf11a_5572 : NoF2ChkSq 5572 := by decide +kernel
theorem wf11b_5572 : NoF3zChkSq 5572 := by decide +kernel
theorem wf11c_5572 : NoF4zChkSq 5572 := by decide +kernel
theorem wf12_5572 : GammaChkDW 5572 := by decide +kernel
theorem wf13_5572 : Erdos634.Draft.S1Band.S1UBChkW 5572 := by decide +kernel
theorem wf14_5572 : RWChkW 5572 := by decide +kernel
theorem wf15_5572 : S5wChkW 5572 := by decide +kernel
theorem cnzFixW_5572 : CNzFixW 5572 :=
  ⟨wf1_5572, wf2_5572, wf3_5572, wf4_5572, wf5_5572, wf6_5572, wf7_5572, wf8_5572, wf9_5572, wf10_5572, ⟨wf11a_5572, wf11b_5572, wf11c_5572⟩, wf12_5572, wf13_5572, wf14_5572, wf15_5572⟩
theorem no_tileCount_W_5572 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 5572 := not_tileCount_of_CNzFixW 5572 cnzFixW_5572

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_5572

/-
Draft/WGapLinkI1988.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 1988.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_1988 : NQChkW 1988 := by decide +kernel
theorem wf2_1988 : (EllChk2 1988 ∨ AsqChk 1988) := by decide +kernel
theorem wf3_1988 : NSqChkSq 1988 := by decide +kernel
theorem wf4_1988 : HArithChkSq 1988 := by decide +kernel
theorem wf5_1988 : (1988 % 2 = 1 ∨ (1988 % 2 = 0 ∧ NHSqChkSq 1988)) := by decide +kernel
theorem wf6a_1988 : Pairs60ChkSq 1988 [] := by decide +kernel
theorem wf6b_1988 : Pairs120ChkSq 1988 [] := by decide +kernel
theorem wf6_1988 : LeafEsqS 1988 := Or.inr ⟨by norm_num, wf6a_1988, wf6b_1988⟩
theorem wf7_1988 : (1988 % 4 = 2 ∨ F1ChkParW 1988) := by decide +kernel
theorem wf8_1988 : S2ChkSq 1988 := by decide +kernel
theorem wf9_1988 : S3newChk 1988 := by decide +kernel
theorem wf10_1988 : IsoH9bChkW 1988 := by decide +kernel
theorem wf11a_1988 : NoF2ChkSq 1988 := by decide +kernel
theorem wf11b_1988 : NoF3zChkSq 1988 := by decide +kernel
theorem wf11c_1988 : NoF4zChkSq 1988 := by decide +kernel
theorem wf12_1988 : GammaChkDW 1988 := by decide +kernel
theorem wf13_1988 : Erdos634.Draft.S1Band.S1UBChkW 1988 := by decide +kernel
theorem wf14_1988 : RWChkW 1988 := by decide +kernel
theorem wf15_1988 : S5wChkW 1988 := by decide +kernel
theorem cnzFixW_1988 : CNzFixW 1988 :=
  ⟨wf1_1988, wf2_1988, wf3_1988, wf4_1988, wf5_1988, wf6_1988, wf7_1988, wf8_1988, wf9_1988, wf10_1988, ⟨wf11a_1988, wf11b_1988, wf11c_1988⟩, wf12_1988, wf13_1988, wf14_1988, wf15_1988⟩
theorem no_tileCount_W_1988 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 1988 := not_tileCount_of_CNzFixW 1988 cnzFixW_1988

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_1988

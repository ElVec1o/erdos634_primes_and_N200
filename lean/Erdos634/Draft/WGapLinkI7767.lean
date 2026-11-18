/-
Draft/WGapLinkI7767.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 7767.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_7767 : NQChkW 7767 := by decide +kernel
theorem wf2_7767 : (EllChk2 7767 ∨ AsqChk 7767) := by decide +kernel
theorem wf3_7767 : NSqChkSq 7767 := by decide +kernel
theorem wf4_7767 : HArithChkSq 7767 := by decide +kernel
theorem wf5_7767 : (7767 % 2 = 1 ∨ (7767 % 2 = 0 ∧ NHSqChkSq 7767)) := by decide +kernel
theorem wf6a_7767 : Pairs60ChkSq 7767 [] := by decide +kernel
theorem wf6b_7767 : Pairs120ChkSq 7767 [] := by decide +kernel
theorem wf6_7767 : LeafEsqS 7767 := Or.inr ⟨by norm_num, wf6a_7767, wf6b_7767⟩
theorem wf7_7767 : (7767 % 4 = 2 ∨ F1ChkParW 7767) := by decide +kernel
theorem wf8_7767 : S2ChkSq 7767 := by decide +kernel
theorem wf9_7767 : S3newChk 7767 := by decide +kernel
theorem wf10_7767 : IsoH9bChkW 7767 := by decide +kernel
theorem wf11a_7767 : NoF2ChkSq 7767 := by decide +kernel
theorem wf11b_7767 : NoF3zChkSq 7767 := by decide +kernel
theorem wf11c_7767 : NoF4zChkSq 7767 := by decide +kernel
theorem wf12_7767 : GammaChkDW 7767 := by decide +kernel
theorem wf13_7767 : Erdos634.Draft.S1Band.S1UBChkW 7767 := by decide +kernel
theorem wf14_7767 : RWChkW 7767 := by decide +kernel
theorem wf15_7767 : S5wChkW 7767 := by decide +kernel
theorem cnzFixW_7767 : CNzFixW 7767 :=
  ⟨wf1_7767, wf2_7767, wf3_7767, wf4_7767, wf5_7767, wf6_7767, wf7_7767, wf8_7767, wf9_7767, wf10_7767, ⟨wf11a_7767, wf11b_7767, wf11c_7767⟩, wf12_7767, wf13_7767, wf14_7767, wf15_7767⟩
theorem no_tileCount_W_7767 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 7767 := not_tileCount_of_CNzFixW 7767 cnzFixW_7767

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_7767

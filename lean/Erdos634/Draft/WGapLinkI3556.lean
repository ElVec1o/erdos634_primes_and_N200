/-
Draft/WGapLinkI3556.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 3556.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_3556 : NQChkW 3556 := by decide +kernel
theorem wf2_3556 : (EllChk2 3556 ∨ AsqChk 3556) := by decide +kernel
theorem wf3_3556 : NSqChkSq 3556 := by decide +kernel
theorem wf4_3556 : HArithChkSq 3556 := by decide +kernel
theorem wf5_3556 : (3556 % 2 = 1 ∨ (3556 % 2 = 0 ∧ NHSqChkSq 3556)) := by decide +kernel
theorem wf6a_3556 : Pairs60ChkSq 3556 [] := by decide +kernel
theorem wf6b_3556 : Pairs120ChkSq 3556 [] := by decide +kernel
theorem wf6_3556 : LeafEsqS 3556 := Or.inr ⟨by norm_num, wf6a_3556, wf6b_3556⟩
theorem wf7_3556 : (3556 % 4 = 2 ∨ F1ChkParW 3556) := by decide +kernel
theorem wf8_3556 : S2ChkSq 3556 := by decide +kernel
theorem wf9_3556 : S3newChk 3556 := by decide +kernel
theorem wf10_3556 : IsoH9bChkW 3556 := by decide +kernel
theorem wf11a_3556 : NoF2ChkSq 3556 := by decide +kernel
theorem wf11b_3556 : NoF3zChkSq 3556 := by decide +kernel
theorem wf11c_3556 : NoF4zChkSq 3556 := by decide +kernel
theorem wf12_3556 : GammaChkDW 3556 := by decide +kernel
theorem wf13_3556 : Erdos634.Draft.S1Band.S1UBChkW 3556 := by decide +kernel
theorem wf14_3556 : RWChkW 3556 := by decide +kernel
theorem wf15_3556 : S5wChkW 3556 := by decide +kernel
theorem cnzFixW_3556 : CNzFixW 3556 :=
  ⟨wf1_3556, wf2_3556, wf3_3556, wf4_3556, wf5_3556, wf6_3556, wf7_3556, wf8_3556, wf9_3556, wf10_3556, ⟨wf11a_3556, wf11b_3556, wf11c_3556⟩, wf12_3556, wf13_3556, wf14_3556, wf15_3556⟩
theorem no_tileCount_W_3556 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 3556 := not_tileCount_of_CNzFixW 3556 cnzFixW_3556

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_3556

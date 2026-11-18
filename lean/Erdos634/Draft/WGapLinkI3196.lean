/-
Draft/WGapLinkI3196.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 3196.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_3196 : NQChkW 3196 := by decide +kernel
theorem wf2_3196 : (EllChk2 3196 ∨ AsqChk 3196) := by decide +kernel
theorem wf3_3196 : NSqChkSq 3196 := by decide +kernel
theorem wf4_3196 : HArithChkSq 3196 := by decide +kernel
theorem wf5_3196 : (3196 % 2 = 1 ∨ (3196 % 2 = 0 ∧ NHSqChkSq 3196)) := by decide +kernel
theorem wf6a_3196 : Pairs60ChkSq 3196 [] := by decide +kernel
theorem wf6b_3196 : Pairs120ChkSq 3196 [] := by decide +kernel
theorem wf6_3196 : LeafEsqS 3196 := Or.inr ⟨by norm_num, wf6a_3196, wf6b_3196⟩
theorem wf7_3196 : (3196 % 4 = 2 ∨ F1ChkParW 3196) := by decide +kernel
theorem wf8_3196 : S2ChkSq 3196 := by decide +kernel
theorem wf9_3196 : S3newChk 3196 := by decide +kernel
theorem wf10_3196 : IsoH9bChkW 3196 := by decide +kernel
theorem wf11a_3196 : NoF2ChkSq 3196 := by decide +kernel
theorem wf11b_3196 : NoF3zChkSq 3196 := by decide +kernel
theorem wf11c_3196 : NoF4zChkSq 3196 := by decide +kernel
theorem wf12_3196 : GammaChkDW 3196 := by decide +kernel
theorem wf13_3196 : Erdos634.Draft.S1Band.S1UBChkW 3196 := by decide +kernel
theorem wf14_3196 : RWChkW 3196 := by decide +kernel
theorem wf15_3196 : S5wChkW 3196 := by decide +kernel
theorem cnzFixW_3196 : CNzFixW 3196 :=
  ⟨wf1_3196, wf2_3196, wf3_3196, wf4_3196, wf5_3196, wf6_3196, wf7_3196, wf8_3196, wf9_3196, wf10_3196, ⟨wf11a_3196, wf11b_3196, wf11c_3196⟩, wf12_3196, wf13_3196, wf14_3196, wf15_3196⟩
theorem no_tileCount_W_3196 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 3196 := not_tileCount_of_CNzFixW 3196 cnzFixW_3196

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_3196

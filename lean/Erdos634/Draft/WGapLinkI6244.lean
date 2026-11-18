/-
Draft/WGapLinkI6244.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 6244.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_6244 : NQChkW 6244 := by decide +kernel
theorem wf2_6244 : (EllChk2 6244 ∨ AsqChk 6244) := by decide +kernel
theorem wf3_6244 : NSqChkSq 6244 := by decide +kernel
theorem wf4_6244 : HArithChkSq 6244 := by decide +kernel
theorem wf5_6244 : (6244 % 2 = 1 ∨ (6244 % 2 = 0 ∧ NHSqChkSq 6244)) := by decide +kernel
theorem wf6a_6244 : Pairs60ChkSq 6244 [] := by decide +kernel
theorem wf6b_6244 : Pairs120ChkSq 6244 [] := by decide +kernel
theorem wf6_6244 : LeafEsqS 6244 := Or.inr ⟨by norm_num, wf6a_6244, wf6b_6244⟩
theorem wf7_6244 : (6244 % 4 = 2 ∨ F1ChkParW 6244) := by decide +kernel
theorem wf8_6244 : S2ChkSq 6244 := by decide +kernel
theorem wf9_6244 : S3newChk 6244 := by decide +kernel
theorem wf10_6244 : IsoH9bChkW 6244 := by decide +kernel
theorem wf11a_6244 : NoF2ChkSq 6244 := by decide +kernel
theorem wf11b_6244 : NoF3zChkSq 6244 := by decide +kernel
theorem wf11c_6244 : NoF4zChkSq 6244 := by decide +kernel
theorem wf12_6244 : GammaChkDW 6244 := by decide +kernel
theorem wf13_6244 : Erdos634.Draft.S1Band.S1UBChkW 6244 := by decide +kernel
theorem wf14_6244 : RWChkW 6244 := by decide +kernel
theorem wf15_6244 : S5wChkW 6244 := by decide +kernel
theorem cnzFixW_6244 : CNzFixW 6244 :=
  ⟨wf1_6244, wf2_6244, wf3_6244, wf4_6244, wf5_6244, wf6_6244, wf7_6244, wf8_6244, wf9_6244, wf10_6244, ⟨wf11a_6244, wf11b_6244, wf11c_6244⟩, wf12_6244, wf13_6244, wf14_6244, wf15_6244⟩
theorem no_tileCount_W_6244 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 6244 := not_tileCount_of_CNzFixW 6244 cnzFixW_6244

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_6244

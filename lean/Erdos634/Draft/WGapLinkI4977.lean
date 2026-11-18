/-
Draft/WGapLinkI4977.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 4977.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_4977 : NQChkW 4977 := by decide +kernel
theorem wf2_4977 : (EllChk2 4977 ∨ AsqChk 4977) := by decide +kernel
theorem wf3_4977 : NSqChkSq 4977 := by decide +kernel
theorem wf4_4977 : HArithChkSq 4977 := by decide +kernel
theorem wf5_4977 : (4977 % 2 = 1 ∨ (4977 % 2 = 0 ∧ NHSqChkSq 4977)) := by decide +kernel
theorem wf6a_4977 : Pairs60ChkSq 4977 [] := by decide +kernel
theorem wf6b_4977 : Pairs120ChkSq 4977 [] := by decide +kernel
theorem wf6_4977 : LeafEsqS 4977 := Or.inr ⟨by norm_num, wf6a_4977, wf6b_4977⟩
theorem wf7_4977 : (4977 % 4 = 2 ∨ F1ChkParW 4977) := by decide +kernel
theorem wf8_4977 : S2ChkSq 4977 := by decide +kernel
theorem wf9_4977 : S3newChk 4977 := by decide +kernel
theorem wf10_4977 : IsoH9bChkW 4977 := by decide +kernel
theorem wf11a_4977 : NoF2ChkSq 4977 := by decide +kernel
theorem wf11b_4977 : NoF3zChkSq 4977 := by decide +kernel
theorem wf11c_4977 : NoF4zChkSq 4977 := by decide +kernel
theorem wf12_4977 : GammaChkDW 4977 := by decide +kernel
theorem wf13_4977 : Erdos634.Draft.S1Band.S1UBChkW 4977 := by decide +kernel
theorem wf14_4977 : RWChkW 4977 := by decide +kernel
theorem wf15_4977 : S5wChkW 4977 := by decide +kernel
theorem cnzFixW_4977 : CNzFixW 4977 :=
  ⟨wf1_4977, wf2_4977, wf3_4977, wf4_4977, wf5_4977, wf6_4977, wf7_4977, wf8_4977, wf9_4977, wf10_4977, ⟨wf11a_4977, wf11b_4977, wf11c_4977⟩, wf12_4977, wf13_4977, wf14_4977, wf15_4977⟩
theorem no_tileCount_W_4977 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 4977 := not_tileCount_of_CNzFixW 4977 cnzFixW_4977

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_4977

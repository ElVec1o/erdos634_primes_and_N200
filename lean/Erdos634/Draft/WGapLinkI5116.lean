/-
Draft/WGapLinkI5116.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 5116 5704.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_5116 : NQChkW 5116 := by decide +kernel
theorem wf2_5116 : (EllChk2 5116 ∨ AsqChk 5116) := by decide +kernel
theorem wf3_5116 : NSqChkSq 5116 := by decide +kernel
theorem wf4_5116 : HArithChkSq 5116 := by decide +kernel
theorem wf5_5116 : (5116 % 2 = 1 ∨ (5116 % 2 = 0 ∧ NHSqChkSq 5116)) := by decide +kernel
theorem wf6a_5116 : Pairs60ChkSq 5116 [] := by decide +kernel
theorem wf6b_5116 : Pairs120ChkSq 5116 [] := by decide +kernel
theorem wf6_5116 : LeafEsqS 5116 := Or.inr ⟨by norm_num, wf6a_5116, wf6b_5116⟩
theorem wf7_5116 : (5116 % 4 = 2 ∨ F1ChkParW 5116) := by decide +kernel
theorem wf8_5116 : S2ChkSq 5116 := by decide +kernel
theorem wf9_5116 : S3newChk 5116 := by decide +kernel
theorem wf10_5116 : IsoH9bChkW 5116 := by decide +kernel
theorem wf11a_5116 : NoF2ChkSq 5116 := by decide +kernel
theorem wf11b_5116 : NoF3zChkSq 5116 := by decide +kernel
theorem wf11c_5116 : NoF4zChkSq 5116 := by decide +kernel
theorem wf12_5116 : GammaChkDW 5116 := by decide +kernel
theorem wf13_5116 : Erdos634.Draft.S1Band.S1UBChkW 5116 := by decide +kernel
theorem wf14_5116 : RWChkW 5116 := by decide +kernel
theorem wf15_5116 : S5wChkW 5116 := by decide +kernel
theorem cnzFixW_5116 : CNzFixW 5116 :=
  ⟨wf1_5116, wf2_5116, wf3_5116, wf4_5116, wf5_5116, wf6_5116, wf7_5116, wf8_5116, wf9_5116, wf10_5116, ⟨wf11a_5116, wf11b_5116, wf11c_5116⟩, wf12_5116, wf13_5116, wf14_5116, wf15_5116⟩
theorem no_tileCount_W_5116 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 5116 := not_tileCount_of_CNzFixW 5116 cnzFixW_5116

theorem wf1_5704 : NQChkW 5704 := by decide +kernel
theorem wf2_5704 : (EllChk2 5704 ∨ AsqChk 5704) := by decide +kernel
theorem wf3_5704 : NSqChkSq 5704 := by decide +kernel
theorem wf4_5704 : HArithChkSq 5704 := by decide +kernel
theorem wf5_5704 : (5704 % 2 = 1 ∨ (5704 % 2 = 0 ∧ NHSqChkSq 5704)) := by decide +kernel
theorem wf6a_5704 : Pairs60ChkSq 5704 [] := by decide +kernel
theorem wf6b_5704 : Pairs120ChkSq 5704 [] := by decide +kernel
theorem wf6_5704 : LeafEsqS 5704 := Or.inr ⟨by norm_num, wf6a_5704, wf6b_5704⟩
theorem wf7_5704 : (5704 % 4 = 2 ∨ F1ChkParW 5704) := by decide +kernel
theorem wf8_5704 : S2ChkSq 5704 := by decide +kernel
theorem wf9_5704 : S3newChk 5704 := by decide +kernel
theorem wf10_5704 : IsoH9bChkW 5704 := by decide +kernel
theorem wf11a_5704 : NoF2ChkSq 5704 := by decide +kernel
theorem wf11b_5704 : NoF3zChkSq 5704 := by decide +kernel
theorem wf11c_5704 : NoF4zChkSq 5704 := by decide +kernel
theorem wf12_5704 : GammaChkDW 5704 := by decide +kernel
theorem wf13_5704 : Erdos634.Draft.S1Band.S1UBChkW 5704 := by decide +kernel
theorem wf14_5704 : RWChkW 5704 := by decide +kernel
theorem wf15_5704 : S5wChkW 5704 := by decide +kernel
theorem cnzFixW_5704 : CNzFixW 5704 :=
  ⟨wf1_5704, wf2_5704, wf3_5704, wf4_5704, wf5_5704, wf6_5704, wf7_5704, wf8_5704, wf9_5704, wf10_5704, ⟨wf11a_5704, wf11b_5704, wf11c_5704⟩, wf12_5704, wf13_5704, wf14_5704, wf15_5704⟩
theorem no_tileCount_W_5704 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 5704 := not_tileCount_of_CNzFixW 5704 cnzFixW_5704

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_5116
#print axioms Erdos634.Draft.NSQM.no_tileCount_W_5704

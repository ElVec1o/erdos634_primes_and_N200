/-
Draft/WGapLinkI5048.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 5048.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_5048 : NQChkW 5048 := by decide +kernel
theorem wf2_5048 : (EllChk2 5048 ∨ AsqChk 5048) := by decide +kernel
theorem wf3_5048 : NSqChkSq 5048 := by decide +kernel
theorem wf4_5048 : HArithChkSq 5048 := by decide +kernel
theorem wf5_5048 : (5048 % 2 = 1 ∨ (5048 % 2 = 0 ∧ NHSqChkSq 5048)) := by decide +kernel
theorem wf6a_5048 : Pairs60ChkSq 5048 [] := by decide +kernel
theorem wf6b_5048 : Pairs120ChkSq 5048 [] := by decide +kernel
theorem wf6_5048 : LeafEsqS 5048 := Or.inr ⟨by norm_num, wf6a_5048, wf6b_5048⟩
theorem wf7_5048 : (5048 % 4 = 2 ∨ F1ChkParW 5048) := by decide +kernel
theorem wf8_5048 : S2ChkSq 5048 := by decide +kernel
theorem wf9_5048 : S3newChk 5048 := by decide +kernel
theorem wf10_5048 : IsoH9bChkW 5048 := by decide +kernel
theorem wf11a_5048 : NoF2ChkSq 5048 := by decide +kernel
theorem wf11b_5048 : NoF3zChkSq 5048 := by decide +kernel
theorem wf11c_5048 : NoF4zChkSq 5048 := by decide +kernel
theorem wf12_5048 : GammaChkDW 5048 := by decide +kernel
theorem wf13_5048 : Erdos634.Draft.S1Band.S1UBChkW 5048 := by decide +kernel
theorem wf14_5048 : RWChkW 5048 := by decide +kernel
theorem wf15_5048 : S5wChkW 5048 := by decide +kernel
theorem cnzFixW_5048 : CNzFixW 5048 :=
  ⟨wf1_5048, wf2_5048, wf3_5048, wf4_5048, wf5_5048, wf6_5048, wf7_5048, wf8_5048, wf9_5048, wf10_5048, ⟨wf11a_5048, wf11b_5048, wf11c_5048⟩, wf12_5048, wf13_5048, wf14_5048, wf15_5048⟩
theorem no_tileCount_W_5048 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 5048 := not_tileCount_of_CNzFixW 5048 cnzFixW_5048

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_5048

/-
Draft/WGapLinkI2488.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 2488.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_2488 : NQChkW 2488 := by decide +kernel
theorem wf2_2488 : (EllChk2 2488 ∨ AsqChk 2488) := by decide +kernel
theorem wf3_2488 : NSqChkSq 2488 := by decide +kernel
theorem wf4_2488 : HArithChkSq 2488 := by decide +kernel
theorem wf5_2488 : (2488 % 2 = 1 ∨ (2488 % 2 = 0 ∧ NHSqChkSq 2488)) := by decide +kernel
theorem wf6a_2488 : Pairs60ChkSq 2488 [] := by decide +kernel
theorem wf6b_2488 : Pairs120ChkSq 2488 [] := by decide +kernel
theorem wf6_2488 : LeafEsqS 2488 := Or.inr ⟨by norm_num, wf6a_2488, wf6b_2488⟩
theorem wf7_2488 : (2488 % 4 = 2 ∨ F1ChkParW 2488) := by decide +kernel
theorem wf8_2488 : S2ChkSq 2488 := by decide +kernel
theorem wf9_2488 : S3newChk 2488 := by decide +kernel
theorem wf10_2488 : IsoH9bChkW 2488 := by decide +kernel
theorem wf11a_2488 : NoF2ChkSq 2488 := by decide +kernel
theorem wf11b_2488 : NoF3zChkSq 2488 := by decide +kernel
theorem wf11c_2488 : NoF4zChkSq 2488 := by decide +kernel
theorem wf12_2488 : GammaChkDW 2488 := by decide +kernel
theorem wf13_2488 : Erdos634.Draft.S1Band.S1UBChkW 2488 := by decide +kernel
theorem wf14_2488 : RWChkW 2488 := by decide +kernel
theorem wf15_2488 : S5wChkW 2488 := by decide +kernel
theorem cnzFixW_2488 : CNzFixW 2488 :=
  ⟨wf1_2488, wf2_2488, wf3_2488, wf4_2488, wf5_2488, wf6_2488, wf7_2488, wf8_2488, wf9_2488, wf10_2488, ⟨wf11a_2488, wf11b_2488, wf11c_2488⟩, wf12_2488, wf13_2488, wf14_2488, wf15_2488⟩
theorem no_tileCount_W_2488 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 2488 := not_tileCount_of_CNzFixW 2488 cnzFixW_2488

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_2488

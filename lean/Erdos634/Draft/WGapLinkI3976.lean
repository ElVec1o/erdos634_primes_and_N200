/-
Draft/WGapLinkI3976.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 3976.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_3976 : NQChkW 3976 := by decide +kernel
theorem wf2_3976 : (EllChk2 3976 ∨ AsqChk 3976) := by decide +kernel
theorem wf3_3976 : NSqChkSq 3976 := by decide +kernel
theorem wf4_3976 : HArithChkSq 3976 := by decide +kernel
theorem wf5_3976 : (3976 % 2 = 1 ∨ (3976 % 2 = 0 ∧ NHSqChkSq 3976)) := by decide +kernel
theorem wf6a_3976 : Pairs60ChkSq 3976 [] := by decide +kernel
theorem wf6b_3976 : Pairs120ChkSq 3976 [] := by decide +kernel
theorem wf6_3976 : LeafEsqS 3976 := Or.inr ⟨by norm_num, wf6a_3976, wf6b_3976⟩
theorem wf7_3976 : (3976 % 4 = 2 ∨ F1ChkParW 3976) := by decide +kernel
theorem wf8_3976 : S2ChkSq 3976 := by decide +kernel
theorem wf9_3976 : S3newChk 3976 := by decide +kernel
theorem wf10_3976 : IsoH9bChkW 3976 := by decide +kernel
theorem wf11a_3976 : NoF2ChkSq 3976 := by decide +kernel
theorem wf11b_3976 : NoF3zChkSq 3976 := by decide +kernel
theorem wf11c_3976 : NoF4zChkSq 3976 := by decide +kernel
theorem wf12_3976 : GammaChkDW 3976 := by decide +kernel
theorem wf13_3976 : Erdos634.Draft.S1Band.S1UBChkW 3976 := by decide +kernel
theorem wf14_3976 : RWChkW 3976 := by decide +kernel
theorem wf15_3976 : S5wChkW 3976 := by decide +kernel
theorem cnzFixW_3976 : CNzFixW 3976 :=
  ⟨wf1_3976, wf2_3976, wf3_3976, wf4_3976, wf5_3976, wf6_3976, wf7_3976, wf8_3976, wf9_3976, wf10_3976, ⟨wf11a_3976, wf11b_3976, wf11c_3976⟩, wf12_3976, wf13_3976, wf14_3976, wf15_3976⟩
theorem no_tileCount_W_3976 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 3976 := not_tileCount_of_CNzFixW 3976 cnzFixW_3976

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_3976

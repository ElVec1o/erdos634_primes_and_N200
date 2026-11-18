/-
Draft/WGapLinkI4324.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 4324.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_4324 : NQChkW 4324 := by decide +kernel
theorem wf2_4324 : (EllChk2 4324 ∨ AsqChk 4324) := by decide +kernel
theorem wf3_4324 : NSqChkSq 4324 := by decide +kernel
theorem wf4_4324 : HArithChkSq 4324 := by decide +kernel
theorem wf5_4324 : (4324 % 2 = 1 ∨ (4324 % 2 = 0 ∧ NHSqChkSq 4324)) := by decide +kernel
theorem wf6a_4324 : Pairs60ChkSq 4324 [] := by decide +kernel
theorem wf6b_4324 : Pairs120ChkSq 4324 [] := by decide +kernel
theorem wf6_4324 : LeafEsqS 4324 := Or.inr ⟨by norm_num, wf6a_4324, wf6b_4324⟩
theorem wf7_4324 : (4324 % 4 = 2 ∨ F1ChkParW 4324) := by decide +kernel
theorem wf8_4324 : S2ChkSq 4324 := by decide +kernel
theorem wf9_4324 : S3newChk 4324 := by decide +kernel
theorem wf10_4324 : IsoH9bChkW 4324 := by decide +kernel
theorem wf11a_4324 : NoF2ChkSq 4324 := by decide +kernel
theorem wf11b_4324 : NoF3zChkSq 4324 := by decide +kernel
theorem wf11c_4324 : NoF4zChkSq 4324 := by decide +kernel
theorem wf12_4324 : GammaChkDW 4324 := by decide +kernel
theorem wf13_4324 : Erdos634.Draft.S1Band.S1UBChkW 4324 := by decide +kernel
theorem wf14_4324 : RWChkW 4324 := by decide +kernel
theorem wf15_4324 : S5wChkW 4324 := by decide +kernel
theorem cnzFixW_4324 : CNzFixW 4324 :=
  ⟨wf1_4324, wf2_4324, wf3_4324, wf4_4324, wf5_4324, wf6_4324, wf7_4324, wf8_4324, wf9_4324, wf10_4324, ⟨wf11a_4324, wf11b_4324, wf11c_4324⟩, wf12_4324, wf13_4324, wf14_4324, wf15_4324⟩
theorem no_tileCount_W_4324 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 4324 := not_tileCount_of_CNzFixW 4324 cnzFixW_4324

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_4324

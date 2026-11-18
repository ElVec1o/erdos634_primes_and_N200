/-
Draft/WGapLinkI5372.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 5372.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_5372 : NQChkW 5372 := by decide +kernel
theorem wf2_5372 : (EllChk2 5372 ∨ AsqChk 5372) := by decide +kernel
theorem wf3_5372 : NSqChkSq 5372 := by decide +kernel
theorem wf4_5372 : HArithChkSq 5372 := by decide +kernel
theorem wf5_5372 : (5372 % 2 = 1 ∨ (5372 % 2 = 0 ∧ NHSqChkSq 5372)) := by decide +kernel
theorem wf6a_5372 : Pairs60ChkSq 5372 [] := by decide +kernel
theorem wf6b_5372 : Pairs120ChkSq 5372 [] := by decide +kernel
theorem wf6_5372 : LeafEsqS 5372 := Or.inr ⟨by norm_num, wf6a_5372, wf6b_5372⟩
theorem wf7_5372 : (5372 % 4 = 2 ∨ F1ChkParW 5372) := by decide +kernel
theorem wf8_5372 : S2ChkSq 5372 := by decide +kernel
theorem wf9_5372 : S3newChk 5372 := by decide +kernel
theorem wf10_5372 : IsoH9bChkW 5372 := by decide +kernel
theorem wf11a_5372 : NoF2ChkSq 5372 := by decide +kernel
theorem wf11b_5372 : NoF3zChkSq 5372 := by decide +kernel
theorem wf11c_5372 : NoF4zChkSq 5372 := by decide +kernel
theorem wf12_5372 : GammaChkDW 5372 := by decide +kernel
theorem wf13_5372 : Erdos634.Draft.S1Band.S1UBChkW 5372 := by decide +kernel
theorem wf14_5372 : RWChkW 5372 := by decide +kernel
theorem wf15_5372 : S5wChkW 5372 := by decide +kernel
theorem cnzFixW_5372 : CNzFixW 5372 :=
  ⟨wf1_5372, wf2_5372, wf3_5372, wf4_5372, wf5_5372, wf6_5372, wf7_5372, wf8_5372, wf9_5372, wf10_5372, ⟨wf11a_5372, wf11b_5372, wf11c_5372⟩, wf12_5372, wf13_5372, wf14_5372, wf15_5372⟩
theorem no_tileCount_W_5372 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 5372 := not_tileCount_of_CNzFixW 5372 cnzFixW_5372

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_5372

/-
Draft/WGapLinkI5432.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 5432.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_5432 : NQChkW 5432 := by decide +kernel
theorem wf2_5432 : (EllChk2 5432 ∨ AsqChk 5432) := by decide +kernel
theorem wf3_5432 : NSqChkSq 5432 := by decide +kernel
theorem wf4_5432 : HArithChkSq 5432 := by decide +kernel
theorem wf5_5432 : (5432 % 2 = 1 ∨ (5432 % 2 = 0 ∧ NHSqChkSq 5432)) := by decide +kernel
theorem wf6a_5432 : Pairs60ChkSq 5432 [] := by decide +kernel
theorem wf6b_5432 : Pairs120ChkSq 5432 [] := by decide +kernel
theorem wf6_5432 : LeafEsqS 5432 := Or.inr ⟨by norm_num, wf6a_5432, wf6b_5432⟩
theorem wf7_5432 : (5432 % 4 = 2 ∨ F1ChkParW 5432) := by decide +kernel
theorem wf8_5432 : S2ChkSq 5432 := by decide +kernel
theorem wf9_5432 : S3newChk 5432 := by decide +kernel
theorem wf10_5432 : IsoH9bChkW 5432 := by decide +kernel
theorem wf11a_5432 : NoF2ChkSq 5432 := by decide +kernel
theorem wf11b_5432 : NoF3zChkSq 5432 := by decide +kernel
theorem wf11c_5432 : NoF4zChkSq 5432 := by decide +kernel
theorem wf12_5432 : GammaChkDW 5432 := by decide +kernel
theorem wf13_5432 : Erdos634.Draft.S1Band.S1UBChkW 5432 := by decide +kernel
theorem wf14_5432 : RWChkW 5432 := by decide +kernel
theorem wf15_5432 : S5wChkW 5432 := by decide +kernel
theorem cnzFixW_5432 : CNzFixW 5432 :=
  ⟨wf1_5432, wf2_5432, wf3_5432, wf4_5432, wf5_5432, wf6_5432, wf7_5432, wf8_5432, wf9_5432, wf10_5432, ⟨wf11a_5432, wf11b_5432, wf11c_5432⟩, wf12_5432, wf13_5432, wf14_5432, wf15_5432⟩
theorem no_tileCount_W_5432 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 5432 := not_tileCount_of_CNzFixW 5432 cnzFixW_5432

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_5432

/-
Draft/WGapLinkI4676.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 4676.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_4676 : NQChkW 4676 := by decide +kernel
theorem wf2_4676 : (EllChk2 4676 ∨ AsqChk 4676) := by decide +kernel
theorem wf3_4676 : NSqChkSq 4676 := by decide +kernel
theorem wf4_4676 : HArithChkSq 4676 := by decide +kernel
theorem wf5_4676 : (4676 % 2 = 1 ∨ (4676 % 2 = 0 ∧ NHSqChkSq 4676)) := by decide +kernel
theorem wf6a_4676 : Pairs60ChkSq 4676 [] := by decide +kernel
theorem wf6b_4676 : Pairs120ChkSq 4676 [] := by decide +kernel
theorem wf6_4676 : LeafEsqS 4676 := Or.inr ⟨by norm_num, wf6a_4676, wf6b_4676⟩
theorem wf7_4676 : (4676 % 4 = 2 ∨ F1ChkParW 4676) := by decide +kernel
theorem wf8_4676 : S2ChkSq 4676 := by decide +kernel
theorem wf9_4676 : S3newChk 4676 := by decide +kernel
theorem wf10_4676 : IsoH9bChkW 4676 := by decide +kernel
theorem wf11a_4676 : NoF2ChkSq 4676 := by decide +kernel
theorem wf11b_4676 : NoF3zChkSq 4676 := by decide +kernel
theorem wf11c_4676 : NoF4zChkSq 4676 := by decide +kernel
theorem wf12_4676 : GammaChkDW 4676 := by decide +kernel
theorem wf13_4676 : Erdos634.Draft.S1Band.S1UBChkW 4676 := by decide +kernel
theorem wf14_4676 : RWChkW 4676 := by decide +kernel
theorem wf15_4676 : S5wChkW 4676 := by decide +kernel
theorem cnzFixW_4676 : CNzFixW 4676 :=
  ⟨wf1_4676, wf2_4676, wf3_4676, wf4_4676, wf5_4676, wf6_4676, wf7_4676, wf8_4676, wf9_4676, wf10_4676, ⟨wf11a_4676, wf11b_4676, wf11c_4676⟩, wf12_4676, wf13_4676, wf14_4676, wf15_4676⟩
theorem no_tileCount_W_4676 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 4676 := not_tileCount_of_CNzFixW 4676 cnzFixW_4676

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_4676

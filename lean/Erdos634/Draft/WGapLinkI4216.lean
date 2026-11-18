/-
Draft/WGapLinkI4216.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 4216.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_4216 : NQChkW 4216 := by decide +kernel
theorem wf2_4216 : (EllChk2 4216 ∨ AsqChk 4216) := by decide +kernel
theorem wf3_4216 : NSqChkSq 4216 := by decide +kernel
theorem wf4_4216 : HArithChkSq 4216 := by decide +kernel
theorem wf5_4216 : (4216 % 2 = 1 ∨ (4216 % 2 = 0 ∧ NHSqChkSq 4216)) := by decide +kernel
theorem wf6a_4216 : Pairs60ChkSq 4216 [] := by decide +kernel
theorem wf6b_4216 : Pairs120ChkSq 4216 [] := by decide +kernel
theorem wf6_4216 : LeafEsqS 4216 := Or.inr ⟨by norm_num, wf6a_4216, wf6b_4216⟩
theorem wf7_4216 : (4216 % 4 = 2 ∨ F1ChkParW 4216) := by decide +kernel
theorem wf8_4216 : S2ChkSq 4216 := by decide +kernel
theorem wf9_4216 : S3newChk 4216 := by decide +kernel
theorem wf10_4216 : IsoH9bChkW 4216 := by decide +kernel
theorem wf11a_4216 : NoF2ChkSq 4216 := by decide +kernel
theorem wf11b_4216 : NoF3zChkSq 4216 := by decide +kernel
theorem wf11c_4216 : NoF4zChkSq 4216 := by decide +kernel
theorem wf12_4216 : GammaChkDW 4216 := by decide +kernel
theorem wf13_4216 : Erdos634.Draft.S1Band.S1UBChkW 4216 := by decide +kernel
theorem wf14_4216 : RWChkW 4216 := by decide +kernel
theorem wf15_4216 : S5wChkW 4216 := by decide +kernel
theorem cnzFixW_4216 : CNzFixW 4216 :=
  ⟨wf1_4216, wf2_4216, wf3_4216, wf4_4216, wf5_4216, wf6_4216, wf7_4216, wf8_4216, wf9_4216, wf10_4216, ⟨wf11a_4216, wf11b_4216, wf11c_4216⟩, wf12_4216, wf13_4216, wf14_4216, wf15_4216⟩
theorem no_tileCount_W_4216 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 4216 := not_tileCount_of_CNzFixW 4216 cnzFixW_4216

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_4216

/-
Draft/WGapLinkI2716.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 2716.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_2716 : NQChkW 2716 := by decide +kernel
theorem wf2_2716 : (EllChk2 2716 ∨ AsqChk 2716) := by decide +kernel
theorem wf3_2716 : NSqChkSq 2716 := by decide +kernel
theorem wf4_2716 : HArithChkSq 2716 := by decide +kernel
theorem wf5_2716 : (2716 % 2 = 1 ∨ (2716 % 2 = 0 ∧ NHSqChkSq 2716)) := by decide +kernel
theorem wf6a_2716 : Pairs60ChkSq 2716 [] := by decide +kernel
theorem wf6b_2716 : Pairs120ChkSq 2716 [] := by decide +kernel
theorem wf6_2716 : LeafEsqS 2716 := Or.inr ⟨by norm_num, wf6a_2716, wf6b_2716⟩
theorem wf7_2716 : (2716 % 4 = 2 ∨ F1ChkParW 2716) := by decide +kernel
theorem wf8_2716 : S2ChkSq 2716 := by decide +kernel
theorem wf9_2716 : S3newChk 2716 := by decide +kernel
theorem wf10_2716 : IsoH9bChkW 2716 := by decide +kernel
theorem wf11a_2716 : NoF2ChkSq 2716 := by decide +kernel
theorem wf11b_2716 : NoF3zChkSq 2716 := by decide +kernel
theorem wf11c_2716 : NoF4zChkSq 2716 := by decide +kernel
theorem wf12_2716 : GammaChkDW 2716 := by decide +kernel
theorem wf13_2716 : Erdos634.Draft.S1Band.S1UBChkW 2716 := by decide +kernel
theorem wf14_2716 : RWChkW 2716 := by decide +kernel
theorem wf15_2716 : S5wChkW 2716 := by decide +kernel
theorem cnzFixW_2716 : CNzFixW 2716 :=
  ⟨wf1_2716, wf2_2716, wf3_2716, wf4_2716, wf5_2716, wf6_2716, wf7_2716, wf8_2716, wf9_2716, wf10_2716, ⟨wf11a_2716, wf11b_2716, wf11c_2716⟩, wf12_2716, wf13_2716, wf14_2716, wf15_2716⟩
theorem no_tileCount_W_2716 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 2716 := not_tileCount_of_CNzFixW 2716 cnzFixW_2716

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_2716

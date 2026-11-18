/-
Draft/WGapLinkI8504.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 8504.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_8504 : NQChkW 8504 := by decide +kernel
theorem wf2_8504 : (EllChk2 8504 ∨ AsqChk 8504) := by decide +kernel
theorem wf3_8504 : NSqChkSq 8504 := by decide +kernel
theorem wf4_8504 : HArithChkSq 8504 := by decide +kernel
theorem wf5_8504 : (8504 % 2 = 1 ∨ (8504 % 2 = 0 ∧ NHSqChkSq 8504)) := by decide +kernel
theorem wf6a_8504 : Pairs60ChkSq 8504 [] := by decide +kernel
theorem wf6b_8504 : Pairs120ChkSq 8504 [] := by decide +kernel
theorem wf6_8504 : LeafEsqS 8504 := Or.inr ⟨by norm_num, wf6a_8504, wf6b_8504⟩
theorem wf7_8504 : (8504 % 4 = 2 ∨ F1ChkParW 8504) := by decide +kernel
theorem wf8_8504 : S2ChkSq 8504 := by decide +kernel
theorem wf9_8504 : S3newChk 8504 := by decide +kernel
theorem wf10_8504 : IsoH9bChkW 8504 := by decide +kernel
theorem wf11a_8504 : NoF2ChkSq 8504 := by decide +kernel
theorem wf11b_8504 : NoF3zChkSq 8504 := by decide +kernel
theorem wf11c_8504 : NoF4zChkSq 8504 := by decide +kernel
theorem wf12_8504 : GammaChkDW 8504 := by decide +kernel
theorem wf13_8504 : Erdos634.Draft.S1Band.S1UBChkW 8504 := by decide +kernel
theorem wf14_8504 : RWChkW 8504 := by decide +kernel
theorem wf15_8504 : S5wChkW 8504 := by decide +kernel
theorem cnzFixW_8504 : CNzFixW 8504 :=
  ⟨wf1_8504, wf2_8504, wf3_8504, wf4_8504, wf5_8504, wf6_8504, wf7_8504, wf8_8504, wf9_8504, wf10_8504, ⟨wf11a_8504, wf11b_8504, wf11c_8504⟩, wf12_8504, wf13_8504, wf14_8504, wf15_8504⟩
theorem no_tileCount_W_8504 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 8504 := not_tileCount_of_CNzFixW 8504 cnzFixW_8504

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_8504

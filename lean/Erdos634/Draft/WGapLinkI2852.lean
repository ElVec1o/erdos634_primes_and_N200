/-
Draft/WGapLinkI2852.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 2852.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_2852 : NQChkW 2852 := by decide +kernel
theorem wf2_2852 : (EllChk2 2852 ∨ AsqChk 2852) := by decide +kernel
theorem wf3_2852 : NSqChkSq 2852 := by decide +kernel
theorem wf4_2852 : HArithChkSq 2852 := by decide +kernel
theorem wf5_2852 : (2852 % 2 = 1 ∨ (2852 % 2 = 0 ∧ NHSqChkSq 2852)) := by decide +kernel
theorem wf6a_2852 : Pairs60ChkSq 2852 [] := by decide +kernel
theorem wf6b_2852 : Pairs120ChkSq 2852 [] := by decide +kernel
theorem wf6_2852 : LeafEsqS 2852 := Or.inr ⟨by norm_num, wf6a_2852, wf6b_2852⟩
theorem wf7_2852 : (2852 % 4 = 2 ∨ F1ChkParW 2852) := by decide +kernel
theorem wf8_2852 : S2ChkSq 2852 := by decide +kernel
theorem wf9_2852 : S3newChk 2852 := by decide +kernel
theorem wf10_2852 : IsoH9bChkW 2852 := by decide +kernel
theorem wf11a_2852 : NoF2ChkSq 2852 := by decide +kernel
theorem wf11b_2852 : NoF3zChkSq 2852 := by decide +kernel
theorem wf11c_2852 : NoF4zChkSq 2852 := by decide +kernel
theorem wf12_2852 : GammaChkDW 2852 := by decide +kernel
theorem wf13_2852 : Erdos634.Draft.S1Band.S1UBChkW 2852 := by decide +kernel
theorem wf14_2852 : RWChkW 2852 := by decide +kernel
theorem wf15_2852 : S5wChkW 2852 := by decide +kernel
theorem cnzFixW_2852 : CNzFixW 2852 :=
  ⟨wf1_2852, wf2_2852, wf3_2852, wf4_2852, wf5_2852, wf6_2852, wf7_2852, wf8_2852, wf9_2852, wf10_2852, ⟨wf11a_2852, wf11b_2852, wf11c_2852⟩, wf12_2852, wf13_2852, wf14_2852, wf15_2852⟩
theorem no_tileCount_W_2852 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 2852 := not_tileCount_of_CNzFixW 2852 cnzFixW_2852

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_2852

/-
Draft/WGapLinkI3906.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 3906.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_3906 : NQChkW 3906 := by decide +kernel
theorem wf2_3906 : (EllChk2 3906 ∨ AsqChk 3906) := by decide +kernel
theorem wf3_3906 : NSqChkSq 3906 := by decide +kernel
theorem wf4_3906 : HArithChkSq 3906 := by decide +kernel
theorem wf5_3906 : (3906 % 2 = 1 ∨ (3906 % 2 = 0 ∧ NHSqChkSq 3906)) := by decide +kernel
theorem wf6_3906 : LeafEsqS 3906 := Or.inl (by norm_num)
theorem wf7_3906 : (3906 % 4 = 2 ∨ F1ChkParW 3906) := by decide +kernel
theorem wf8_3906 : S2ChkSq 3906 := by decide +kernel
theorem wf9_3906 : S3newChk 3906 := by decide +kernel
theorem wf10_3906 : IsoH9bChkW 3906 := by decide +kernel
theorem wf11a_3906 : NoF2ChkSq 3906 := by decide +kernel
theorem wf11b_3906 : NoF3zChkSq 3906 := by decide +kernel
theorem wf11c_3906 : NoF4zChkSq 3906 := by decide +kernel
theorem wf12_3906 : GammaChkDW 3906 := by decide +kernel
theorem wf13_3906 : Erdos634.Draft.S1Band.S1UBChkW 3906 := by decide +kernel
theorem wf14_3906 : RWChkW 3906 := by decide +kernel
theorem wf15_3906 : S5wChkW 3906 := by decide +kernel
theorem cnzFixW_3906 : CNzFixW 3906 :=
  ⟨wf1_3906, wf2_3906, wf3_3906, wf4_3906, wf5_3906, wf6_3906, wf7_3906, wf8_3906, wf9_3906, wf10_3906, ⟨wf11a_3906, wf11b_3906, wf11c_3906⟩, wf12_3906, wf13_3906, wf14_3906, wf15_3906⟩
theorem no_tileCount_W_3906 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 3906 := not_tileCount_of_CNzFixW 3906 cnzFixW_3906

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_3906

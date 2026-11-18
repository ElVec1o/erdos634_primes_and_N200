/-
Draft/WGapLink3.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the 15 conjuncts of CNzFixW N are decided in separate decide +kernel declarations, then not TileCount N.  Values: 824.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_824 : NQChkW 824 := by decide +kernel
theorem wf2_824 : (EllChk2 824 ∨ AsqChk 824) := by decide +kernel
theorem wf3_824 : NSqChkSq 824 := by decide +kernel
theorem wf4_824 : HArithChkSq 824 := by decide +kernel
theorem wf5_824 : (824 % 2 = 1 ∨ (824 % 2 = 0 ∧ NHSqChkSq 824)) := by decide +kernel
theorem wf6_824 : LeafEsqS 824 := by decide +kernel
theorem wf7_824 : (824 % 4 = 2 ∨ F1ChkParW 824) := by decide +kernel
theorem wf8_824 : S2ChkSq 824 := by decide +kernel
theorem wf9_824 : S3newChk 824 := by decide +kernel
theorem wf10_824 : IsoH9bChkW 824 := by decide +kernel
theorem wf11_824 : (NoF2ChkSq 824 ∧ NoF3zChkSq 824 ∧ NoF4zChkSq 824) := by decide +kernel
theorem wf12_824 : GammaChkDW 824 := by decide +kernel
theorem wf13_824 : Erdos634.Draft.S1Band.S1UBChkW 824 := by decide +kernel
theorem wf14_824 : RWChkW 824 := by decide +kernel
theorem wf15_824 : S5wChkW 824 := by decide +kernel
theorem cnzFixW_824 : CNzFixW 824 :=
  ⟨wf1_824, wf2_824, wf3_824, wf4_824, wf5_824, wf6_824, wf7_824, wf8_824, wf9_824, wf10_824, wf11_824, wf12_824, wf13_824, wf14_824, wf15_824⟩
theorem no_tileCount_W_824 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 824 := not_tileCount_of_CNzFixW 824 cnzFixW_824

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_824

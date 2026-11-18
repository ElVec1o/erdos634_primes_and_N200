/-
Draft/WGapLinkI3519.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 3519.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_3519 : NQChkW 3519 := by decide +kernel
theorem wf2_3519 : (EllChk2 3519 ∨ AsqChk 3519) := by decide +kernel
theorem wf3_3519 : NSqChkSq 3519 := by decide +kernel
theorem wf4_3519 : HArithChkSq 3519 := by decide +kernel
theorem wf5_3519 : (3519 % 2 = 1 ∨ (3519 % 2 = 0 ∧ NHSqChkSq 3519)) := by decide +kernel
theorem wf6a_3519 : Pairs60ChkSq 3519 [] := by decide +kernel
theorem wf6b_3519 : Pairs120ChkSq 3519 [] := by decide +kernel
theorem wf6_3519 : LeafEsqS 3519 := Or.inr ⟨by norm_num, wf6a_3519, wf6b_3519⟩
theorem wf7_3519 : (3519 % 4 = 2 ∨ F1ChkParW 3519) := by decide +kernel
theorem wf8_3519 : S2ChkSq 3519 := by decide +kernel
theorem wf9_3519 : S3newChk 3519 := by decide +kernel
theorem wf10_3519 : IsoH9bChkW 3519 := by decide +kernel
theorem wf11a_3519 : NoF2ChkSq 3519 := by decide +kernel
theorem wf11b_3519 : NoF3zChkSq 3519 := by decide +kernel
theorem wf11c_3519 : NoF4zChkSq 3519 := by decide +kernel
theorem wf12_3519 : GammaChkDW 3519 := by decide +kernel
theorem wf13_3519 : Erdos634.Draft.S1Band.S1UBChkW 3519 := by decide +kernel
theorem wf14_3519 : RWChkW 3519 := by decide +kernel
theorem wf15_3519 : S5wChkW 3519 := by decide +kernel
theorem cnzFixW_3519 : CNzFixW 3519 :=
  ⟨wf1_3519, wf2_3519, wf3_3519, wf4_3519, wf5_3519, wf6_3519, wf7_3519, wf8_3519, wf9_3519, wf10_3519, ⟨wf11a_3519, wf11b_3519, wf11c_3519⟩, wf12_3519, wf13_3519, wf14_3519, wf15_3519⟩
theorem no_tileCount_W_3519 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 3519 := not_tileCount_of_CNzFixW 3519 cnzFixW_3519

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_3519

/-
Draft/WGapLinkI3808.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 3808.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_3808 : NQChkW 3808 := by decide +kernel
theorem wf2_3808 : (EllChk2 3808 ∨ AsqChk 3808) := by decide +kernel
theorem wf3_3808 : NSqChkSq 3808 := by decide +kernel
theorem wf4_3808 : HArithChkSq 3808 := by decide +kernel
theorem wf5_3808 : (3808 % 2 = 1 ∨ (3808 % 2 = 0 ∧ NHSqChkSq 3808)) := by decide +kernel
theorem wf6a_3808 : Pairs60ChkSq 3808 [] := by decide +kernel
theorem wf6b_3808 : Pairs120ChkSq 3808 [] := by decide +kernel
theorem wf6_3808 : LeafEsqS 3808 := Or.inr ⟨by norm_num, wf6a_3808, wf6b_3808⟩
theorem wf7_3808 : (3808 % 4 = 2 ∨ F1ChkParW 3808) := by decide +kernel
theorem wf8_3808 : S2ChkSq 3808 := by decide +kernel
theorem wf9_3808 : S3newChk 3808 := by decide +kernel
theorem wf10_3808 : IsoH9bChkW 3808 := by decide +kernel
theorem wf11a_3808 : NoF2ChkSq 3808 := by decide +kernel
theorem wf11b_3808 : NoF3zChkSq 3808 := by decide +kernel
theorem wf11c_3808 : NoF4zChkSq 3808 := by decide +kernel
theorem wf12_3808 : GammaChkDW 3808 := by decide +kernel
theorem wf13_3808 : Erdos634.Draft.S1Band.S1UBChkW 3808 := by decide +kernel
theorem wf14_3808 : RWChkW 3808 := by decide +kernel
theorem wf15_3808 : S5wChkW 3808 := by decide +kernel
theorem cnzFixW_3808 : CNzFixW 3808 :=
  ⟨wf1_3808, wf2_3808, wf3_3808, wf4_3808, wf5_3808, wf6_3808, wf7_3808, wf8_3808, wf9_3808, wf10_3808, ⟨wf11a_3808, wf11b_3808, wf11c_3808⟩, wf12_3808, wf13_3808, wf14_3808, wf15_3808⟩
theorem no_tileCount_W_3808 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 3808 := not_tileCount_of_CNzFixW 3808 cnzFixW_3808

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_3808

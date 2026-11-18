/-
Draft/WGapLinkI3448.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the conjuncts of CNzFixW N are decided in separate decide +kernel declarations (E and NoF split in parts), then not TileCount N.  Values: 3448.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.E120Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_3448 : NQChkW 3448 := by decide +kernel
theorem wf2_3448 : (EllChk2 3448 ∨ AsqChk 3448) := by decide +kernel
theorem wf3_3448 : NSqChkSq 3448 := by decide +kernel
theorem wf4_3448 : HArithChkSq 3448 := by decide +kernel
theorem wf5_3448 : (3448 % 2 = 1 ∨ (3448 % 2 = 0 ∧ NHSqChkSq 3448)) := by decide +kernel
theorem wf6a_3448 : Pairs60ChkSq 3448 [] := by decide +kernel
theorem wf6b_3448 : Pairs120ChkSq 3448 [] := by decide +kernel
theorem wf6_3448 : LeafEsqS 3448 := Or.inr ⟨by norm_num, wf6a_3448, wf6b_3448⟩
theorem wf7_3448 : (3448 % 4 = 2 ∨ F1ChkParW 3448) := by decide +kernel
theorem wf8_3448 : S2ChkSq 3448 := by decide +kernel
theorem wf9_3448 : S3newChk 3448 := by decide +kernel
theorem wf10_3448 : IsoH9bChkW 3448 := by decide +kernel
theorem wf11a_3448 : NoF2ChkSq 3448 := by decide +kernel
theorem wf11b_3448 : NoF3zChkSq 3448 := by decide +kernel
theorem wf11c_3448 : NoF4zChkSq 3448 := by decide +kernel
theorem wf12_3448 : GammaChkDW 3448 := by decide +kernel
theorem wf13_3448 : Erdos634.Draft.S1Band.S1UBChkW 3448 := by decide +kernel
theorem wf14_3448 : RWChkW 3448 := by decide +kernel
theorem wf15_3448 : S5wChkW 3448 := by decide +kernel
theorem cnzFixW_3448 : CNzFixW 3448 :=
  ⟨wf1_3448, wf2_3448, wf3_3448, wf4_3448, wf5_3448, wf6_3448, wf7_3448, wf8_3448, wf9_3448, wf10_3448, ⟨wf11a_3448, wf11b_3448, wf11c_3448⟩, wf12_3448, wf13_3448, wf14_3448, wf15_3448⟩
theorem no_tileCount_W_3448 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 3448 := not_tileCount_of_CNzFixW 3448 cnzFixW_3448

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_3448

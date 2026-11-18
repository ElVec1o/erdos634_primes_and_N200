/-
Draft/WGapLink4.lean -- 16 November 2026 (work item internal working notes).  Per-N kernel instances of NSQM.not_tileCount_of_CNzFixW (WGapLink2):
for each N the 15 conjuncts of CNzFixW N are decided in separate decide +kernel declarations, then not TileCount N.  Values: 956 1359 1724 1912.
UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

theorem wf1_956 : NQChkW 956 := by decide +kernel
theorem wf2_956 : (EllChk2 956 ∨ AsqChk 956) := by decide +kernel
theorem wf3_956 : NSqChkSq 956 := by decide +kernel
theorem wf4_956 : HArithChkSq 956 := by decide +kernel
theorem wf5_956 : (956 % 2 = 1 ∨ (956 % 2 = 0 ∧ NHSqChkSq 956)) := by decide +kernel
theorem wf6_956 : LeafEsqS 956 := by decide +kernel
theorem wf7_956 : (956 % 4 = 2 ∨ F1ChkParW 956) := by decide +kernel
theorem wf8_956 : S2ChkSq 956 := by decide +kernel
theorem wf9_956 : S3newChk 956 := by decide +kernel
theorem wf10_956 : IsoH9bChkW 956 := by decide +kernel
theorem wf11_956 : (NoF2ChkSq 956 ∧ NoF3zChkSq 956 ∧ NoF4zChkSq 956) := by decide +kernel
theorem wf12_956 : GammaChkDW 956 := by decide +kernel
theorem wf13_956 : Erdos634.Draft.S1Band.S1UBChkW 956 := by decide +kernel
theorem wf14_956 : RWChkW 956 := by decide +kernel
theorem wf15_956 : S5wChkW 956 := by decide +kernel
theorem cnzFixW_956 : CNzFixW 956 :=
  ⟨wf1_956, wf2_956, wf3_956, wf4_956, wf5_956, wf6_956, wf7_956, wf8_956, wf9_956, wf10_956, wf11_956, wf12_956, wf13_956, wf14_956, wf15_956⟩
theorem no_tileCount_W_956 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 956 := not_tileCount_of_CNzFixW 956 cnzFixW_956

theorem wf1_1359 : NQChkW 1359 := by decide +kernel
theorem wf2_1359 : (EllChk2 1359 ∨ AsqChk 1359) := by decide +kernel
theorem wf3_1359 : NSqChkSq 1359 := by decide +kernel
theorem wf4_1359 : HArithChkSq 1359 := by decide +kernel
theorem wf5_1359 : (1359 % 2 = 1 ∨ (1359 % 2 = 0 ∧ NHSqChkSq 1359)) := by decide +kernel
theorem wf6_1359 : LeafEsqS 1359 := by decide +kernel
theorem wf7_1359 : (1359 % 4 = 2 ∨ F1ChkParW 1359) := by decide +kernel
theorem wf8_1359 : S2ChkSq 1359 := by decide +kernel
theorem wf9_1359 : S3newChk 1359 := by decide +kernel
theorem wf10_1359 : IsoH9bChkW 1359 := by decide +kernel
theorem wf11_1359 : (NoF2ChkSq 1359 ∧ NoF3zChkSq 1359 ∧ NoF4zChkSq 1359) := by decide +kernel
theorem wf12_1359 : GammaChkDW 1359 := by decide +kernel
theorem wf13_1359 : Erdos634.Draft.S1Band.S1UBChkW 1359 := by decide +kernel
theorem wf14_1359 : RWChkW 1359 := by decide +kernel
theorem wf15_1359 : S5wChkW 1359 := by decide +kernel
theorem cnzFixW_1359 : CNzFixW 1359 :=
  ⟨wf1_1359, wf2_1359, wf3_1359, wf4_1359, wf5_1359, wf6_1359, wf7_1359, wf8_1359, wf9_1359, wf10_1359, wf11_1359, wf12_1359, wf13_1359, wf14_1359, wf15_1359⟩
theorem no_tileCount_W_1359 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 1359 := not_tileCount_of_CNzFixW 1359 cnzFixW_1359

theorem wf1_1724 : NQChkW 1724 := by decide +kernel
theorem wf2_1724 : (EllChk2 1724 ∨ AsqChk 1724) := by decide +kernel
theorem wf3_1724 : NSqChkSq 1724 := by decide +kernel
theorem wf4_1724 : HArithChkSq 1724 := by decide +kernel
theorem wf5_1724 : (1724 % 2 = 1 ∨ (1724 % 2 = 0 ∧ NHSqChkSq 1724)) := by decide +kernel
theorem wf6_1724 : LeafEsqS 1724 := by decide +kernel
theorem wf7_1724 : (1724 % 4 = 2 ∨ F1ChkParW 1724) := by decide +kernel
theorem wf8_1724 : S2ChkSq 1724 := by decide +kernel
theorem wf9_1724 : S3newChk 1724 := by decide +kernel
theorem wf10_1724 : IsoH9bChkW 1724 := by decide +kernel
theorem wf11_1724 : (NoF2ChkSq 1724 ∧ NoF3zChkSq 1724 ∧ NoF4zChkSq 1724) := by decide +kernel
theorem wf12_1724 : GammaChkDW 1724 := by decide +kernel
theorem wf13_1724 : Erdos634.Draft.S1Band.S1UBChkW 1724 := by decide +kernel
theorem wf14_1724 : RWChkW 1724 := by decide +kernel
theorem wf15_1724 : S5wChkW 1724 := by decide +kernel
theorem cnzFixW_1724 : CNzFixW 1724 :=
  ⟨wf1_1724, wf2_1724, wf3_1724, wf4_1724, wf5_1724, wf6_1724, wf7_1724, wf8_1724, wf9_1724, wf10_1724, wf11_1724, wf12_1724, wf13_1724, wf14_1724, wf15_1724⟩
theorem no_tileCount_W_1724 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 1724 := not_tileCount_of_CNzFixW 1724 cnzFixW_1724

theorem wf1_1912 : NQChkW 1912 := by decide +kernel
theorem wf2_1912 : (EllChk2 1912 ∨ AsqChk 1912) := by decide +kernel
theorem wf3_1912 : NSqChkSq 1912 := by decide +kernel
theorem wf4_1912 : HArithChkSq 1912 := by decide +kernel
theorem wf5_1912 : (1912 % 2 = 1 ∨ (1912 % 2 = 0 ∧ NHSqChkSq 1912)) := by decide +kernel
theorem wf6_1912 : LeafEsqS 1912 := by decide +kernel
theorem wf7_1912 : (1912 % 4 = 2 ∨ F1ChkParW 1912) := by decide +kernel
theorem wf8_1912 : S2ChkSq 1912 := by decide +kernel
theorem wf9_1912 : S3newChk 1912 := by decide +kernel
theorem wf10_1912 : IsoH9bChkW 1912 := by decide +kernel
theorem wf11_1912 : (NoF2ChkSq 1912 ∧ NoF3zChkSq 1912 ∧ NoF4zChkSq 1912) := by decide +kernel
theorem wf12_1912 : GammaChkDW 1912 := by decide +kernel
theorem wf13_1912 : Erdos634.Draft.S1Band.S1UBChkW 1912 := by decide +kernel
theorem wf14_1912 : RWChkW 1912 := by decide +kernel
theorem wf15_1912 : S5wChkW 1912 := by decide +kernel
theorem cnzFixW_1912 : CNzFixW 1912 :=
  ⟨wf1_1912, wf2_1912, wf3_1912, wf4_1912, wf5_1912, wf6_1912, wf7_1912, wf8_1912, wf9_1912, wf10_1912, wf11_1912, wf12_1912, wf13_1912, wf14_1912, wf15_1912⟩
theorem no_tileCount_W_1912 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 1912 := not_tileCount_of_CNzFixW 1912 cnzFixW_1912

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.no_tileCount_W_956
#print axioms Erdos634.Draft.NSQM.no_tileCount_W_1359
#print axioms Erdos634.Draft.NSQM.no_tileCount_W_1724
#print axioms Erdos634.Draft.NSQM.no_tileCount_W_1912

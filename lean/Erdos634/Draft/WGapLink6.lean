/-
Draft/WGapLink6.lean -- 16 November 2026 (work item internal working notes).  NON-VACUITY CONTROLS for `NSQM.CNzFixW` (WGapLink2).  UNAUDITED beyond internal checks.
Leaf module, imported by no aggregate.  No sorry, no native_decide.
(a) the three Lean `WTilable` instances of WGapRung6b, N = M^2 (2 f^2 - e^2): (2,3,3) -> 126, (6,11,11) -> 24926, (6,11,17) -> 59534
    (numbers recomputed by `norm_num` below).  For each: `TileCount N` from the Lean tiling, hence `not CNzFixW N` by `not_tileCount_of_CNzFixW`
    (the theorem rejects its own hypothesis), AND, by kernel evaluation, the failing conjunct itself: `not RWChkW N`.
(b) five other tile counts from the Lean `TileCount` literals: 143 (N143.lean), 189 (Spectrum200d.lean), 345 (N345N506.lean), 1648 (TW1648.lean, a W tiling (5,8,4)),
    4450 (TW4450.lean, a W tiling (8,11,5)): `not CNzFixW N` by the failing conjunct, kernel-decided; where cheap also from the Lean literal.
-/
import Erdos634.Draft.WGapLink2
import Erdos634.Draft.WGapRung6b

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.E60Irr Erdos634.Draft.NSQMain Erdos634.Draft.LeafFix

-- arithmetic of the three instances
example : (2 * 3 ^ 2 - 2 ^ 2) * 3 ^ 2 = 126 := by norm_num
example : (2 * 11 ^ 2 - 6 ^ 2) * 11 ^ 2 = 24926 := by norm_num
example : (2 * 11 ^ 2 - 6 ^ 2) * 17 ^ 2 = 59534 := by norm_num

theorem tileCount_126 : Erdos634.Draft.TileCountFamilies.TileCount 126 := by
  obtain ⟨D, -, -⟩ := Erdos634.Draft.WGapRung.wt_2_3_3
  exact ⟨D⟩
theorem tileCount_24926 : Erdos634.Draft.TileCountFamilies.TileCount 24926 := by
  obtain ⟨D, -, -⟩ := Erdos634.Draft.WGapRung.wt_6_11_11
  exact ⟨D⟩
theorem tileCount_59534 : Erdos634.Draft.TileCountFamilies.TileCount 59534 := by
  obtain ⟨D, -, -⟩ := Erdos634.Draft.WGapRung.wt_6_11_17
  exact ⟨D⟩

theorem ctl_not_cnzFixW_126 : ¬ CNzFixW 126 := fun h => not_tileCount_of_CNzFixW 126 h tileCount_126
theorem ctl_not_cnzFixW_24926 : ¬ CNzFixW 24926 := fun h => not_tileCount_of_CNzFixW 24926 h tileCount_24926
theorem ctl_not_cnzFixW_59534 : ¬ CNzFixW 59534 := fun h => not_tileCount_of_CNzFixW 59534 h tileCount_59534

-- the failing conjunct itself, by the kernel
theorem ctl_not_rwChkW_126 : ¬ RWChkW 126 := by decide +kernel
theorem ctl_not_rwChkW_24926 : ¬ RWChkW 24926 := by decide +kernel
theorem ctl_not_rwChkW_59534 : ¬ RWChkW 59534 := by decide +kernel
theorem ctl_not_cnzFixW_126' : ¬ CNzFixW 126 := fun h => ctl_not_rwChkW_126 h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ctl_not_cnzFixW_24926' : ¬ CNzFixW 24926 := fun h => ctl_not_rwChkW_24926 h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ctl_not_cnzFixW_59534' : ¬ CNzFixW 59534 := fun h => ctl_not_rwChkW_59534 h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

-- (b) other tile counts: conjunct that fails (positions: 1 NQ, 2 Ell/Asq, 3 NSq, ..., 9 S3, 11 NoF, 14 RWChkW)
theorem ctl_not_cnzFixW_1648 : ¬ CNzFixW 1648 := fun h => (by decide +kernel : ¬ RWChkW 1648) h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ctl_not_cnzFixW_4450 : ¬ CNzFixW 4450 := fun h => (by decide +kernel : ¬ NSqChkSq 4450) h.2.2.1
theorem ctl_not_cnzFixW_143 : ¬ CNzFixW 143 := fun h => (by decide +kernel : ¬ (NoF2ChkSq 143 ∧ NoF3zChkSq 143 ∧ NoF4zChkSq 143)) h.2.2.2.2.2.2.2.2.2.2.1
theorem ctl_not_cnzFixW_189 : ¬ CNzFixW 189 := fun h => (by decide +kernel : ¬ S3newChk 189) h.2.2.2.2.2.2.2.2.1
theorem ctl_not_cnzFixW_345 : ¬ CNzFixW 345 := fun h => (by decide +kernel : ¬ (NoF2ChkSq 345 ∧ NoF3zChkSq 345 ∧ NoF4zChkSq 345)) h.2.2.2.2.2.2.2.2.2.2.1

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.ctl_not_cnzFixW_126
#print axioms Erdos634.Draft.NSQM.ctl_not_cnzFixW_24926
#print axioms Erdos634.Draft.NSQM.ctl_not_cnzFixW_59534
#print axioms Erdos634.Draft.NSQM.ctl_not_cnzFixW_126'
#print axioms Erdos634.Draft.NSQM.ctl_not_cnzFixW_24926'
#print axioms Erdos634.Draft.NSQM.ctl_not_cnzFixW_59534'
#print axioms Erdos634.Draft.NSQM.ctl_not_cnzFixW_1648
#print axioms Erdos634.Draft.NSQM.ctl_not_cnzFixW_4450
#print axioms Erdos634.Draft.NSQM.ctl_not_cnzFixW_143
#print axioms Erdos634.Draft.NSQM.ctl_not_cnzFixW_189
#print axioms Erdos634.Draft.NSQM.ctl_not_cnzFixW_345

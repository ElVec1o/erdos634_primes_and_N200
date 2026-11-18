/-
Draft/WGapLightLink.lean -- 16 November 2026 (work item internal working notes).  UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.
HEAVY link (imports WGapLink2): `CNzFixWl N -> CNzFixW N` (WGapLightDefs), hence `CNzFixWl N -> not TileCount N`.  Generic, built once.
Per-N work (deciding `CNzFixWl N`) lives in light modules that import only WGapLightDefs.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLightDefs
import Erdos634.Draft.WGapLink2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM

theorem rwChkWl_iff (N : ℕ) : RWChkWl N ↔ RWChkW N := Iff.rfl

theorem cnzFixW_of_l {N : ℕ} (h : CNzFixWl N) : CNzFixW N := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, leafEsqS_of_R h6, h7, h8, h9, h10, h11, h12, h13, (rwChkWl_iff N).1 h14, h15⟩

theorem not_tileCount_of_l (N : ℕ) (h : CNzFixWl N) : ¬ Erdos634.Draft.TileCountFamilies.TileCount N :=
  not_tileCount_of_CNzFixW N (cnzFixW_of_l h)

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.not_tileCount_of_l
#print axioms Erdos634.Draft.NSQM.pairs60_of_R
#print axioms Erdos634.Draft.NSQM.pairs120_of_R

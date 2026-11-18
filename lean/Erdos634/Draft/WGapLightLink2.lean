/-
Draft/WGapLightLink2.lean -- 16 November 2026 (work item internal working notes).  UNAUDITED beyond internal checks.  Leaf module, imported by no aggregate.
HEAVY link of the self-contained copy: `WGapPure.CNzFixP N -> NSQM.CNzFixW N` (each of the 15 conjuncts by definitional unfolding, so every transcription is checked by the
kernel), hence `CNzFixP N -> not TileCount N`.  Generic, built once.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapLightPure
import Erdos634.Draft.WGapLightLink

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.WGapPure

open Erdos634.Draft.NSQM

theorem cnzFixW_of_P {N : ℕ} (h : CNzFixP N) : CNzFixW N := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ⟨h11a, h11b, h11c⟩, h12, h13, h14, h15⟩ := h
  have e60 : ∀ M : ℕ, Erdos634.Draft.WGapPure.Pairs60R M → Erdos634.Draft.NSQM.Pairs60R M := fun M h => h
  have e120 : ∀ M : ℕ, Erdos634.Draft.WGapPure.Pairs120R M → Erdos634.Draft.NSQM.Pairs120R M := fun M h => h
  refine ⟨h1, h2, h3, h4, h5, leafEsqS_of_R ?_, h7, h8, h9, h10, ⟨h11a, h11b, h11c⟩, h12, h13, h14, h15⟩
  rcases h6 with h | ⟨hh, ha, hb⟩
  · exact Or.inl h
  · exact Or.inr ⟨hh, e60 N ha, e120 N hb⟩

theorem not_tileCount_of_P (N : ℕ) (h : CNzFixP N) : ¬ Erdos634.Draft.TileCountFamilies.TileCount N :=
  not_tileCount_of_CNzFixW N (cnzFixW_of_P h)

end Erdos634.Draft.WGapPure

#print axioms Erdos634.Draft.WGapPure.not_tileCount_of_P
#print axioms Erdos634.Draft.WGapPure.cover_divisors

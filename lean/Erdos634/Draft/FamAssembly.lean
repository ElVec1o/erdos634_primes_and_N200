-- Draft/FamAssembly.lean — the assembly of the existence families:
-- `Fam N → TileCount N`.  Existence only (no theoremP_6 dependence).  Not imported by `All`.
import Erdos634.Draft.WFamily
import Erdos634.Draft.SporadicCounts

namespace Erdos634.Draft.FamAssembly
open Erdos634.Draft.TileCountFamilies

/-- The families proved to occur as tile counts. -/
def Fam (N : ℕ) : Prop :=
  (∃ k, 0 < k ∧ N = k * k)
  ∨ (∃ k a b, 0 < k ∧ 0 < a ∧ 0 < b ∧ N = k * k * (a * a + b * b))
  ∨ (∃ k, 0 < k ∧ N = 3 * (k * k))
  ∨ (∃ k, 0 < k ∧ N = 6 * (k * k))
  ∨ (∃ m, 2 ≤ m ∧ N = 7 * (m * m))
  ∨ (∃ m, 2 ≤ m ∧ N = 11 * (m * m))
  ∨ N = 77

theorem Fam_subset_S {N : ℕ} (h : Fam N) : TileCount N := by
  rcases h with ⟨k, hk, rfl⟩ | ⟨k, a, b, hk, ha, hb, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | rfl
  · exact tileCount_sq hk
  · exact tileCount_sq_mul_two_squares hk ha hb
  · exact tileCount_three_sq hk
  · exact tileCount_six_sq hk
  · exact Erdos634.Draft.WFamily.tileCount_seven_sq hm
  · exact tileCount_eleven_sq hm
  · exact Erdos634.Draft.SporadicCounts.tc77

end Erdos634.Draft.FamAssembly

#print axioms Erdos634.Draft.FamAssembly.Fam_subset_S

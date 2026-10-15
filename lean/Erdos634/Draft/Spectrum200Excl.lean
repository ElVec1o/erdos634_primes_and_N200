/-
Draft/Spectrum200Excl.lean -- the spectrum up to 200 from six exclusions, with no certificate imported.

    theorem tileCount_iff_le_200_of_excl
        (h132 : ¬ TileCount 132) (h135 : ¬ TileCount 135) (h154 : ¬ TileCount 154) (h156 : ¬ TileCount 156)
        (h161 : ¬ TileCount 161) (h184 : ¬ TileCount 184) {N : ℕ} (h1 : 1 ≤ N) (h200 : N ≤ 200) :
        TileCount N ↔ FamD N = true

The six values are settled by search certificates of 63,895 to 1,326,256 nodes each.
A module that imports several of them exceeds the memory budget of a single `lean` process (about 9 GB),
so each exclusion lives in its own module (`N132Final`, `N135Final`, `N154Final`, `N156Final`, `N161Final`,
`N184Final`) and the
statement about all `N ≤ 200` is kept here in the form "given the six exclusions", without importing any of them.
Each of the six hypotheses is a Lean theorem (`N132F.not_tileCount_132`, `N135F.not_tileCount_135`,
`N154F.not_tileCount_154`, `N156.not_tileCount_156`, `N161F.not_tileCount_161`, `N184F.not_tileCount_184`).
Every hypothesis is of the form `¬ TileCount n`.

No sorry, no native_decide.
-/
import Erdos634.Draft.N143

namespace Erdos634.Draft.Spectrum200Excl

open Erdos634.Geometry Erdos634.Draft.TileCountFamilies
open Erdos634.Draft.Spectrum200d Erdos634.Draft.Spectrum200g Erdos634.Draft.N143

/-- **The spectrum up to 200, given the six exclusions.** -/
theorem tileCount_iff_le_200_of_excl
    (h132 : ¬ TileCount 132) (h135 : ¬ TileCount 135) (h154 : ¬ TileCount 154) (h156 : ¬ TileCount 156)
    (h161 : ¬ TileCount 161) (h184 : ¬ TileCount 184) {N : ℕ} (h1 : 1 ≤ N) (h200 : N ≤ 200) :
    TileCount N ↔ FamD N = true := by
  by_cases h143 : N = 143
  · subst h143
    exact ⟨fun _ => by decide +kernel, fun _ => tileCount_143⟩
  have hD : FamD N = FamC N := by
    have : (N == 143) = false := by simpa using h143
    simp [FamD, this]
  rw [hD]
  by_cases hu : N ∈ undecided200g
  · simp only [undecided200g, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun h => absurd h h132, fun hf => absurd hf (by decide +kernel)⟩
    · exact ⟨fun h => absurd h h135, fun hf => absurd hf (by decide +kernel)⟩
    · exact absurd rfl h143
    · exact ⟨fun h => absurd h h154, fun hf => absurd hf (by decide +kernel)⟩
    · exact ⟨fun h => absurd h h156, fun hf => absurd hf (by decide +kernel)⟩
    · exact ⟨fun h => absurd h h161, fun hf => absurd hf (by decide +kernel)⟩
    · exact ⟨fun h => absurd h h184, fun hf => absurd hf (by decide +kernel)⟩
  · exact tileCount_iff_le_200g h1 h200 hu

/-- the converse reading: below 200 the six exclusions are also NECESSARY for the formula (each of the six values
has `FamD = false`) -/
theorem excl_of_tileCount_iff (h : ∀ N : ℕ, 1 ≤ N → N ≤ 200 → (TileCount N ↔ FamD N = true)) :
    ¬ TileCount 132 ∧ ¬ TileCount 135 ∧ ¬ TileCount 154 ∧ ¬ TileCount 156 ∧ ¬ TileCount 161 ∧ ¬ TileCount 184 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hT
  · exact absurd ((h 132 (by norm_num) (by norm_num)).mp hT) (by decide +kernel)
  · exact absurd ((h 135 (by norm_num) (by norm_num)).mp hT) (by decide +kernel)
  · exact absurd ((h 154 (by norm_num) (by norm_num)).mp hT) (by decide +kernel)
  · exact absurd ((h 156 (by norm_num) (by norm_num)).mp hT) (by decide +kernel)
  · exact absurd ((h 161 (by norm_num) (by norm_num)).mp hT) (by decide +kernel)
  · exact absurd ((h 184 (by norm_num) (by norm_num)).mp hT) (by decide +kernel)

end Erdos634.Draft.Spectrum200Excl

#print axioms Erdos634.Draft.Spectrum200Excl.tileCount_iff_le_200_of_excl
#print axioms Erdos634.Draft.Spectrum200Excl.excl_of_tileCount_iff

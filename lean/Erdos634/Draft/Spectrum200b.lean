import Erdos634.Draft.SpectrumGap200
import Erdos634.Draft.N92
import Erdos634.Draft.N124
import Erdos634.Draft.N140
import Erdos634.Draft.N172
import Erdos634.Draft.N188

/-! Draft/Spectrum200b.lean -- the tile-count spectrum up to 200: everything except 13 values is decided in Lean.

`SpectrumGap200.tileCount_iff_le_200` left 18 values undecided.  Five of them are now excluded
(`N92.not_tile_92`, `N124.not_tile_124`, `N140.not_tile_140`, `N172.not_tile_172`, `N188.not_tile_188`), so the
Lean table for `1 ≤ N ≤ 200` has exactly 13 undecided entries, `undecided200b`; the smallest is 105.

Composite-N statement; not prime-case work.  No sorry, no native_decide. -/

namespace Erdos634.Draft.Spectrum200b

open Erdos634.Draft.TileCountFamilies Erdos634.Geometry Erdos634.Draft.FDDSpectrumTable Erdos634.Draft.SpectrumGap200

/-- the values `≤ 200` not decided by this file -/
def undecided200b : List ℕ := [105, 120, 132, 135, 143, 154, 156, 161, 168, 171, 184, 189, 198]

/-- **The spectrum up to 200, outside 13 undecided values.** -/
theorem tileCount_iff_le_200b {N : ℕ} (h1 : 1 ≤ N) (h200 : N ≤ 200) (hu : N ∉ undecided200b) :
    TileCount N ↔ FamB N = true := by
  by_cases h : N ∈ [92, 124, 140, 172, 188]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact ⟨fun ⟨D⟩ => (Erdos634.Draft.N92.not_tile_92 D).elim, fun h => absurd h (by decide +kernel)⟩
    · exact ⟨fun ⟨D⟩ => (Erdos634.Draft.N124.not_tile_124 D).elim, fun h => absurd h (by decide +kernel)⟩
    · exact ⟨fun ⟨D⟩ => (Erdos634.Draft.N140.not_tile_140 D).elim, fun h => absurd h (by decide +kernel)⟩
    · exact ⟨fun ⟨D⟩ => (Erdos634.Draft.N172.not_tile_172 D).elim, fun h => absurd h (by decide +kernel)⟩
    · exact ⟨fun ⟨D⟩ => (Erdos634.Draft.N188.not_tile_188 D).elim, fun h => absurd h (by decide +kernel)⟩
  · refine tileCount_iff_le_200 h1 h200 ?_
    intro hu'
    simp only [undecided200, undecided200b, List.mem_cons, List.not_mem_nil, or_false] at hu' hu h
    omega

/-- the five values closed since `SpectrumGap200` are not tile counts -/
theorem not_tileCount_92_124_140_172_188 :
    ¬ TileCount 92 ∧ ¬ TileCount 124 ∧ ¬ TileCount 140 ∧ ¬ TileCount 172 ∧ ¬ TileCount 188 :=
  ⟨fun ⟨D⟩ => Erdos634.Draft.N92.not_tile_92 D, fun ⟨D⟩ => Erdos634.Draft.N124.not_tile_124 D,
    fun ⟨D⟩ => Erdos634.Draft.N140.not_tile_140 D, fun ⟨D⟩ => Erdos634.Draft.N172.not_tile_172 D,
    fun ⟨D⟩ => Erdos634.Draft.N188.not_tile_188 D⟩

end Erdos634.Draft.Spectrum200b

#print axioms Erdos634.Draft.Spectrum200b.tileCount_iff_le_200b

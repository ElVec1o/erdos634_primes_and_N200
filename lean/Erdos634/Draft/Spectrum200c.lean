import Erdos634.Draft.Spectrum200b
import Erdos634.Draft.N168
import Erdos634.Draft.N198

/-! Draft/Spectrum200c.lean -- the tile-count spectrum up to 200: everything except 11 values is decided in Lean.

`Spectrum200b.tileCount_iff_le_200b` left 13 values undecided.  Two of them are now excluded
(`N168.not_tile_168`, `N198.not_tile_198`: their only open leaf was the `π/3` equilateral leaf, closed by certificates
with Galois-conjugate kills), so the Lean table for `1 ≤ N ≤ 200` has exactly 11 undecided entries, `undecided200c`;
the smallest is 105.

Composite-N statement; not prime-case work.  No sorry, no native_decide. -/

namespace Erdos634.Draft.Spectrum200c

open Erdos634.Draft.TileCountFamilies Erdos634.Geometry Erdos634.Draft.FDDSpectrumTable Erdos634.Draft.Spectrum200b

/-- the values `≤ 200` not decided by this file -/
def undecided200c : List ℕ := [105, 120, 132, 135, 143, 154, 156, 161, 171, 184, 189]

/-- **The spectrum up to 200, outside 11 undecided values.** -/
theorem tileCount_iff_le_200c {N : ℕ} (h1 : 1 ≤ N) (h200 : N ≤ 200) (hu : N ∉ undecided200c) :
    TileCount N ↔ FamB N = true := by
  by_cases h : N ∈ [168, 198]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact ⟨fun ⟨D⟩ => (Erdos634.Draft.N168.not_tile_168 D).elim, fun h => absurd h (by decide +kernel)⟩
    · exact ⟨fun ⟨D⟩ => (Erdos634.Draft.N198.not_tile_198 D).elim, fun h => absurd h (by decide +kernel)⟩
  · refine tileCount_iff_le_200b h1 h200 ?_
    intro hu'
    simp only [undecided200b, undecided200c, List.mem_cons, List.not_mem_nil, or_false] at hu' hu h
    omega

/-- the two values closed since `Spectrum200b` are not tile counts -/
theorem not_tileCount_168_198 : ¬ TileCount 168 ∧ ¬ TileCount 198 :=
  ⟨fun ⟨D⟩ => Erdos634.Draft.N168.not_tile_168 D, fun ⟨D⟩ => Erdos634.Draft.N198.not_tile_198 D⟩

end Erdos634.Draft.Spectrum200c

#print axioms Erdos634.Draft.Spectrum200c.tileCount_iff_le_200c

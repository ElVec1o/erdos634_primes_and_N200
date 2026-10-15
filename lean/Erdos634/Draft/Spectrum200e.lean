import Erdos634.Draft.Spectrum200d
import Erdos634.Draft.N171

/-! Draft/Spectrum200e.lean -- the tile-count spectrum up to 200: everything except 9 values is decided in Lean.

Since `Spectrum200d` (10 undecided values), `171` is excluded (`N171.not_tile_171`: its three open leaves are closed:
the `π/3` pair `(57, 9)` has a non-square discriminant (`E60Irr.e60Pair_of_not_isSquare`), and the S5 instance
`(3, 9, 10)` and the `γ = 2α` pair `(3, 57)` are refuted by kernel-checked certificates).

The Lean table for `1 ≤ N ≤ 200` has exactly 9 undecided entries, `undecided200e`; the smallest is 105.

Composite-N statement; not prime-case work.  No sorry, no native_decide. -/

namespace Erdos634.Draft.Spectrum200e

open Erdos634.Draft.TileCountFamilies Erdos634.Geometry Erdos634.Draft.FDDSpectrumTable Erdos634.Draft.Spectrum200d

/-- the values `≤ 200` not decided by this file -/
def undecided200e : List ℕ := [105, 120, 132, 135, 143, 154, 156, 161, 184]

/-- **The spectrum up to 200, outside 9 undecided values.** -/
theorem tileCount_iff_le_200e {N : ℕ} (h1 : 1 ≤ N) (h200 : N ≤ 200) (hu : N ∉ undecided200e) :
    TileCount N ↔ FamC N = true := by
  by_cases h171 : N = 171
  · subst h171
    exact ⟨fun ⟨D⟩ => (Erdos634.Draft.N171.not_tile_171 D).elim, fun h => absurd h (by decide +kernel)⟩
  refine tileCount_iff_le_200d h1 h200 ?_
  intro hu'
  simp only [undecided200d, undecided200e, List.mem_cons, List.not_mem_nil, or_false] at hu' hu
  omega

end Erdos634.Draft.Spectrum200e

#print axioms Erdos634.Draft.Spectrum200e.tileCount_iff_le_200e

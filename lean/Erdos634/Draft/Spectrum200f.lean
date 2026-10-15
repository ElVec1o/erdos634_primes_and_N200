import Erdos634.Draft.Spectrum200e
import Erdos634.Draft.N120

/-! Draft/Spectrum200f.lean -- the tile-count spectrum up to 200: everything except 8 values is decided in Lean.

Since `Spectrum200e` (9 undecided values), `120` is excluded (`N120.not_tile_120`: the Case A leaf by the uniform theorem
`GAU.gapA_sq` for `N = 30 s²`, the equilateral `π/3` leaf by `E60N120.gapE60_120`, and the `F₁` pair `(6, 20)` by the
kernel-checked certificate `Refl.MF120`).

The Lean table for `1 ≤ N ≤ 200` has exactly 8 undecided entries, `undecided200f`; the smallest is 105.

Composite-N statement; not prime-case work.  No sorry, no native_decide. -/

namespace Erdos634.Draft.Spectrum200f

open Erdos634.Draft.TileCountFamilies Erdos634.Geometry Erdos634.Draft.FDDSpectrumTable Erdos634.Draft.Spectrum200d
open Erdos634.Draft.Spectrum200e

/-- the values `≤ 200` not decided by this file -/
def undecided200f : List ℕ := [105, 132, 135, 143, 154, 156, 161, 184]

/-- **The spectrum up to 200, outside 8 undecided values.** -/
theorem tileCount_iff_le_200f {N : ℕ} (h1 : 1 ≤ N) (h200 : N ≤ 200) (hu : N ∉ undecided200f) :
    TileCount N ↔ FamC N = true := by
  by_cases h120 : N = 120
  · subst h120
    exact ⟨fun ⟨D⟩ => (Erdos634.Draft.N120.not_tile_120 D).elim, fun h => absurd h (by decide +kernel)⟩
  refine tileCount_iff_le_200e h1 h200 ?_
  intro hu'
  simp only [undecided200e, undecided200f, List.mem_cons, List.not_mem_nil, or_false] at hu' hu
  omega

end Erdos634.Draft.Spectrum200f

#print axioms Erdos634.Draft.Spectrum200f.tileCount_iff_le_200f

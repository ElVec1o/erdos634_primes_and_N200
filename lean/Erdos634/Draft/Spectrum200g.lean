import Erdos634.Draft.Spectrum200f
import Erdos634.Draft.N105

/-! The tile-count spectrum up to 200, with `105` excluded.

`105` is excluded (`N105.not_tile_105`: the equilateral `π/3` leaf by
`Eq105.gapE60_105` and the two rational `F₁` pairs `(5, 21)`, `(3, 35)` by the kernel-checked certificates
`Refl.MF105A`, `Refl.MF105B`).  The exclusion of 105 was also announced by D. Paliy (unrefereed note, four exact
certificates for the same four instances).

`undecided200g` lists the values `≤ 200` for which this file gives no verdict.

No sorry, no native_decide. -/

namespace Erdos634.Draft.Spectrum200g

open Erdos634.Draft.TileCountFamilies Erdos634.Geometry Erdos634.Draft.FDDSpectrumTable Erdos634.Draft.Spectrum200d
open Erdos634.Draft.Spectrum200f

/-- the values `≤ 200` not decided by this file -/
def undecided200g : List ℕ := [132, 135, 143, 154, 156, 161, 184]

/-- **The spectrum up to 200, outside 7 undecided values.** -/
theorem tileCount_iff_le_200g {N : ℕ} (h1 : 1 ≤ N) (h200 : N ≤ 200) (hu : N ∉ undecided200g) :
    TileCount N ↔ FamC N = true := by
  by_cases h105 : N = 105
  · subst h105
    exact ⟨fun ⟨D⟩ => (Erdos634.Draft.N105.not_tile_105 D).elim, fun h => absurd h (by decide +kernel)⟩
  refine tileCount_iff_le_200f h1 h200 ?_
  intro hu'
  simp only [undecided200f, undecided200g, List.mem_cons, List.not_mem_nil, or_false] at hu' hu
  omega

/-- **Every `N ≤ 131` is decided.** -/
theorem tileCount_iff_le_131 {N : ℕ} (h1 : 1 ≤ N) (h131 : N ≤ 131) : TileCount N ↔ FamC N = true :=
  tileCount_iff_le_200g h1 (by omega) (by
    intro hu
    simp only [undecided200g, List.mem_cons, List.not_mem_nil, or_false] at hu
    omega)

end Erdos634.Draft.Spectrum200g

#print axioms Erdos634.Draft.Spectrum200g.tileCount_iff_le_200g
#print axioms Erdos634.Draft.Spectrum200g.tileCount_iff_le_131

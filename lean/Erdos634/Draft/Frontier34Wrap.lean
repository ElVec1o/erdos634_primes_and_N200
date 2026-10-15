import Erdos634.Draft.SpectrumGap200
import Erdos634.Draft.N92

/-! Draft/Frontier34Wrap.lean -- the paper statements `thm:frontier3` and `thm:frontier4`, as written.

* `frontier3`: no triangle can be cut into 51, 55, 56, 57, 60, 62, 69 or 78 congruent triangles.
* `frontier4`: no triangle can be cut into 76 congruent triangles, and every `N ≤ 80` is determined
  (`TileCount N ↔ N ∈ tileCounts91`, an explicit list).
* `tileCount_iff_le_104`: with `N92.not_tile_92`, every `N ≤ 104` is determined (`TileCount N ↔ FamB N`).

`TileCount N = Nonempty (CongruentDissection N)`: any target triangle, any tile, isometries including reflections.
Composite-N statements; not prime-case work.  No sorry, no native_decide. -/

namespace Erdos634.Draft.Frontier34Wrap

open Erdos634.Draft.TileCountFamilies Erdos634.Geometry Erdos634.Draft.FDDSpectrumTable
open Erdos634.Draft.SpectrumLe91 Erdos634.Draft.SpectrumGap200

/-- **`thm:frontier3`.** -/
theorem frontier3 : ∀ N ∈ [51, 55, 56, 57, 60, 62, 69, 78], ¬ TileCount N := by
  intro N hN hT
  have h91 : N ≤ 91 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hN
    omega
  have h1 : 1 ≤ N := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hN
    omega
  have hmem := (tileCounts_le_91 h1 h91).mp hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hN
  rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd hmem (by decide)

/-- **`thm:frontier4`.** -/
theorem frontier4 : ¬ TileCount 76 ∧ ∀ N : ℕ, 1 ≤ N → N ≤ 80 → (TileCount N ↔ N ∈ tileCounts91) :=
  ⟨not_tileCount_56_60_70_76.2.2.2, fun _ h1 h80 => tileCounts_le_91 h1 (by omega)⟩

/-- **Every `N ≤ 104` is determined.** -/
theorem tileCount_iff_le_104 {N : ℕ} (h1 : 1 ≤ N) (h104 : N ≤ 104) : TileCount N ↔ FamB N = true := by
  by_cases h92 : N = 92
  · subst h92
    constructor
    · rintro ⟨D⟩; exact (Erdos634.Draft.N92.not_tile_92 D).elim
    · intro h; exact absurd h (by decide +kernel)
  · refine tileCount_iff_le_200 h1 (by omega) ?_
    intro hu
    simp only [undecided200, List.mem_cons, List.not_mem_nil, or_false] at hu
    omega

end Erdos634.Draft.Frontier34Wrap

#print axioms Erdos634.Draft.Frontier34Wrap.frontier3
#print axioms Erdos634.Draft.Frontier34Wrap.frontier4
#print axioms Erdos634.Draft.Frontier34Wrap.tileCount_iff_le_104

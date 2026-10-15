import Erdos634.Draft.Spectrum200c
import Erdos634.R189TilingBridge

/-! The tile-count spectrum up to 200, with the value 189 added.

`189` is realized (`R189TilingBridge.r189_nonempty_congruentDissection`: 189 copies of `(2,3,4)` tile the isosceles triangle `(36,36,63)`;
a 189-tiling of this triangle is due to J. P. Harries).  `189` is not
in the families of `FamB`, so the table of realizable values is `FamC = FamB ∪ {189}`.

`undecided200d` lists the values `≤ 200` for which this file gives no verdict.

No sorry, no native_decide. -/

namespace Erdos634.Draft.Spectrum200d

open Erdos634.Draft.TileCountFamilies Erdos634.Geometry Erdos634.Draft.FDDSpectrumTable Erdos634.Draft.Spectrum200c

/-- the realizable table: the families of `FamB` and the value 189 -/
def FamC (N : ℕ) : Bool := FamB N || N == 189

/-- the values `≤ 200` not decided by this file -/
def undecided200d : List ℕ := [105, 120, 132, 135, 143, 154, 156, 161, 171, 184]

/-- **189 is a tile count.** -/
theorem tileCount_189 : TileCount 189 := Erdos634.R189TilingBridge.r189_nonempty_congruentDissection

/-- **The spectrum up to 200, outside 10 undecided values.** -/
theorem tileCount_iff_le_200d {N : ℕ} (h1 : 1 ≤ N) (h200 : N ≤ 200) (hu : N ∉ undecided200d) :
    TileCount N ↔ FamC N = true := by
  by_cases h189 : N = 189
  · subst h189
    exact ⟨fun _ => by decide +kernel, fun _ => tileCount_189⟩
  have hC : FamC N = FamB N := by
    have : (N == 189) = false := by simpa using h189
    simp [FamC, this]
  rw [hC]
  refine tileCount_iff_le_200c h1 h200 ?_
  intro hu'
  simp only [undecided200c, undecided200d, List.mem_cons, List.not_mem_nil, or_false] at hu' hu
  omega

/-- the values decided since `Spectrum200b`: 168 and 198 are not tile counts and 189 is one -/
theorem decided_168_189_198 : ¬ TileCount 168 ∧ TileCount 189 ∧ ¬ TileCount 198 :=
  ⟨fun ⟨D⟩ => Erdos634.Draft.N168.not_tile_168 D, tileCount_189, fun ⟨D⟩ => Erdos634.Draft.N198.not_tile_198 D⟩

end Erdos634.Draft.Spectrum200d

#print axioms Erdos634.Draft.Spectrum200d.tileCount_iff_le_200d

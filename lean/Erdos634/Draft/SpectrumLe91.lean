import Erdos634.Draft.FDDSpectrumTable
import Erdos634.Draft.N566076
import Erdos634.Draft.T30Cert
import Erdos634.Draft.N70

/-! Draft/SpectrumLe91.lean -- the tile-count spectrum is decided for every `N ≤ 91`.

`FDDSpectrumTable.spectrumStatus` left exactly four values `≤ 91` undecided in Lean: `56, 60, 70, 76`
(the next one is `92`).  With `N566076.not_tile_56`, `T30Cert.not_tile_60`, `AllN2.not_tile_70`, `N566076.not_tile_76`:

  `tileCount_iff_le_91 : 1 ≤ N → N ≤ 91 → (TileCount N ↔ FamB N = true)`

where `TileCount N := Nonempty (CongruentDissection N)` and `FamB` is the Boolean of the realizable families
(`k²`, `3k²`, `6k²`, `7m²`, `11m²` (`m ≥ 2`), `k²(a²+b²)`, and `k²·s` for the certified sporadic `s`).
`tileCounts_le_91` lists the 54 tile counts `≤ 91` explicitly.

Every ingredient is (including `theoremP_6` for the primes `≡ 3 (mod 4)`); no paper label is
changed by this file.  Corresponds to `thm:frontier4` ("every `N ≤ 80` is determined") and the paragraph on `81–90`.
No sorry, no native_decide. -/

namespace Erdos634.Draft.SpectrumLe91

open Erdos634.Draft.TileCountFamilies Erdos634.Geometry Erdos634.Draft.FDDSpectrumTable

set_option maxRecDepth 100000 in
theorem excluded_cases : ∀ N : ℕ, 1 ≤ N → N ≤ 91 → FamB N ≠ true →
    N ∈ exclList ∨ N ∈ primeExcl ∨ N = 56 ∨ N = 60 ∨ N = 70 ∨ N = 76 := by
  intro N h1 h91 hF
  interval_cases N <;> first | decide | exact absurd (by decide +kernel) hF

/-- **The spectrum up to 91.**  For `1 ≤ N ≤ 91`: a triangle can be cut into `N` congruent triangles iff `N` belongs to
one of the realizable families. -/
theorem tileCount_iff_le_91 {N : ℕ} (h1 : 1 ≤ N) (h91 : N ≤ 91) : TileCount N ↔ FamB N = true := by
  constructor
  · intro hT
    by_contra hF
    rcases excluded_cases N h1 h91 hF with h | h | rfl | rfl | rfl | rfl
    · exact not_tileCount_of_mem_exclList h hT
    · exact not_tileCount_of_mem_primeExcl h hT
    · obtain ⟨D⟩ := hT; exact Erdos634.Draft.N566076.not_tile_56 D
    · obtain ⟨D⟩ := hT; exact Erdos634.Draft.T30Cert.not_tile_60 D
    · obtain ⟨D⟩ := hT; exact Erdos634.Draft.AllN2.not_tile_70 D
    · obtain ⟨D⟩ := hT; exact Erdos634.Draft.N566076.not_tile_76 D
  · exact fam_sound

/-- the tile counts `≤ 91` -/
def tileCounts91 : List ℕ :=
  [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 16, 17, 18, 20, 24, 25, 26, 27, 28, 29, 32, 34, 36, 37, 40, 41, 44, 45, 48, 49,
   50, 52, 53, 54, 58, 61, 63, 64, 65, 68, 72, 73, 74, 75, 77, 80, 81, 82, 84, 85, 88, 89, 90]

set_option maxRecDepth 100000 in
theorem famB_iff_mem : ∀ N : ℕ, 1 ≤ N → N ≤ 91 → (FamB N = true ↔ N ∈ tileCounts91) := by
  intro N h1 h91
  interval_cases N <;> decide +kernel

/-- **The tile counts up to 91, explicitly.** -/
theorem tileCounts_le_91 {N : ℕ} (h1 : 1 ≤ N) (h91 : N ≤ 91) : TileCount N ↔ N ∈ tileCounts91 :=
  (tileCount_iff_le_91 h1 h91).trans (famB_iff_mem N h1 h91)

/-- no tile count among `56, 60, 70, 76` -/
theorem not_tileCount_56_60_70_76 : ¬ TileCount 56 ∧ ¬ TileCount 60 ∧ ¬ TileCount 70 ∧ ¬ TileCount 76 :=
  ⟨fun ⟨D⟩ => Erdos634.Draft.N566076.not_tile_56 D, fun ⟨D⟩ => Erdos634.Draft.T30Cert.not_tile_60 D,
   fun ⟨D⟩ => Erdos634.Draft.AllN2.not_tile_70 D, fun ⟨D⟩ => Erdos634.Draft.N566076.not_tile_76 D⟩

end Erdos634.Draft.SpectrumLe91

#print axioms Erdos634.Draft.SpectrumLe91.tileCount_iff_le_91
#print axioms Erdos634.Draft.SpectrumLe91.tileCounts_le_91
#print axioms Erdos634.Draft.SpectrumLe91.not_tileCount_56_60_70_76

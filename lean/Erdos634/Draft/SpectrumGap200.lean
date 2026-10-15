import Erdos634.Draft.SpectrumLe91
import Erdos634.Draft.AllN2CheckGap200a
import Erdos634.Draft.AllN2CheckGap200b

/-! Draft/SpectrumGap200.lean -- the tile-count spectrum below 200: everything except 18 values is decided in Lean.

Sixteen squarefree values below 200 satisfy the general exclusion condition `AllN2.C'` but had never been instantiated
(`AllN2CheckGap200a/b`): 102, 114, 115, 118, 119, 134, 138, 142, 155, 158, 166, 174, 182, 186, 187, 190.  With the four
values closed by certificates (56, 60, 70, 76) the Lean table for `1 ≤ N ≤ 200` has exactly 18 undecided entries,
`undecided200`; the smallest is 92. no paper label is changed.  No sorry, no native_decide. -/

namespace Erdos634.Draft.SpectrumGap200

open Erdos634.Draft.TileCountFamilies Erdos634.Geometry Erdos634.Draft.FDDSpectrumTable Erdos634.Draft.AllN2

def gap200 : List ℕ := [102, 114, 115, 118, 119, 134, 138, 142, 155, 158, 166, 174, 182, 186, 187, 190]

theorem not_tileCount_of_mem_gap200 {N : ℕ} (h : N ∈ gap200) : ¬ TileCount N := by
  simp only [gap200, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun ⟨D⟩ => not_tile'_102 D
  · exact fun ⟨D⟩ => not_tile'_114 D
  · exact fun ⟨D⟩ => not_tile'_115 D
  · exact fun ⟨D⟩ => not_tile'_118 D
  · exact fun ⟨D⟩ => not_tile'_119 D
  · exact fun ⟨D⟩ => not_tile'_134 D
  · exact fun ⟨D⟩ => not_tile'_138 D
  · exact fun ⟨D⟩ => not_tile'_142 D
  · exact fun ⟨D⟩ => not_tile'_155 D
  · exact fun ⟨D⟩ => not_tile'_158 D
  · exact fun ⟨D⟩ => not_tile'_166 D
  · exact fun ⟨D⟩ => not_tile'_174 D
  · exact fun ⟨D⟩ => not_tile'_182 D
  · exact fun ⟨D⟩ => not_tile'_186 D
  · exact fun ⟨D⟩ => not_tile'_187 D
  · exact fun ⟨D⟩ => not_tile'_190 D

/-- the values `≤ 200` not decided by this file -/
def undecided200 : List ℕ := [92, 105, 120, 124, 132, 135, 140, 143, 154, 156, 161, 168, 171, 172, 184, 188, 189, 198]

set_option maxRecDepth 100000 in
theorem excluded_cases200 : ∀ N : ℕ, 1 ≤ N → N ≤ 200 → N ∉ undecided200 → FamB N ≠ true →
    N ∈ exclList ∨ N ∈ primeExcl ∨ N ∈ gap200 ∨ N = 56 ∨ N = 60 ∨ N = 70 ∨ N = 76 := by
  intro N h1 h200 hu hF
  interval_cases N <;> first | decide | exact absurd (by decide +kernel) hF | exact absurd (by decide) hu

/-- **The spectrum up to 200, outside 18 undecided values.** -/
theorem tileCount_iff_le_200 {N : ℕ} (h1 : 1 ≤ N) (h200 : N ≤ 200) (hu : N ∉ undecided200) :
    TileCount N ↔ FamB N = true := by
  constructor
  · intro hT
    by_contra hF
    rcases excluded_cases200 N h1 h200 hu hF with h | h | h | rfl | rfl | rfl | rfl
    · exact not_tileCount_of_mem_exclList h hT
    · exact not_tileCount_of_mem_primeExcl h hT
    · exact not_tileCount_of_mem_gap200 h hT
    · obtain ⟨D⟩ := hT; exact Erdos634.Draft.N566076.not_tile_56 D
    · obtain ⟨D⟩ := hT; exact Erdos634.Draft.T30Cert.not_tile_60 D
    · obtain ⟨D⟩ := hT; exact Erdos634.Draft.AllN2.not_tile_70 D
    · obtain ⟨D⟩ := hT; exact Erdos634.Draft.N566076.not_tile_76 D
  · exact fam_sound

end Erdos634.Draft.SpectrumGap200

#print axioms Erdos634.Draft.SpectrumGap200.tileCount_iff_le_200

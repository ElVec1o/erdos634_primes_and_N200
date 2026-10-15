import Mathlib.Tactic
import Erdos634.Draft.FamAssembly
import Erdos634.Draft.TileCountSpectrum
import Erdos634.R84TilingBridge
import Erdos634.R88TilingBridge
import Erdos634.R126TilingBridge
import Erdos634.Draft.AllNExclusion
import Erdos634.Draft.AllN2Check4
import Erdos634.Draft.AllN2Check5
import Erdos634.Draft.AllN2Check8
import Erdos634.Draft.AllN2Check9
import Erdos634.Draft.AllN2Check12
import Erdos634.Draft.FDEChecks
import Erdos634.Draft.N15Final
import Erdos634.Draft.N30KF
import Erdos634.Draft.SIXF21
import Erdos634.Draft.SIXF33
import Erdos634.Draft.NSQCheck152

/-!
# The spectrum below 200 in Lean-checked form

`spectrumStatus N` is `realizable` / `excluded` / `unknown`, with soundness theorems

* `realizable_sound : spectrumStatus N = .realizable → TileCount N`   (all `N`),
* `excluded_sound   : spectrumStatus N = .excluded   → ¬ TileCount N` (all `N`),

so the table is Lean-checked entry by entry, and `unknown` means "no Lean proof either way found".
`TileCount N := Nonempty (CongruentDissection N)`.

Realizability families (`FamAssembly`, `SporadicCounts`, `R84/88/126TilingBridge`, `Ladder`): squares
`k²`, `k²(a²+b²)`, `3k²`, `6k²`, `7m²`, `11m²` (`m ≥ 2`), and the ladder `k²·s` over the certified
`s ∈ {28,44,63,77,84,88,99,126}`.  Exclusions: primes `≡ 3 (mod 4)`, `N > 3`
(`TileCountSpectrum.not_tileCount_prime` = `theoremP_6`) and the per-`N` composite chains listed in
`exclList` (each a hypothesis-free `CongruentDissection N → False` theorem).
-/

namespace Erdos634.Draft.FDDSpectrumTable
open Erdos634.Draft.TileCountFamilies Erdos634.Geometry

theorem tc_sporadic {s : ℕ} (hs : s ∈ sporadic) : TileCount s := by
  simp only [sporadic, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Erdos634.Draft.SporadicCounts.tc28
  · exact Erdos634.Draft.SporadicCounts.tc44
  · exact Erdos634.Draft.SporadicCounts.tc63
  · exact Erdos634.Draft.SporadicCounts.tc77
  · exact Erdos634.R84TilingBridge.r84_nonempty_congruentDissection
  · exact Erdos634.R88TilingBridge.r88_nonempty_congruentDissection
  · exact Erdos634.Draft.SporadicCounts.tc99
  · exact Erdos634.R126TilingBridge.r126_nonempty_congruentDissection

theorem fam_sound {N : ℕ} (h : FamB N = true) : TileCount N := by
  simp only [FamB, List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨k, -, hk, h⟩ := h
  rcases h with (((((h | h) | h) | ⟨hm, h | h⟩) | ⟨s, hs, h⟩) | ⟨a, -, b, -, ⟨ha, hb⟩, h⟩)
  · rw [h]; exact tileCount_sq hk
  · rw [h]; exact tileCount_three_sq hk
  · rw [h]; exact tileCount_six_sq hk
  · rw [h]; exact Erdos634.Draft.WFamily.tileCount_seven_sq hm
  · rw [h]; exact tileCount_eleven_sq hm
  · rw [h]; exact tileCount_scale (tc_sporadic hs) hk
  · rw [h]; exact tileCount_sq_mul_two_squares hk ha hb

theorem not_tileCount_of_mem_exclList {N : ℕ} (h : N ∈ exclList) : ¬ TileCount N := by
  simp only [exclList, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_14 D
  · exact fun ⟨D⟩ => Erdos634.Draft.N15Final.not_tile_15 D
  · exact fun ⟨D⟩ => Erdos634.Draft.SIXF21.chain_21_final' D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_22 D
  · exact fun ⟨D⟩ => Erdos634.N30K.not_tile_30 D
  · exact fun ⟨D⟩ => Erdos634.Draft.SIXF33.chain_33_final' D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_35 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_38 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_39 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_42 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_46 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_51 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_55 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_57 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_62 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_66 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_69 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_78 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_86 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllN2.not_tile'_87 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_91 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllN2.not_tile'_93 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_94 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_95 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_110 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllN2.not_tile'_111 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllN2.not_tile'_123 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllN2.not_tile'_129 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllNExclusion.not_tile_133 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllN2.not_tile'_141 D
  · exact fun ⟨D⟩ => Erdos634.Draft.NSQCheck152.not_tile_152 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllN2.not_tile'_159 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllN2.not_tile'_165 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllN2.not_tile'_177 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllN2.not_tile'_183 D
  · exact fun ⟨D⟩ => Erdos634.Draft.AllN2.not_tile'_195 D

theorem not_tileCount_of_mem_primeExcl {N : ℕ} (h : N ∈ primeExcl) : ¬ TileCount N := by
  simp only [primeExcl, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)
  · exact Erdos634.Draft.TileCountSpectrum.not_tileCount_prime (by norm_num) (by norm_num) (by norm_num)

theorem realizable_sound {N : ℕ} (h : spectrumStatus N = .realizable) : TileCount N := by
  unfold spectrumStatus at h
  split_ifs at h with h1 h2
  · exact fam_sound h1

theorem excluded_sound {N : ℕ} (h : spectrumStatus N = .excluded) : ¬ TileCount N := by
  unfold spectrumStatus at h
  by_cases hf : FamB N = true
  · simp [hf] at h
  · simp only [hf, if_false, Bool.false_eq_true] at h
    by_cases hx : (decide (N ∈ exclList) || decide (N ∈ primeExcl)) = true
    · simp only [Bool.or_eq_true, decide_eq_true_eq] at hx
      rcases hx with hx | hx
      · exact not_tileCount_of_mem_exclList hx
      · exact not_tileCount_of_mem_primeExcl hx
    · simp only [hx, if_false, Bool.false_eq_true] at h
      exact absurd h (by decide)

/-- The table is consistent: no `N` is both realizable and excluded (this follows from the two
soundness theorems; it is also checked by computation on `N ≤ 200`). -/
theorem no_overlap {N : ℕ} :
    ¬ (FamB N = true ∧ (decide (N ∈ exclList) || decide (N ∈ primeExcl)) = true) := by
  rintro ⟨hf, hx⟩
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hx
  rcases hx with hx | hx
  · exact not_tileCount_of_mem_exclList hx (fam_sound hf)
  · exact not_tileCount_of_mem_primeExcl hx (fam_sound hf)

/-- Examples of the soundness theorems at specific `N` (the incommensurable realizations). -/
theorem tc_84 : TileCount 84 := realizable_sound (by decide +kernel)
theorem tc_112 : TileCount 112 := realizable_sound (by decide +kernel)
theorem tc_175 : TileCount 175 := realizable_sound (by decide +kernel)
theorem not_tc_91 : ¬ TileCount 91 := excluded_sound (by decide +kernel)
theorem not_tc_131 : ¬ TileCount 131 := excluded_sound (by decide +kernel)

end Erdos634.Draft.FDDSpectrumTable

#print axioms Erdos634.Draft.FDDSpectrumTable.realizable_sound
#print axioms Erdos634.Draft.FDDSpectrumTable.excluded_sound
#print axioms Erdos634.Draft.FDDSpectrumTable.realizable_eq_paper
#print axioms Erdos634.Draft.FDDSpectrumTable.excluded_below_card
#print axioms Erdos634.Draft.FDDSpectrumTable.paper_excluded_missing_in_lean
#print axioms Erdos634.Draft.FDDSpectrumTable.lean_excluded_beyond_paper
#print axioms Erdos634.Draft.FDDSpectrumTable.unknown_eq
#print axioms Erdos634.Draft.FDDSpectrumTable.status_examples
#print axioms Erdos634.Draft.FDDSpectrumTable.tc_84
#print axioms Erdos634.Draft.FDDSpectrumTable.no_overlap_check
#print axioms Erdos634.Draft.FDDSpectrumTable.fam_sound
#print axioms Erdos634.Draft.FDDSpectrumTable.not_tc_131

import Erdos634.ARAForm
import Erdos634.ATDWit

/-!
# ARA: the derived integer corollaries on the two real witnesses  `B84.witness84` (`N = 84`, `(e,f) = (1,2)`, `X = 24`, `Y = 42`):
`84 = r²·3·7` with `r² = 4`, the area relation DERIVED (not assumed).  `ATDWit.witness_A4`
(`N = 48`, `X = 24`, `Y = 12`): `3·48 = μ²`, `μ = 12`, `48 = 3 r²`, `r² = 16`.
-/

namespace Erdos634.ARA
open Erdos634.Geometry

noncomputable section

theorem nform_at_84 : ∃ D : CongruentDissection 84, B84.Hyp 1 2 24 42 D ∧
    ∃ r : ℤ, ((84 : ℕ) : ℤ) = r ^ 2 * (2 ^ 2 - 1 ^ 2) * (2 * 2 ^ 2 - 1 ^ 2) ∧ r ^ 2 = 4 := by
  obtain ⟨D, h⟩ := B84.witness84
  obtain ⟨σ, τ, l0, l1, l2, a0, a1, m0, m1, m2⟩ := h
  obtain ⟨r, hr⟩ := theoremA_N_form_full D 1 2 (by norm_num) (by norm_num) (by norm_num) 24 42
    σ l0 l1 l2 τ a0 a1 m0 m1 m2
  refine ⟨D, ⟨σ, τ, l0, l1, l2, a0, a1, m0, m1, m2⟩, r, hr, ?_⟩
  push_cast at hr
  nlinarith

theorem atom_nform_A4 : ∃ D : CongruentDissection G3CAtomTiling.tiles.length,
    ATDL2.AHyp 1 2 24 12 D ∧ ∃ μ r : ℤ, μ = 12 ∧
      (2 ^ 2 - 1 ^ 2 : ℤ) * ((G3CAtomTiling.tiles.length : ℕ) : ℤ) = μ ^ 2 ∧
      ((G3CAtomTiling.tiles.length : ℕ) : ℤ) = (2 ^ 2 - 1 ^ 2) * r ^ 2 ∧ r ^ 2 = 16 := by
  obtain ⟨D, -, h⟩ := ATDL2.witness_A4
  obtain ⟨σ, τ, l0, l1, l2, a0, a1, m0, m1, m2⟩ := h
  obtain ⟨μ, r, hX, -, hZ, hr⟩ := atomDiv_N_form_full D 1 2 (by norm_num) (by norm_num)
    (by norm_num) 24 12 σ l0 l1 l2 τ a0 a1 m0 m1 m2
  have hμ : μ = 12 := by
    have h1 : (24 : ℝ) = 2 * μ := by simpa using hX
    have h2 : (24 : ℤ) = 2 * μ := by exact_mod_cast h1
    omega
  have hl : ((G3CAtomTiling.tiles.length : ℕ) : ℤ) = 48 := by
    rw [Erdos634.G3CAtomTilingBridge.tiles_length_eq_48]; norm_num
  refine ⟨D, ⟨σ, τ, l0, l1, l2, a0, a1, m0, m1, m2⟩, μ, r, hμ, hZ, hr, ?_⟩
  rw [hl] at hr
  nlinarith

end

end Erdos634.ARA

#print axioms Erdos634.ARA.nform_at_84
#print axioms Erdos634.ARA.atom_nform_A4

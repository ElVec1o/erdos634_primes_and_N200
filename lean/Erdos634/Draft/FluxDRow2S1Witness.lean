-- Draft/FluxDRow2S1Witness.lean: non-vacuity witness for Draft/FluxDRow2S1.lean on
-- `FluxRow2Witness.D2` (the scale-2 ladder of the `(16, 24, 32)` tile, `N = 4`, target `= 2·model`).
-- Imported by `All`.
--
-- * The model is scalene (`oppLen = (24, 32, 16)`), so `sideCount_sum`, `sideCount_eigen` (`μ = 2`) and
--   `sideCount_rows` apply in full: equation (1) `D v = 2 v` for the side matrix of `D2`.
-- * `Row2.mu_irrational` / `Row2.lemmaD_tiling` need `¬ IsSquare N`; `D2` has `N = 4 = 2²`, so that
--   hypothesis fails here (as it must: at `μ = 2` the ladder's sides are `2a, 2b, 2c`, and Lemma D's
--   irrational-eigenvalue argument does not apply).  No tile-similar tiling with non-square `N` is in
--   the corpus, so that hypothesis is unwitnessed jointly with the geometry.
import Erdos634.Draft.FluxDRow2S1
import Erdos634.Draft.FluxRow2Witness

open scoped Classical

namespace Erdos634.Draft.FluxDRow2S1Witness

open Erdos634.Geometry Erdos634.Draft.FluxGridWitness Erdos634.Draft.FluxRow2Witness

theorem M'_opp (k : Fin 3) : M'.oppLen k = M44.oppLen k := by
  unfold Tri.oppLen; rw [M'_pts]

/-- The model of `D2` is scalene: `(24, 32, 16)`. -/
theorem D2_scalene : ∀ k k', k ≠ k' → D2.model.oppLen k ≠ D2.model.oppLen k' := by
  have h0 : D2.model.oppLen 0 = 24 := by rw [show D2.model = M' from rfl, M'_opp]; exact m_opp.1
  have h1 : D2.model.oppLen 1 = 32 := by rw [show D2.model = M' from rfl, M'_opp]; exact m_opp.2.1
  have h2 : D2.model.oppLen 2 = 16 := by rw [show D2.model = M' from rfl, M'_opp]; exact m_opp.2.2
  intro k k' hkk'
  fin_cases k <;> fin_cases k' <;> simp_all <;> norm_num

/-- **Equation (1) on the real `D2`**: its side matrix satisfies `D v = 2 v`, rows nonzero. -/
theorem D2_side_matrix : (∀ i, ∑ j, (D2.sideCount i j : ℝ) * D2.model.oppLen j = 2 * D2.model.oppLen i)
    ∧ (∀ i, ∃ j, 0 < D2.sideCount i j) :=
  ⟨Row2.sideCount_eigen D2 2 (fun k => (D2_sim k).2) D2_scalene, Row2.sideCount_rows D2 D2_scalene⟩

/-- `N = 4` is a square, so `lemmaD_tiling`'s `¬ IsSquare N` fails on `D2` (stated, not hidden). -/
theorem D2_square : IsSquare (2 * 2 : ℕ) := ⟨2, rfl⟩

end Erdos634.Draft.FluxDRow2S1Witness

#print axioms Erdos634.Draft.FluxDRow2S1Witness.D2_scalene
#print axioms Erdos634.Draft.FluxDRow2S1Witness.D2_side_matrix
#print axioms Erdos634.Draft.FluxDRow2S1Witness.D2_square

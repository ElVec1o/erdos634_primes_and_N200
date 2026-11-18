-- Draft/ThetaNotch3Fin.lean -- STAGE 2/3 wrap-up: witnesses for the hypotheses of `thetaTiled_general_rho0`, controls for `thetaTiled_general`.
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
* `thetaTiled_general_rho0` is applied at `(e,f) = (1,2), (1,3), (1,6)` (the hypotheses are satisfiable: `by decide`); these are three of the rows `(1,f)`;
  `rho0f 1 f = 0` for EVERY `f >= 2` (ThetaNotch4E1.rho0f_one).  For coprime `2 <= e < f`, `rho0f e f != 0` is PROVED in ThetaNotch4Rho (`rho0f_ne_zero`).
  Superseded 2026-11-14: for e = 1 by `ThetaNotch4E1.rho0f_one` / `thetaTiled_general_rho0_e1`, for coprime e >= 2 by `ThetaNotch4Rho.rho0f_ne_zero`; the closed statement is `ThetaNotch4Rho.thetaTiled_all`.
* `thetaTiled_general` is applied at the rows `(2,3), (3,4), (4,5), (5,6), (3,8), (3,5), (2,5), (5,7), (7,10)`; the `t0f` values match
  `internal notes` 2.2 (`t0f_table`).
* controls: at `(2,3)`, `t0f = 7` and `ThetaUnitUp.not_thetaTiled_2_3_t4` (no tiling at `t = 4`) is consistent; `t = 6` at `(2,3)` is NOT claimed.
CREDIT: Paliy, Beeson, Laczkovich, Zhang, Beeson-Rosu; the project.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotch3Rho0

open scoped Classical
open Erdos634.Geometry

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.ThetaUnit (ThetaTiled)
open Erdos634.Draft.TileCountFamilies (TileCount)

theorem thetaTiled_1_2_rho0 : ∀ t, t0f 1 2 ≤ t → ThetaTiled 1 2 (2 * 2 - 1 * 1) t :=
  thetaTiled_general_rho0 1 2 (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem thetaTiled_1_3_rho0 : ∀ t, t0f 1 3 ≤ t → ThetaTiled 1 3 (3 * 3 - 1 * 1) t :=
  thetaTiled_general_rho0 1 3 (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem thetaTiled_1_6_rho0 : ∀ t, t0f 1 6 ≤ t → ThetaTiled 1 6 (6 * 6 - 1 * 1) t :=
  thetaTiled_general_rho0 1 6 (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem thetaTiled_3_4_general : ∀ t, 14 ≤ t → ThetaTiled 3 4 7 t := by
  have := thetaTiled_general 3 4 (by norm_num) (by norm_num) (by decide)
  intro t ht; exact this t (by have := t0f_table.2.2.1; omega)
theorem thetaTiled_4_5_general : ∀ t, 18 ≤ t → ThetaTiled 4 5 9 t := by
  have := thetaTiled_general 4 5 (by norm_num) (by norm_num) (by decide)
  intro t ht; exact this t (by have := t0f_table.2.2.2.1; omega)
theorem thetaTiled_5_6_general : ∀ t, 28 ≤ t → ThetaTiled 5 6 11 t := by
  have := thetaTiled_general 5 6 (by norm_num) (by norm_num) (by decide)
  intro t ht; exact this t (by have := t0f_table.2.2.2.2.1; omega)
theorem thetaTiled_3_8_general : ∀ t, 11 ≤ t → ThetaTiled 3 8 55 t := by
  have := thetaTiled_general 3 8 (by norm_num) (by norm_num) (by decide)
  intro t ht; exact this t (by have := t0f_table.2.2.2.2.2.1; omega)

theorem tileCount_6655_general : TileCount 6655 := by
  obtain ⟨D, -, -⟩ := thetaTiled_3_8_general 11 le_rfl; exact ⟨D⟩

/-- control: the formula value at the boundary row `(2,3)` is `7`, strictly above the exact NO at `t = 4` -/
theorem t0_2_3_gt_no : t0f 2 3 = 7 ∧ ¬ ThetaTiled 2 3 5 4 := ⟨by decide, Erdos634.Draft.ThetaUnit.not_thetaTiled_2_3_t4⟩

end

end Erdos634.Draft.ThetaNotch

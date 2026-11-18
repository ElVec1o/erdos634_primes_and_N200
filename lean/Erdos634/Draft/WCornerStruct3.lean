/-
Draft/WCornerStruct3.lean -- written 16 November 2026 (work item LEAN_CORNERSTRUCT_2026-11-16).  UNAUDITED beyond internal checks.  Not imported by any aggregate.  New leaf module (imports `WCornerStruct1`).
Audit gap G1 (`internal audit`, O1): `w_corner_run_long` is stated for `e = 1` as well (`sigma_B_joint_P` never uses `2 <= e`).  There is NO e = 1 W witness file in `data/witnesses`
(37 W files, all `e >= 2`); the Lean tilings of `W_M(1,f)` for `M >= f` come from `CollarG.wTilable_lin` (kernel proofs).  Controls: the theorem applied at the Lean tilings `WTilable 1 4 4` and `WTilable 1 5 6`.
This is a consistency check of the STATEMENT (hypotheses satisfiable at e = 1), not an independent data test of the e = 1 prediction.
-/
import Erdos634.Draft.WCornerStruct1

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WCornerStruct

open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.Draft.CollarG

theorem ctl_e1_1_4_4 : ∃ (N : ℕ) (D₀ : CongruentDissection N) (x y z : ℕ), WLongRunWord D₀ 4 1 4 x y z ∧ 4 ≤ z := by
  obtain ⟨D₀, hT, hMod⟩ : WTilable 1 4 4 := by
    have := wTilable_lin 1 4 (by norm_num) (by norm_num) 1 (by norm_num) 0; simpa using this
  obtain ⟨x, y, z, hw, hnat, hz⟩ := w_corner_run_long (e := 1) (f := 4) (M := 4) (by decide) (by omega) (by omega) (by omega) D₀ hT hMod
  exact ⟨_, D₀, x, y, z, hw, hz⟩

theorem ctl_e1_1_5_6 : ∃ (N : ℕ) (D₀ : CongruentDissection N) (x y z : ℕ), WLongRunWord D₀ 6 1 5 x y z ∧ 5 ≤ z := by
  obtain ⟨D₀, hT, hMod⟩ : WTilable 1 5 6 := by
    have := wTilable_lin 1 5 (by norm_num) (by norm_num) 1 (by norm_num) 1; simpa using this
  obtain ⟨x, y, z, hw, hnat, hz⟩ := w_corner_run_long (e := 1) (f := 5) (M := 6) (by decide) (by omega) (by omega) (by omega) D₀ hT hMod
  exact ⟨_, D₀, x, y, z, hw, hz⟩

#print axioms ctl_e1_1_4_4
#print axioms ctl_e1_1_5_6

end Erdos634.Draft.WCornerStruct

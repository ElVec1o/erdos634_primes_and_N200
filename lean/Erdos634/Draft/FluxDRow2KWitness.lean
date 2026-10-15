-- Draft/FluxDRow2KWitness.lean: non-vacuity witness for `Row2.lemmaK` / `Row2.lemmaK_cos`
-- (Draft/FluxDRow2K.lean).  Imported by `All`.
--
-- Every hypothesis is met by the `(1, 2, √7)` survivor of the Lemma D witness (`N = 7`,
-- `D = [[0,0,1],[0,0,2],[1,3,0]]`, `μ = √7`): the conclusion holds with `a/c = 1/√7 = (1/7)·√7`,
-- `b/c = (2/7)·√7`, not both rational.  This is an algebraic model, not a tiling.
-- The geometric hypotheses of `Row2.lemmaK_tiling` are met by `FluxRow2Witness.D2` except
-- `¬ IsSquare N` (`N = 4`), as in Draft/FluxDRow2S1Witness.lean.
import Erdos634.Draft.FluxDRow2K
import Erdos634.Draft.FluxDRow2DWitness

open scoped Classical

namespace Erdos634.Draft.FluxDRow2KWitness

open Erdos634.Geometry Erdos634.Draft.FluxDRow2DWitness

/-- **Lemma K on the `(1, 2, √7)` survivor.** -/
theorem lemmaK_P2 : Row2.QMu √(7 : ℝ) (vm 0 / vm 2) ∧ Row2.QMu √(7 : ℝ) (vm 1 / vm 2) ∧
    ¬ ((∃ r : ℚ, vm 0 = r * vm 2) ∧ (∃ r : ℚ, vm 1 = r * vm 2)) :=
  Row2.lemmaK Dm vm vm_pos sqrt7_irr sqrt7_sq Dm_eigen

/-- **Lemma K's cosines on the survivor** (the triangle `(1, 2, √7)`, angle `2π/3` at `c`). -/
theorem lemmaK_cos_P2 :
    Row2.QMu √(7 : ℝ) ((vm 1 ^ 2 + vm 2 ^ 2 - vm 0 ^ 2) / (2 * vm 1 * vm 2)) ∧
    Row2.QMu √(7 : ℝ) ((vm 2 ^ 2 + vm 0 ^ 2 - vm 1 ^ 2) / (2 * vm 2 * vm 0)) ∧
    Row2.QMu √(7 : ℝ) ((vm 0 ^ 2 + vm 1 ^ 2 - vm 2 ^ 2) / (2 * vm 0 * vm 1)) :=
  Row2.lemmaK_cos Dm vm vm_pos sqrt7_irr sqrt7_sq Dm_eigen

/-- The explicit value: `a/c = 1/√7 = (1/7)·√7`. -/
theorem ratio_value : vm 0 / vm 2 = (0 : ℚ) + ((1 / 7 : ℚ) : ℝ) * √(7 : ℝ) := by
  have h7 : √(7 : ℝ) * √(7 : ℝ) = 7 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 < √(7 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  simp only [vm, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  push_cast
  field_simp
  linarith

end Erdos634.Draft.FluxDRow2KWitness

#print axioms Erdos634.Draft.FluxDRow2KWitness.lemmaK_P2
#print axioms Erdos634.Draft.FluxDRow2KWitness.lemmaK_cos_P2
#print axioms Erdos634.Draft.FluxDRow2KWitness.ratio_value

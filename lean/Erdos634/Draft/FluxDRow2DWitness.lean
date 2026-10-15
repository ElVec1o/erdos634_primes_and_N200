-- Draft/FluxDRow2DWitness.lean: non-vacuity witness for `Row2.lemmaD` / `Row2.lemmaD_scale`
-- (Draft/FluxDRow2D.lean).  Imported by `All`.
--
-- Every hypothesis is met by the survivor shape: the side matrix `D = [[0,0,1],[0,0,2],[1,3,0]]` of
-- the tile `(a, b, c) = (1, 2, √7)`, `μ = √7` (`N = 7`), with (A) and (B) both through their first
-- disjuncts.  This is an algebraic model (Lemma D is pure linear algebra), not a tiling: the angle
-- condition `γ = 2π/3 > π/2` excludes it.
import Erdos634.Draft.FluxDRow2D

open scoped Classical

namespace Erdos634.Draft.FluxDRow2DWitness

open Erdos634.Geometry

unseal Nat.sqrt.iter in
theorem irr7 : Irrational √(7 : ℝ) := by decide

/-- The survivor's side matrix. -/
def Dm : Fin 3 → Fin 3 → ℕ := ![![0, 0, 1], ![0, 0, 2], ![1, 3, 0]]

/-- The tile `(1, 2, √7)`. -/
noncomputable def vm : Fin 3 → ℝ := ![1, 2, √(7 : ℝ)]

theorem vm_pos : ∀ i, 0 < vm i := by
  intro i
  fin_cases i <;> simp [vm]

theorem sqrt7_irr : ¬ ∃ r : ℚ, √(7 : ℝ) = r := by
  rintro ⟨r, hr⟩
  exact irr7 ⟨r, hr.symm⟩

theorem sqrt7_sq : √(7 : ℝ) ^ 2 = ((7 : ℤ) : ℝ) := by
  rw [Real.sq_sqrt (by norm_num)]; norm_num

theorem Dm_eigen : ∀ i, ∑ j, (Dm i j : ℝ) * vm j = √(7 : ℝ) * vm i := by
  have h7 : √(7 : ℝ) * √(7 : ℝ) = 7 := Real.mul_self_sqrt (by norm_num)
  intro i
  fin_cases i <;> simp [Dm, vm, Fin.sum_univ_three] <;> linarith

theorem Dm_rows : ∀ i, ∃ j, 0 < Dm i j := by
  intro i
  fin_cases i
  · exact ⟨2, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨0, by decide⟩

/-- **Lemma D applied to the `(1, 2, √7)` survivor**: all hypotheses hold, and the conclusion is the
survivor shape `[[0,0,1],[0,0,2],[1,3,0]]`. -/
theorem lemmaD_P2 :
    Dm 0 0 = 0 ∧ Dm 0 1 = 0 ∧ Dm 1 0 = 0 ∧ Dm 1 1 = 0 ∧ Dm 2 2 = 0 ∧
      0 < Dm 0 2 ∧ 0 < Dm 1 2 ∧ 0 < Dm 2 0 ∧ 0 < Dm 2 1 :=
  Row2.lemmaD Dm vm vm_pos sqrt7_irr sqrt7_sq Dm_eigen Dm_rows
    (Or.inl ⟨by decide, by decide⟩) (Or.inl ⟨by decide, by decide⟩)

/-- **`Row2.lemmaD_scale` on the survivor**: `√7·1 = 1·√7`, `√7·2 = 2·√7`, `√7·√7 = 1·1 + 3·2`. -/
theorem lemmaD_scale_P2 :
    √(7 : ℝ) * vm 0 = Dm 0 2 * vm 2 ∧ √(7 : ℝ) * vm 1 = Dm 1 2 * vm 2 ∧
      √(7 : ℝ) * vm 2 = Dm 2 0 * vm 0 + Dm 2 1 * vm 1 :=
  Row2.lemmaD_scale Dm vm vm_pos sqrt7_irr sqrt7_sq Dm_eigen Dm_rows
    (Or.inl ⟨by decide, by decide⟩) (Or.inl ⟨by decide, by decide⟩)

end Erdos634.Draft.FluxDRow2DWitness

#print axioms Erdos634.Draft.FluxDRow2DWitness.lemmaD_P2
#print axioms Erdos634.Draft.FluxDRow2DWitness.lemmaD_scale_P2

/-
Satisfiability checks for the corner-fact files of Case D.
  * `cornerB_witness`, `cornerA_witness`: the corner facts hold, hypothesis `RightNormal` and all, on the REAL
    `CongruentDissection 2` `dissection'` (tile α456 = (4,5,6)-type right tile, N = 2) of `H1Witnesses`
    (a real tiling: so the hypotheses of `cornerB_fact`/`cornerA_fact` are satisfied and their conclusions are
    instantiated, not vacuous).
  * `caseD_core_needs_cornerA`: in `caseD_core` every hypothesis EXCEPT the corner-A input `P ≠ 0 ∨ R ≠ 0` is
    satisfiable (explicit reals): so the corner-A fact (H1eCLFacts.cornerA_fact) is exactly what closes D9; it is not
    redundant.
  No sorry.
-/
import Erdos634.Draft.H1eCLCaseD
import Erdos634.Draft.H1Witnesses

namespace Erdos634.Draft.H1eCL

open Erdos634.Draft.H1Witnesses Erdos634.Draft.FluxGRow3AngleWitnessDissection

theorem cornerB_witness : True := by
  have _ := cornerB_fact rightNormal_witness
  trivial

theorem cornerA_witness : True := by
  have _ := cornerA_fact rightNormal_witness
  trivial

/-- Control: drop `cornerA` and the remaining hypotheses of `caseD_core` are consistent
(`lam = √2`, `c = 2√2`, `a = √3`, `Q = 4`, `R₂ = 1`, `P = R = P₂ = Q₂ = 0`, `c' = -1`). -/
theorem caseD_core_needs_cornerA :
    ∃ (a c lam a' c' : ℝ) (M : ℕ) (P Q R P₂ Q₂ R₂ : ℕ),
      0 < lam ∧ lam ^ 2 = M ∧ Irrational a ∧
      (P : ℝ) * a + (Q : ℝ) * 1 + (R : ℝ) * c = lam * c ∧
      (P ≠ 0 → 0 < a' * (-lam * c')) ∧ (Q ≠ 0 → 0 < 1 * (-lam * c')) ∧ (R ≠ 0 → 0 < c' * (-lam * c')) ∧
      (P₂ : ℝ) * a + (Q₂ : ℝ) * 1 + (R₂ : ℝ) * c = 2 * lam ∧
      (P₂ ≠ 0 → 0 < a' * (-(2 * lam))) ∧ (Q₂ ≠ 0 → 0 < 1 * (-(2 * lam))) ∧
      (R₂ ≠ 0 → 0 < c' * (-(2 * lam))) ∧
      ((Q ≠ 0 ∧ R₂ ≠ 0) ∨ (R ≠ 0 ∧ Q₂ ≠ 0)) ∧ ¬ (P ≠ 0 ∨ R ≠ 0) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := by positivity
  refine ⟨Real.sqrt 3, 2 * Real.sqrt 2, Real.sqrt 2, 0, -1, 2, 0, 4, 0, 0, 0, 1,
    hpos, by rw [h2]; norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact irrational_sqrt_natCast_iff.mpr (by
    rintro ⟨m, hm⟩
    have : m < 2 := by nlinarith
    interval_cases m <;> simp at hm)
  · push_cast; linear_combination (-2 : ℝ) * h2
  · exact fun h => (h rfl).elim
  · exact fun _ => by nlinarith [hpos]
  · exact fun h => (h rfl).elim
  · push_cast; ring
  · exact fun h => (h rfl).elim
  · exact fun h => (h rfl).elim
  · exact fun _ => by nlinarith [hpos]
  · exact Or.inl ⟨by decide, by decide⟩
  · simp

end Erdos634.Draft.H1eCL

#print axioms Erdos634.Draft.H1eCL.cornerB_witness
#print axioms Erdos634.Draft.H1eCL.cornerA_witness

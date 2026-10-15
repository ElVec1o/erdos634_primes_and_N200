-- Draft/N3EqCase.lean — For N=3, no CongruentDissection 3 can have TwoPiThreeData tile
-- with IrrPi α and an equilateral target.  This closes the N=3 equilateral branch of the reduction
-- to isosceles non-equilateral targets.  0 sorry, standard axioms.
import Erdos634.Draft.FluxCRow5Complete
import Erdos634.Draft.ISUMain

open scoped Classical

namespace Erdos634.Draft.N3EqCase

open Erdos634.Geometry Erdos634.Draft.ISUMain

/-- **N=3 equilateral case.**  A TwoPiThreeData tile with IrrPi α cannot tile an equilateral
triangle with N=3 pieces.  The closed forms force a=b (tile is isosceles), which gives α=π/6, a
rational multiple of π, contradicting IrrPi. -/
theorem no_three_equilateral_twoPiThree (D : CongruentDissection 3)
    {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) : False := by
  have hNp : (3 : ℕ).Prime := by decide
  -- Get closed forms for N=3
  obtain ⟨hc2, hD, hab2⟩ := Row5.twoPiThree_closedForms D hα h hP hNp
  -- For N=3: (N:ℝ)-3 = 0 and 3-(N:ℝ) = 0, so both branches of hD give 6*(a-b)=0
  have hab : a = b := by
    have hN3 : (3 : ℕ) = (3 : ℕ) := rfl
    push_cast at hD
    rcases hD with hD | hD <;> linarith
  -- Obtain the permutation from TwoPiThreeData
  obtain ⟨σ, hA, hoA, hB, hoB, hC, hoC⟩ := h
  -- σ 0 ≠ σ 1 since σ is injective and 0 ≠ 1
  have hσ01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  -- oppLen(σ 0) = a = b = oppLen(σ 1)
  have hopeq : D.model.oppLen (σ 0) = D.model.oppLen (σ 1) := by
    rw [hoA, hoB, hab]
  -- By law of sines: equal oppLens → equal angles
  have hangle_eq : D.model.angleAt (σ 0) = D.model.angleAt (σ 1) :=
    angleAt_eq_of_oppLen_eq D.model (σ 0) (σ 1) hσ01 hopeq
  -- So α = π/3 - α, giving α = π/6
  rw [hA, hB] at hangle_eq
  -- α = π/3 - α → α = π/6 → contradicts IrrPi
  have hα6 : α = Real.pi / 6 := by linarith
  exact hα ⟨1 / 6, by rw [hα6]; push_cast; ring⟩

end Erdos634.Draft.N3EqCase

#print axioms Erdos634.Draft.N3EqCase.no_three_equilateral_twoPiThree

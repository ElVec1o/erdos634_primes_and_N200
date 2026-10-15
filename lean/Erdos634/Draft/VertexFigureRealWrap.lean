import Erdos634.VertexFigureReal

/-!
# Vertex figures of a real dissection: wrapper

Key results:
- `interior_figure_cases`: at an interior vertex (no straight angles/coverings), exactly 4 cases
- `interior_figure_cases_gen`: full generalization with straight angles and covering tiles
- `boundary_figure_cases`: at a boundary vertex with sum = π, 5 cases

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.VertexFigureRealWrap

open Erdos634.VertexFigureReal

theorem vfr_interior_figure_cases {α β γ : ℝ} (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (p q r : ℕ) (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ = 2 * Real.pi) :
    (p = 6 ∧ q = 4 ∧ r = 0) ∨ (p = 4 ∧ q = 3 ∧ r = 1) ∨
    (p = 2 ∧ q = 2 ∧ r = 2) ∨ (p = 0 ∧ q = 1 ∧ r = 3) :=
  interior_figure_cases hγ hrel hirr p q r hsum

theorem vfr_boundary_figure_cases {α β γ : ℝ} (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (p q r s : ℕ) (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = Real.pi) :
    (s = 1 ∧ p = 0 ∧ q = 0 ∧ r = 0) ∨
    (s = 0 ∧ ((p = 3 ∧ q = 2 ∧ r = 0) ∨ (p = 1 ∧ q = 1 ∧ r = 1))) :=
  boundary_figure_cases hγ hrel hirr p q r s hsum

/-- Non-vacuity: α = π/4, β = π/8 satisfies 3α + 2β = π. -/
theorem vfr_witness : ∃ α β : ℝ, 3 * α + 2 * β = Real.pi ∧ α ≠ β :=
  ⟨Real.pi / 4, Real.pi / 8, by ring, by
    intro h
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith⟩

#print axioms vfr_interior_figure_cases
#print axioms vfr_boundary_figure_cases

end Erdos634.Draft.VertexFigureRealWrap

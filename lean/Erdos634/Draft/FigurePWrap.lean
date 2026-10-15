import Erdos634.ApexRigidity

/-!
# Angle-sum kernels for the vertex figures at P and P': arithmetic wrapper

`ApexRigidity.lean` has the angle-sum arithmetic for both:

* `figure_at_P`: γ + π + β + α = 2π — the figure at P.
* `figure_at_Pprime`: 3γ + β = 2π — the figure at P' is {β,3γ}.
* `Pprime_residuals`: the two residuals at P' are β and γ respectively.

All are linarith/ring over ℝ from the single relation 3α + 2β = π, γ = 2α + β.
The geometric claim that these are the actual vertex figures at P and P' in a
real dissection requires the placement layer.

No sorry, standard axioms.
-/

namespace Erdos634.Draft.FigurePWrap

/-- cor:figureP: the figure at P is γ + π + β + α = 2π. -/
theorem figure_P_sum {al be ga : ℝ}
    (hsum : 3 * al + 2 * be = Real.pi) (hga : ga = 2 * al + be) :
    ga + Real.pi + be + al = 2 * Real.pi :=
  Erdos634.ApexRigidity.figure_at_P hsum hga

/-- prop:figurePprime: {β,3γ} is a legal figure at P': 3γ + β = 2π. -/
theorem figure_Pprime_sum {al be ga : ℝ}
    (hsum : 3 * al + 2 * be = Real.pi) (hga : ga = 2 * al + be) :
    3 * ga + be = 2 * Real.pi :=
  Erdos634.ApexRigidity.figure_at_Pprime hsum hga

/-- The two residuals at P': 2π − 3γ = β and 2π − (2γ+β) = γ. -/
theorem figure_Pprime_residuals {al be ga : ℝ}
    (hsum : 3 * al + 2 * be = Real.pi) (hga : ga = 2 * al + be) :
    2 * Real.pi - 3 * ga = be ∧ 2 * Real.pi - (2 * ga + be) = ga :=
  Erdos634.ApexRigidity.Pprime_residuals hsum hga

/-- Non-vacuity: the angle hypotheses are satisfiable (use the (1,2) member angles). -/
theorem figure_witness : ∃ (al be ga : ℝ),
    3 * al + 2 * be = Real.pi ∧ ga = 2 * al + be :=
  ⟨Real.pi / 7, Real.pi * (2 / 7), Real.pi * (4 / 7), by ring, by ring⟩

#print axioms figure_P_sum
#print axioms figure_Pprime_sum
#print axioms figure_Pprime_residuals

end Erdos634.Draft.FigurePWrap

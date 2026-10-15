import Erdos634.A36Reduction

/-!
# Row reduction for `3α+2β`: wrapper

Re-exports, under `a36_` names, the results of `A36Reduction`:
- `a36_uniform_of_layer_rigid`: layer rigidity forces uniformity
- `a36_figure_below_cases`: the figure below is `(3,2,0)` or `(1,1,1)`
- `a36_gamma_bound_below`: `ng ≤ 1` in the figure below
- `a36_below_fan_is_pi`: the angle below is `π` when the angle above is `π`

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.A36ReductionWrap

open Erdos634.A36Reduction

theorem a36_uniform_of_layer_rigid {α : Type*} (angleAt : ℕ → α) (orient : ℕ → Prop)
    (h_rigid : ∀ j, orient j)
    (h_det : ∀ j k, orient j → orient k → angleAt j = angleAt k) :
    ∀ j k, angleAt j = angleAt k :=
  uniform_of_layer_rigid angleAt orient h_rigid h_det

theorem a36_figure_below_cases (na nb ng : ℕ) (h1 : na + 2 * ng = 3) (h2 : nb + ng = 2) :
    (na = 3 ∧ nb = 2 ∧ ng = 0) ∨ (na = 1 ∧ nb = 1 ∧ ng = 1) :=
  figure_below_cases na nb ng h1 h2

theorem a36_gamma_bound_below (na nb ng : ℕ) (h1 : na + 2 * ng = 3) (h2 : nb + ng = 2) :
    ng ≤ 1 :=
  gamma_bound_below na nb ng h1 h2

theorem a36_below_fan_is_pi (above below : ℝ)
    (htotal : above + below = 2 * Real.pi) (habove : above = Real.pi) :
    below = Real.pi :=
  below_fan_is_pi above below htotal habove

-- Non-vacuity: figure_below_cases with na=3, nb=2, ng=0
example : (3:ℕ) = 3 ∧ 2 = 2 ∧ 0 = 0 :=
  (a36_figure_below_cases 3 2 0 (by omega) (by omega)).resolve_right (by omega)

#print axioms a36_figure_below_cases
#print axioms a36_below_fan_is_pi

end Erdos634.Draft.A36ReductionWrap

import Erdos634.ApexRigidity

/-!
# Apex geometry and rigidity arithmetic: wrapper

Re-exports, under `ar_` names, results of `ApexRigidity`:
- `two_gamma`: 2γ = π + α (from 3α+2β=π, γ=2α+β)
- `figure_at_P`: vertex figure at P: γ + π + β + α = 2π
- `figure_at_Pprime`: figure at P': 3γ + β = 2π
- `Pprime_residuals`: residuals at P' (2π−3γ=β and 2π−(2γ+β)=γ)
- `V_interior`: V is interior to U's edge
- `b_gt_f`, `eb_gt_a`: side ordering for base-beta tiles
- `shortest_side`: a is shortest when e²+ef<f²

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.ApexRigidityWrap

open Erdos634.ApexRigidity

theorem ar_two_gamma (α β γ : ℝ) (hsum : 3 * α + 2 * β = Real.pi) (hγ : γ = 2 * α + β) :
    2 * γ = Real.pi + α :=
  two_gamma α β γ hsum hγ

theorem ar_figure_at_P {al be ga : ℝ} (hsum : 3 * al + 2 * be = Real.pi)
    (hga : ga = 2 * al + be) :
    ga + Real.pi + be + al = 2 * Real.pi :=
  figure_at_P hsum hga

theorem ar_figure_at_Pprime {al be ga : ℝ} (hsum : 3 * al + 2 * be = Real.pi)
    (hga : ga = 2 * al + be) :
    3 * ga + be = 2 * Real.pi :=
  figure_at_Pprime hsum hga

theorem ar_Pprime_residuals {al be ga : ℝ} (hsum : 3 * al + 2 * be = Real.pi)
    (hga : ga = 2 * al + be) :
    2 * Real.pi - 3 * ga = be ∧ 2 * Real.pi - (2 * ga + be) = ga :=
  Pprime_residuals hsum hga

theorem ar_V_interior {e f : ℝ} (he : 0 < e) (hef : e < f) (hgold : e ^ 2 + e * f < f ^ 2) :
    f ^ 2 - (f ^ 2 - e ^ 2) < f ^ 2 - e ^ 2 :=
  V_interior he hef hgold

theorem ar_b_gt_f {e f : ℕ} (hef : e < f) (hf : 2 ≤ f) : f + e ^ 2 < f ^ 2 :=
  b_gt_f hef hf

theorem ar_eb_gt_a {e f : ℕ} (he : 1 ≤ e) (hef : e < f) (hf : 2 ≤ f) :
    e * f < e * (f ^ 2 - e ^ 2) :=
  eb_gt_a he hef hf

theorem ar_shortest_side {e f : ℕ} (h : e ^ 2 + e * f < f ^ 2) :
    e * f < f ^ 2 - e ^ 2 ∧ e * f < f ^ 2 :=
  shortest_side h

-- Non-vacuity
example : (1 : ℕ) * 2 < 1 * (2 ^ 2 - 1 ^ 2) := ar_eb_gt_a (by omega) (by omega) (by omega)

#print axioms ar_two_gamma
#print axioms ar_b_gt_f

end Erdos634.Draft.ApexRigidityWrap

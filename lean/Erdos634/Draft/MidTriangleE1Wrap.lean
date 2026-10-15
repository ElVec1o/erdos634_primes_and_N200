import Erdos634.MidTriangleE1
namespace Erdos634.Draft.MidTriangleE1Wrap
open Erdos634.MidTriangleE1
variable (α β γ : ℝ)

theorem wrap_base_single_b {f u v w : ℕ} (hf : 2 ≤ f)
    (h : u * f + v * (f ^ 2 - 1) + w * f ^ 2 = f ^ 2 - 1) :
    u = 0 ∧ v = 1 ∧ w = 0 :=
  base_single_b hf h

theorem wrap_no_gamma_at_base_corner (hγ : γ = 2 * α + β) (hα : 0 < α)
    (θ : ℝ) (hθ : θ = γ) (hfit : θ ≤ α + β) : False :=
  no_gamma_at_base_corner α β γ hγ hα θ hθ hfit

theorem wrap_midTriangle_untileable (hα : 0 < α) (hγ : γ = 2 * α + β)
    (θD θD' : ℝ)
    (hends : (θD = α ∧ θD' = γ) ∨ (θD = γ ∧ θD' = α))
    (hfitD : θD ≤ α + β) (hfitD' : θD' ≤ α + β) : False :=
  midTriangle_untileable α β γ hα hγ θD θD' hends hfitD hfitD'

example : True := trivial
#print axioms wrap_midTriangle_untileable
end Erdos634.Draft.MidTriangleE1Wrap

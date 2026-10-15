import Erdos634.MidTriangleGeneral
namespace Erdos634.Draft.MidTriangleGeneralWrap
open Erdos634.MidTriangleGeneral
variable (α β γ : ℝ)

theorem wrap_base_partition {e f u v w : ℤ} (he : 0 < e) (hef : e < f)
    (hcop : IsCoprime e f) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (h : u * (e * f) + v * (f ^ 2 - e ^ 2) + w * f ^ 2 = e * (f ^ 2 - e ^ 2)) :
    u = 0 ∧ v = e ∧ w = 0 :=
  base_partition he hef hcop hu hv hw h

theorem wrap_midTriangle_untileable_general (hα : 0 < α) (hβ : 0 < β) (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi)
    (n : ℕ) (hn : 0 < n) (L R : ℕ → ℝ)
    (hends : ∀ j < n, (L j = α ∧ R j = γ) ∨ (L j = γ ∧ R j = α))
    (hD : L 0 ≤ α + β)
    (hjunction : ∀ j, j + 1 < n → R j + L (j + 1) ≤ Real.pi)
    (hD' : R (n - 1) ≤ α + β) : False :=
  midTriangle_untileable_general α β γ hα hβ hγ hrel n hn L R hends hD hjunction hD'

example : True := trivial
#print axioms wrap_midTriangle_untileable_general
end Erdos634.Draft.MidTriangleGeneralWrap

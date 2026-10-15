import Erdos634.MidTriangleComposed
namespace Erdos634.Draft.MidTriangleComposedWrap
open Erdos634.MidTriangleGeneral Erdos634.RunForcing

theorem wrap_midTriangle_untileable_composed
    (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi)
    (e f m : ℤ) (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f)
    (hm : 0 < m) (hscale : m * e < f)
    (u v w : ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hpart : u * (e * f) + v * (f ^ 2 - e ^ 2) + w * f ^ 2 = (m * e) * (f ^ 2 - e ^ 2))
    (L R : ℕ → ℝ)
    (hends : ∀ j < v.toNat, (L j = α ∧ R j = γ) ∨ (L j = γ ∧ R j = α))
    (hD : L 0 ≤ α + β)
    (hjunction : ∀ j, j + 1 < v.toNat → R j + L (j + 1) ≤ Real.pi)
    (hD' : R (v.toNat - 1) ≤ α + β) : False :=
  Erdos634.MidTriangleComposed.midTriangle_untileable_composed
    α β γ hα hβ hγ hrel e f m he hef hcop hm hscale
    u v w hu hv hw hpart L R hends hD hjunction hD'

theorem wrap_prime_case_covered {e f : ℤ} (hef : e < f) : 1 * e < f :=
  Erdos634.MidTriangleComposed.prime_case_covered hef

example : True := trivial
#print axioms wrap_midTriangle_untileable_composed
#print axioms wrap_prime_case_covered
end Erdos634.Draft.MidTriangleComposedWrap

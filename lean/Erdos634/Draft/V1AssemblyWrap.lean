import Erdos634.V1Assembly

namespace Erdos634.Draft.V1AssemblyWrap
open Erdos634.V1Assembly

theorem wrap_chord_tip_on_ray_iff (k : ℕ) (c a t u₁ u₂ : ℝ) (hc : c ≠ 0) (hu : u₂ ≠ 0)
    (h1 : ((k : ℝ) - 1) * c + 2 * a * u₁ = t * u₁)
    (h2 : 2 * a * u₂ = t * u₂) : (k : ℝ) = 1 :=
  chord_tip_on_ray_iff k c a t u₁ u₂ hc hu h1 h2

example : True := trivial
#print axioms wrap_chord_tip_on_ray_iff

end Erdos634.Draft.V1AssemblyWrap

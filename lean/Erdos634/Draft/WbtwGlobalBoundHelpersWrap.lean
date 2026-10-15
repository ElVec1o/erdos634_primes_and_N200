import Erdos634.WbtwGlobalBoundHelpers

namespace Erdos634.Draft.WbtwGlobalBoundHelpersWrap
open Erdos634.ChordTraceReal Erdos634.Geometry

theorem wrap_wbtw_far_endpoint_to_Q {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {P Q : Plane}
    (hPQ : D.target.carrier ∩ {x | f x = c} = segment ℝ P Q) (R S : Fin N → Plane)
    (k : Fin N) (hktrace : (D.tile k).carrier ∩ {x | f x = c} = segment ℝ (R k) (S k)) :
    Wbtw ℝ P (S k) Q :=
  wbtw_far_endpoint_to_Q D f c hPQ R S k hktrace

example : True := trivial
#check @wrap_wbtw_far_endpoint_to_Q

end Erdos634.Draft.WbtwGlobalBoundHelpersWrap

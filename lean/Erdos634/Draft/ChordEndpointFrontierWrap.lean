import Erdos634.ChordEndpointFrontier

namespace Erdos634.Draft.ChordEndpointFrontierWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_chord_endpoint_not_interior {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {p q : Plane} (hpq : p ≠ q)
    (hseg : D.target.carrier ∩ {x | f x = c} = segment ℝ p q) :
    p ∉ interior D.target.carrier :=
  chord_endpoint_not_interior D f c hpq hseg

example : True := trivial
#print axioms wrap_chord_endpoint_not_interior

end Erdos634.Draft.ChordEndpointFrontierWrap

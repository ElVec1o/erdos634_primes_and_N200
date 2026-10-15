import Erdos634.ChordEndpointFrontierGeneral

namespace Erdos634.Draft.ChordEndpointFrontierGeneralWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_chord_endpoint_not_interior' (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {T : Tri} {p q : Plane}
    (hpq : p ≠ q) (hseg : T.carrier ∩ {x | f x = c} = segment ℝ p q) :
    p ∉ interior T.carrier :=
  chord_endpoint_not_interior' f c hpq hseg

example : True := trivial
#print axioms wrap_chord_endpoint_not_interior'

end Erdos634.Draft.ChordEndpointFrontierGeneralWrap

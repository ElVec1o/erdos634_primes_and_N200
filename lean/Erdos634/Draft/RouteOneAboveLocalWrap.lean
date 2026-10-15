import Erdos634.RouteOneAboveLocal

namespace Erdos634.Draft.RouteOneAboveLocalWrap
open Erdos634.RouteOne

theorem wrap_witness_cover :
    lowerHalfDisc (Erdos634.CertCoord.mkPt 1 0) (1/2) ⊆ witnessTri.carrier :=
  witness_cover

example : True := trivial
#print axioms wrap_witness_cover

end Erdos634.Draft.RouteOneAboveLocalWrap

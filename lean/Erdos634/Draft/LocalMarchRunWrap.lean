import Erdos634.LocalMarchRun

namespace Erdos634.Draft.LocalMarchRunWrap
open Erdos634.Geometry
open Erdos634.LocalMarchRun

theorem wrap_no_perpetual_march {N : ℕ} {D : Dissection N} {w : Plane}
    (A : StepDatum D w) (hw : w ≠ 0) (hne : A.S.Nonempty) : False :=
  no_perpetual_march A hw hne

example : True := trivial
#print axioms wrap_no_perpetual_march

end Erdos634.Draft.LocalMarchRunWrap

import Erdos634.RouteOneVE

namespace Erdos634.Draft.RouteOneVEWrap
open Erdos634.Geometry
open Erdos634.RouteOne

theorem wrap_pi_count_eq_one {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ interior D.target.carrier) (b k : Fin N)
    (hb : (D.tile b).localAngle p = Real.pi)
    (hk : p ∈ (D.tile k).carrier) (hknot : (D.tile k).localAngle p ≠ Real.pi) :
    ({i | (D.tile i).localAngle p = Real.pi} : Finset (Fin N)).card = 1 :=
  pi_count_eq_one D hp b k hb hk hknot

example : True := trivial
#check @wrap_pi_count_eq_one

end Erdos634.Draft.RouteOneVEWrap

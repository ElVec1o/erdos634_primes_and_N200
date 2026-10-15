import Erdos634.TP_tao

namespace Erdos634.Draft.TP_taoWrap
open Erdos634.TPTao Erdos634.Geometry Set

variable {N : ℕ}

theorem wrap_exists_partner_dart_of_interior (D : Dissection N) (hN : 0 < N) (d : Dart D) {s : ℝ}
    (hs : s ∈ Ioo d.lo d.hi)
    (hint : edgeMap D d.tile d.side s ∈ interior D.target.carrier) :
    ∃ d' : Dart D, d'.tile ≠ d.tile ∧ d'.relInt = d.relInt :=
  exists_partner_dart_of_interior D hN d hs hint

example : True := trivial
#check @wrap_exists_partner_dart_of_interior

end Erdos634.Draft.TP_taoWrap

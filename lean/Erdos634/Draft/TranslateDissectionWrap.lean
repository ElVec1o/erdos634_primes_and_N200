import Erdos634.TranslateDissection

namespace Erdos634.Draft.TranslateDissectionWrap
open Erdos634.TranslateDissection Erdos634.Geometry Erdos634.DissectionMap

theorem wrap_translateCongruentDissection_tile {N : ℕ} (v : Plane) (D : CongruentDissection N)
    (i : Fin N) :
    (translateCongruentDissection v D).tile i = mapTri (transEquiv v).toAffineEquiv (D.tile i) :=
  translateCongruentDissection_tile v D i

example : True := trivial
#print axioms wrap_translateCongruentDissection_tile

end Erdos634.Draft.TranslateDissectionWrap

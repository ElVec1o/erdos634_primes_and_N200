import Erdos634.UnionDissection

namespace Erdos634.Draft.UnionDissectionWrap
open Erdos634.UnionDissection Erdos634.Geometry

theorem wrap_unionDissection_tile_right {M N : ℕ} (T : Tri) (D1 : Dissection M) (D2 : Dissection N)
    (hcov : D1.target.carrier ∪ D2.target.carrier = T.carrier)
    (hdisj : Disjoint (interior D1.target.carrier) (interior D2.target.carrier)) (i : Fin N) :
    (unionDissection T D1 D2 hcov hdisj).tile (Fin.natAdd M i) = D2.tile i :=
  unionDissection_tile_right T D1 D2 hcov hdisj i

example : True := trivial
#print axioms wrap_unionDissection_tile_right

end Erdos634.Draft.UnionDissectionWrap
